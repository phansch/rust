// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(non_camel_case_types)]

use rustc_data_structures::sync::{Lock, LockCell};

use std::cell::{RefCell, Cell};
use std::collections::HashMap;
use std::ffi::CString;
use std::fmt::Debug;
use std::hash::{Hash, BuildHasher};
use std::iter::repeat;
use std::path::Path;
use std::time::{Duration, Instant};
use std::cell::UnsafeCell;

use std::sync::mpsc::{Sender};
use syntax_pos::{SpanData};
use ty::maps::{QueryMsg};
use dep_graph::{DepNode};
use rayon_core::registry::Registry;

scoped_thread_local!(pub static THREAD_INDEX: usize);

#[repr(align(64))]
struct CacheAligned<T>(T);

// FIXME: Find a way to ensure this isn't transferred between multiple thread pools
// Thread pools should be the only thing that has a valid THREAD_INDEX.
// Make it contain a Arc<rayon::Registry> and get the index based on the current worker?
pub struct ThreadLocal<T>(Vec<CacheAligned<UnsafeCell<T>>>);

unsafe impl<T> Send for ThreadLocal<T> {}
unsafe impl<T> Sync for ThreadLocal<T> {}

impl<T> ThreadLocal<T> {
    pub fn new<F>(f: F) -> ThreadLocal<T>
        where F: Fn() -> T,
    {
        let n = Registry::current_num_threads();
        ThreadLocal((0..(1 + n)).map(|_| CacheAligned(UnsafeCell::new(f()))).collect())
    }

    pub fn into_inner(self) -> Vec<T> {
        self.0.into_iter().map(|c| c.0.into_inner()).collect()
    }

    pub fn current(&self) -> &mut T {
        use std::ops::Index;

        unsafe {
            &mut *(self.0.index(THREAD_INDEX.with(|t| *t)).0.get())
        }
    }
}

impl<T> ThreadLocal<Vec<T>> {
    pub fn collect(self) -> Vec<T> {
        self.into_inner().into_iter().flat_map(|v| v).collect()
    }
}

// The name of the associated type for `Fn` return types
pub const FN_OUTPUT_NAME: &'static str = "Output";

// Useful type to use with `Result<>` indicate that an error has already
// been reported to the user, so no need to continue checking.
#[derive(Clone, Copy, Debug, RustcEncodable, RustcDecodable)]
pub struct ErrorReported;

thread_local!(static TIME_DEPTH: Cell<usize> = Cell::new(0));

/// Initialized for -Z profile-queries
scoped_thread_local!(pub static PROFQ_CHAN: Lock<Option<Sender<ProfileQueriesMsg>>>);

/// Parameters to the `Dump` variant of type `ProfileQueriesMsg`.
#[derive(Clone,Debug)]
pub struct ProfQDumpParams {
    /// A base path for the files we will dump
    pub path:String,
    /// To ensure that the compiler waits for us to finish our dumps
    pub ack:Sender<()>,
    /// toggle dumping a log file with every `ProfileQueriesMsg`
    pub dump_profq_msg_log:bool,
}

/// A sequence of these messages induce a trace of query-based incremental compilation.
/// FIXME(matthewhammer): Determine whether we should include cycle detection here or not.
#[derive(Clone,Debug)]
pub enum ProfileQueriesMsg {
    /// begin a timed pass
    TimeBegin(String),
    /// end a timed pass
    TimeEnd,
    /// begin a task (see dep_graph::graph::with_task)
    TaskBegin(DepNode),
    /// end a task
    TaskEnd,
    /// begin a new query
    /// can't use `Span` because queries are sent to other thread
    QueryBegin(SpanData, QueryMsg),
    /// query is satisfied by using an already-known value for the given key
    CacheHit,
    /// query requires running a provider; providers may nest, permitting queries to nest.
    ProviderBegin,
    /// query is satisfied by a provider terminating with a value
    ProviderEnd,
    /// dump a record of the queries to the given path
    Dump(ProfQDumpParams),
    /// halt the profiling/monitoring background thread
    Halt
}

/// If enabled, send a message to the profile-queries thread
pub fn profq_msg(msg: ProfileQueriesMsg) {
    if !PROFQ_CHAN.is_set() {
        // This is not set in trans, see comment below
        return;
    }

    PROFQ_CHAN.with(|sender| {
        if let Some(s) = sender.borrow().as_ref() {
            s.send(msg).unwrap()
        } else {
            // Do nothing.
            //
            // FIXME(matthewhammer): Multi-threaded translation phase triggers the panic below.
            // From backtrace: rustc_trans::back::write::spawn_work::{{closure}}.
            //
            // panic!("no channel on which to send profq_msg: {:?}", msg)
        }
    })
}

/// Set channel for profile queries channel
pub fn profq_set_chan(s: Sender<ProfileQueriesMsg>) -> bool {
    PROFQ_CHAN.with(|chan| {
        if chan.borrow().is_none() {
            *chan.borrow_mut() = Some(s);
            true
        } else { false }
    })
}

/// Read the current depth of `time()` calls. This is used to
/// encourage indentation across threads.
pub fn time_depth() -> usize {
    TIME_DEPTH.with(|slot| slot.get())
}

/// Set the current depth of `time()` calls. The idea is to call
/// `set_time_depth()` with the result from `time_depth()` in the
/// parent thread.
pub fn set_time_depth(depth: usize) {
    TIME_DEPTH.with(|slot| slot.set(depth));
}

pub fn time<T, F>(do_it: bool, what: &str, f: F) -> T where
    F: FnOnce() -> T,
{
    if !do_it { return f(); }

    let old = TIME_DEPTH.with(|slot| {
        let r = slot.get();
        slot.set(r + 1);
        r
    });

    if cfg!(debug_assertions) {
        profq_msg(ProfileQueriesMsg::TimeBegin(what.to_string()))
    };

    #[cfg(not(all(windows, parallel_queries, any(target_arch = "x86", target_arch = "x86_64"))))]
    let rv = time_impl(what, f);
    #[cfg(all(windows, parallel_queries, any(target_arch = "x86", target_arch = "x86_64")))]
    let rv = time_threads_impl(what, f);

    TIME_DEPTH.with(|slot| slot.set(old));

    rv
}

fn time_impl<T, F>(what: &str, f: F) -> T where
    F: FnOnce() -> T,
{
    let start = Instant::now();
    let rv = f();
    let dur = start.elapsed();
    if cfg!(debug_assertions) {
        profq_msg(ProfileQueriesMsg::TimeEnd)
    };
    print_time_passes_entry_internal(what, duration_to_secs_str(dur));
    rv
}

#[cfg(all(windows, parallel_queries, any(target_arch = "x86", target_arch = "x86_64")))]
fn time_threads_impl<T, F>(what: &str, f: F) -> T where
    F: FnOnce() -> T,
{
    use rayon_core::registry;
    use std::iter;
    use winapi;
    use kernel32;

    #[allow(unused_mut)]
    fn read_counter() -> u64 {
        let mut low: u32;
        let mut high: u32;

        unsafe {
            asm!("xor %rax, %rax; cpuid; rdtsc"
                : "={eax}" (low), "={edx}" (high) :: "memory", "rbx", "rcx");
        }

        ((high as u64) << 32) | (low as u64)
    }

    let registry = registry::get_current_registry();
    if let Some(registry) = registry {
        let freq = unsafe {
            let mut freq = 0;
            assert!(kernel32::QueryPerformanceFrequency(&mut freq) == winapi::TRUE);
            freq as u64 * 1000
        };

        let threads: Vec<_> = {
            let threads = registry.handles.lock();
            let current = unsafe {
                iter::once(kernel32::GetCurrentThread())
            };
            current.chain(threads.iter().map(|t| t.0)).collect()
        };
        let mut begin: Vec<u64> = iter::repeat(0).take(threads.len()).collect();
        let mut end: Vec<u64> = iter::repeat(0).take(threads.len()).collect();
        for (i, &handle) in threads.iter().enumerate() {
            unsafe {
                assert!(kernel32::QueryThreadCycleTime(handle, &mut begin[i]) == winapi::TRUE);
            }
        }

        let time_start = read_counter();
        let result = f();
        let time_end = read_counter();
        for (i, &handle) in threads.iter().enumerate() {
            unsafe {
                assert!(kernel32::QueryThreadCycleTime(handle, &mut end[i]) == winapi::TRUE);
            }
        }
        if cfg!(debug_assertions) {
            profq_msg(ProfileQueriesMsg::TimeEnd)
        };
        let time = time_end - time_start;
        let time_secs = time as f64 / freq as f64;

        let thread_times: Vec<u64> = end.iter().zip(begin.iter()).map(|(e, b)| *e - *b).collect();

        let total_thread_time: u64 = thread_times.iter().cloned().sum();
        let core_usage = total_thread_time as f64 / time as f64;

        let mut data = format!("{:.6} - cores {:.2}x - cpu {:.2} - threads (",
                           time_secs,
                           core_usage,
                           core_usage / (thread_times.len() - 1) as f64);

        for (i, thread_time) in thread_times.into_iter().enumerate() {
            data.push_str(&format!("{:.2}", thread_time as f64 / time as f64));
            if i == 0 {
                data.push_str(" - ");
            }
            else if i < begin.len() - 1 {
                data.push_str(" ");
            }
        }

        data.push_str(")");

        print_time_passes_entry_internal(what, data);
        result
    } else {
        time_impl(what, f)
    }
}

pub fn print_time_passes_entry(do_it: bool, what: &str, dur: Duration) {
    if !do_it {
        return
    }

    let old = TIME_DEPTH.with(|slot| {
        let r = slot.get();
        slot.set(r + 1);
        r
    });

    print_time_passes_entry_internal(what, duration_to_secs_str(dur));

    TIME_DEPTH.with(|slot| slot.set(old));
}

fn print_time_passes_entry_internal(what: &str, data: String) {
    let indentation = TIME_DEPTH.with(|slot| slot.get());

    let mem_string = match get_resident() {
        Some(n) => {
            let mb = n as f64 / 1_000_000.0;
            format!("; rss: {}MB", mb.round() as usize)
        }
        None => "".to_owned(),
    };
    println!("{}time: {}{}\t{}",
             repeat("  ").take(indentation).collect::<String>(),
             data,
             mem_string,
             what);
}

// Hack up our own formatting for the duration to make it easier for scripts
// to parse (always use the same number of decimal places and the same unit).
pub fn duration_to_secs_str(dur: Duration) -> String {
    const NANOS_PER_SEC: f64 = 1_000_000_000.0;
    let secs = dur.as_secs() as f64 +
               dur.subsec_nanos() as f64 / NANOS_PER_SEC;

    format!("{:.6}", secs)
}

pub fn to_readable_str(mut val: usize) -> String {
    let mut groups = vec![];
    loop {
        let group = val % 1000;

        val /= 1000;

        if val == 0 {
            groups.push(format!("{}", group));
            break;
        } else {
            groups.push(format!("{:03}", group));
        }
    }

    groups.reverse();

    groups.join("_")
}

pub fn record_time<T, F>(accu: &LockCell<Duration>, f: F) -> T where
    F: FnOnce() -> T,
{
    let start = Instant::now();
    let rv = f();
    let duration = start.elapsed();
    accu.set(duration + accu.get());
    rv
}

// Memory reporting
#[cfg(unix)]
fn get_resident() -> Option<usize> {
    use std::fs;

    let field = 1;
    let contents = fs::read_string("/proc/self/statm").ok()?;
    let s = contents.split_whitespace().nth(field)?;
    let npages = s.parse::<usize>().ok()?;
    Some(npages * 4096)
}

#[cfg(windows)]
fn get_resident() -> Option<usize> {
    type BOOL = i32;
    type DWORD = u32;
    type HANDLE = *mut u8;
    use libc::size_t;
    use std::mem;
    #[repr(C)]
    #[allow(non_snake_case)]
    struct PROCESS_MEMORY_COUNTERS {
        cb: DWORD,
        PageFaultCount: DWORD,
        PeakWorkingSetSize: size_t,
        WorkingSetSize: size_t,
        QuotaPeakPagedPoolUsage: size_t,
        QuotaPagedPoolUsage: size_t,
        QuotaPeakNonPagedPoolUsage: size_t,
        QuotaNonPagedPoolUsage: size_t,
        PagefileUsage: size_t,
        PeakPagefileUsage: size_t,
    }
    type PPROCESS_MEMORY_COUNTERS = *mut PROCESS_MEMORY_COUNTERS;
    #[link(name = "psapi")]
    extern "system" {
        fn GetCurrentProcess() -> HANDLE;
        fn GetProcessMemoryInfo(Process: HANDLE,
                                ppsmemCounters: PPROCESS_MEMORY_COUNTERS,
                                cb: DWORD) -> BOOL;
    }
    let mut pmc: PROCESS_MEMORY_COUNTERS = unsafe { mem::zeroed() };
    pmc.cb = mem::size_of_val(&pmc) as DWORD;
    match unsafe { GetProcessMemoryInfo(GetCurrentProcess(), &mut pmc, pmc.cb) } {
        0 => None,
        _ => Some(pmc.WorkingSetSize as usize),
    }
}

pub fn indent<R, F>(op: F) -> R where
    R: Debug,
    F: FnOnce() -> R,
{
    // Use in conjunction with the log post-processor like `src/etc/indenter`
    // to make debug output more readable.
    debug!(">>");
    let r = op();
    debug!("<< (Result = {:?})", r);
    r
}

pub struct Indenter {
    _cannot_construct_outside_of_this_module: (),
}

impl Drop for Indenter {
    fn drop(&mut self) { debug!("<<"); }
}

pub fn indenter() -> Indenter {
    debug!(">>");
    Indenter { _cannot_construct_outside_of_this_module: () }
}

pub trait MemoizationMap {
    type Key: Clone;
    type Value: Clone;

    /// If `key` is present in the map, return the value,
    /// otherwise invoke `op` and store the value in the map.
    ///
    /// NB: if the receiver is a `DepTrackingMap`, special care is
    /// needed in the `op` to ensure that the correct edges are
    /// added into the dep graph. See the `DepTrackingMap` impl for
    /// more details!
    fn memoize<OP>(&self, key: Self::Key, op: OP) -> Self::Value
        where OP: FnOnce() -> Self::Value;
}

impl<K, V, S> MemoizationMap for RefCell<HashMap<K,V,S>>
    where K: Hash+Eq+Clone, V: Clone, S: BuildHasher
{
    type Key = K;
    type Value = V;

    fn memoize<OP>(&self, key: K, op: OP) -> V
        where OP: FnOnce() -> V
    {
        let result = self.borrow().get(&key).cloned();
        match result {
            Some(result) => result,
            None => {
                let result = op();
                self.borrow_mut().insert(key, result.clone());
                result
            }
        }
    }
}

#[cfg(unix)]
pub fn path2cstr(p: &Path) -> CString {
    use std::os::unix::prelude::*;
    use std::ffi::OsStr;
    let p: &OsStr = p.as_ref();
    CString::new(p.as_bytes()).unwrap()
}
#[cfg(windows)]
pub fn path2cstr(p: &Path) -> CString {
    CString::new(p.to_str().unwrap()).unwrap()
}


#[test]
fn test_to_readable_str() {
    assert_eq!("0", to_readable_str(0));
    assert_eq!("1", to_readable_str(1));
    assert_eq!("99", to_readable_str(99));
    assert_eq!("999", to_readable_str(999));
    assert_eq!("1_000", to_readable_str(1_000));
    assert_eq!("1_001", to_readable_str(1_001));
    assert_eq!("999_999", to_readable_str(999_999));
    assert_eq!("1_000_000", to_readable_str(1_000_000));
    assert_eq!("1_234_567", to_readable_str(1_234_567));
}
