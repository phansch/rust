#!/usr/bin/env python

"""
Regenerate Unicode tables (tables.rs).
"""

# This script uses the Unicode tables as defined
# in the UnicodeFiles class.

# Since this should not require frequent updates, we just store this
# out-of-line and check the tables.rs file into git.

# Note that the "curl" program is required for operation.
# This script is compatible with Python 2.7 and 3.x.

import argparse
import datetime
import fileinput
import operator
import os
import re
import textwrap
import subprocess

from collections import namedtuple


# we don't use enum.Enum because of Python 2.7 compatibility
class UnicodeFiles(object):
    # ReadMe does not contain any unicode data, we
    # only use it to extract versions.
    README = "ReadMe.txt"

    DERIVED_CORE_PROPERTIES = "DerivedCoreProperties.txt"
    DERIVED_NORMALIZATION_PROPS = "DerivedNormalizationProps.txt"
    PROPS = "PropList.txt"
    SCRIPTS = "Scripts.txt"
    SPECIAL_CASING = "SpecialCasing.txt"
    UNICODE_DATA = "UnicodeData.txt"


UnicodeFiles.ALL_FILES = tuple(
    getattr(UnicodeFiles, name) for name in dir(UnicodeFiles)
    if not name.startswith("_")
)

# The directory this file is located in.
THIS_DIR = os.path.dirname(os.path.realpath(__file__))

# Where to download the Unicode data.  The downloaded files
# will be placed in sub-directories named after Unicode version.
FETCH_DIR = os.path.join(THIS_DIR, "downloaded")

FETCH_URL_LATEST = "ftp://ftp.unicode.org/Public/UNIDATA/{filename}"
FETCH_URL_VERSION = "ftp://ftp.unicode.org/Public/{version}/ucd/{filename}"

PREAMBLE = """\
// NOTE: The following code was generated by "./unicode.py", do not edit directly

#![allow(missing_docs, non_upper_case_globals, non_snake_case)]

use unicode::version::UnicodeVersion;
use unicode::bool_trie::{{BoolTrie, SmallBoolTrie}};
""".format(year=datetime.datetime.now().year)

# Mapping taken from Table 12 from:
# http://www.unicode.org/reports/tr44/#General_Category_Values
EXPANDED_CATEGORIES = {
    "Lu": ["LC", "L"], "Ll": ["LC", "L"], "Lt": ["LC", "L"],
    "Lm": ["L"], "Lo": ["L"],
    "Mn": ["M"], "Mc": ["M"], "Me": ["M"],
    "Nd": ["N"], "Nl": ["N"], "No": ["N"],
    "Pc": ["P"], "Pd": ["P"], "Ps": ["P"], "Pe": ["P"],
    "Pi": ["P"], "Pf": ["P"], "Po": ["P"],
    "Sm": ["S"], "Sc": ["S"], "Sk": ["S"], "So": ["S"],
    "Zs": ["Z"], "Zl": ["Z"], "Zp": ["Z"],
    "Cc": ["C"], "Cf": ["C"], "Cs": ["C"], "Co": ["C"], "Cn": ["C"],
}

# these are the surrogate codepoints, which are not valid rust characters
SURROGATE_CODEPOINTS = (0xd800, 0xdfff)

UnicodeData = namedtuple(
    "UnicodeData", ("canon_decomp", "compat_decomp", "gencats", "combines",
                    "to_upper", "to_lower", "to_title", )
)

UnicodeVersion = namedtuple(
    "UnicodeVersion", ("major", "minor", "micro", "as_str")
)


def fetch_files(version=None):
    """
    Fetch all the Unicode files from unicode.org

    :param version: The desired Unicode version, as string.
        (If None, defaults to latest final release available).
    :return: The version downloaded (UnicodeVersion object).
    """
    have_version = should_skip_fetch(version)
    if have_version:
        return have_version

    if version:
        # check if the desired version exists on the server
        get_fetch_url = lambda name: FETCH_URL_VERSION.format(version=version, filename=name)
    else:
        # extract the latest version
        get_fetch_url = lambda name: FETCH_URL_LATEST.format(filename=name)

    readme_url = get_fetch_url(UnicodeFiles.README)

    print("Fetching: {}".format(readme_url))
    readme_content = subprocess.check_output(("curl", readme_url))

    unicode_version = parse_unicode_version(
        readme_content.decode("utf8")
    )

    download_dir = os.path.join(FETCH_DIR, unicode_version.as_str)
    if not os.path.exists(download_dir):
        # for 2.7 compat, we don't use exist_ok=True
        os.makedirs(download_dir)

    for filename in UnicodeFiles.ALL_FILES:
        file_path = os.path.join(download_dir, filename)

        if filename == UnicodeFiles.README:
            with open(file_path, "wb") as fd:
                fd.write(readme_content)
        elif not os.path.exists(file_path):
            url = get_fetch_url(filename)
            print("Fetching: {}".format(url))
            subprocess.check_call(("curl", "-o", file_path, url))

    return unicode_version


def should_skip_fetch(version):
    if not version:
        # should always check latest version
        return False

    fetch_dir = os.path.join(FETCH_DIR, version)

    for filename in UnicodeFiles.ALL_FILES:
        file_path = os.path.join(fetch_dir, filename)

        if not os.path.exists(file_path):
            return False

    with open(os.path.join(fetch_dir, UnicodeFiles.README)) as fd:
        return parse_unicode_version(fd.read())


def parse_unicode_version(readme_content):
    # "raw string" is necessary for \d not being treated as escape char
    # (for the sake of compat with future Python versions)
    # see: https://docs.python.org/3.6/whatsnew/3.6.html#deprecated-python-behavior
    pattern = r"for Version (\d+)\.(\d+)\.(\d+) of the Unicode"
    groups = re.search(pattern, readme_content).groups()

    return UnicodeVersion(*map(int, groups), as_str=".".join(groups))


def get_unicode_file_path(unicode_version, filename):
    return os.path.join(FETCH_DIR, unicode_version.as_str, filename)


def is_surrogate(n):
    return SURROGATE_CODEPOINTS[0] <= n <= SURROGATE_CODEPOINTS[1]


def load_unicode_data(file_path):
    gencats = {}
    to_lower = {}
    to_upper = {}
    to_title = {}
    combines = {}
    canon_decomp = {}
    compat_decomp = {}

    udict = {}
    range_start = -1
    for line in fileinput.input(file_path):
        data = line.split(";")
        if len(data) != 15:
            continue
        cp = int(data[0], 16)
        if is_surrogate(cp):
            continue
        if range_start >= 0:
            for i in range(range_start, cp):
                udict[i] = data
            range_start = -1
        if data[1].endswith(", First>"):
            range_start = cp
            continue
        udict[cp] = data

    for code in udict:
        (code_org, name, gencat, combine, bidi,
         decomp, deci, digit, num, mirror,
         old, iso, upcase, lowcase, titlecase) = udict[code]

        # generate char to char direct common and simple conversions
        # uppercase to lowercase
        if lowcase != "" and code_org != lowcase:
            to_lower[code] = (int(lowcase, 16), 0, 0)

        # lowercase to uppercase
        if upcase != "" and code_org != upcase:
            to_upper[code] = (int(upcase, 16), 0, 0)

        # title case
        if titlecase.strip() != "" and code_org != titlecase:
            to_title[code] = (int(titlecase, 16), 0, 0)

        # store decomposition, if given
        if decomp != "":
            if decomp.startswith("<"):
                seq = []
                for i in decomp.split()[1:]:
                    seq.append(int(i, 16))
                compat_decomp[code] = seq
            else:
                seq = []
                for i in decomp.split():
                    seq.append(int(i, 16))
                canon_decomp[code] = seq

        # place letter in categories as appropriate
        for cat in [gencat, "Assigned"] + EXPANDED_CATEGORIES.get(gencat, []):
            if cat not in gencats:
                gencats[cat] = []
            gencats[cat].append(code)

        # record combining class, if any
        if combine != "0":
            if combine not in combines:
                combines[combine] = []
            combines[combine].append(code)

    # generate Not_Assigned from Assigned
    gencats["Cn"] = gen_unassigned(gencats["Assigned"])
    # Assigned is not a real category
    del(gencats["Assigned"])
    # Other contains Not_Assigned
    gencats["C"].extend(gencats["Cn"])
    gencats = group_cats(gencats)
    combines = to_combines(group_cats(combines))

    return UnicodeData(
        canon_decomp, compat_decomp, gencats, combines, to_upper,
        to_lower, to_title,
    )


def load_special_casing(file_path, unicode_data):
    for line in fileinput.input(file_path):
        data = line.split("#")[0].split(";")
        if len(data) == 5:
            code, lower, title, upper, _comment = data
        elif len(data) == 6:
            code, lower, title, upper, condition, _comment = data
            if condition.strip():  # Only keep unconditional mappins
                continue
        else:
            continue
        code = code.strip()
        lower = lower.strip()
        title = title.strip()
        upper = upper.strip()
        key = int(code, 16)
        for (map_, values) in ((unicode_data.to_lower, lower),
                               (unicode_data.to_upper, upper),
                               (unicode_data.to_title, title)):
            if values != code:
                values = [int(i, 16) for i in values.split()]
                for _ in range(len(values), 3):
                    values.append(0)
                assert len(values) == 3
                map_[key] = values


def group_cats(cats):
    cats_out = {}
    for cat in cats:
        cats_out[cat] = group_cat(cats[cat])
    return cats_out


def group_cat(cat):
    cat_out = []
    letters = sorted(set(cat))
    cur_start = letters.pop(0)
    cur_end = cur_start
    for letter in letters:
        assert letter > cur_end, \
            "cur_end: %s, letter: %s" % (hex(cur_end), hex(letter))
        if letter == cur_end + 1:
            cur_end = letter
        else:
            cat_out.append((cur_start, cur_end))
            cur_start = cur_end = letter
    cat_out.append((cur_start, cur_end))
    return cat_out


def ungroup_cat(cat):
    cat_out = []
    for (lo, hi) in cat:
        while lo <= hi:
            cat_out.append(lo)
            lo += 1
    return cat_out


def gen_unassigned(assigned):
    assigned = set(assigned)
    return ([i for i in range(0, 0xd800) if i not in assigned] +
            [i for i in range(0xe000, 0x110000) if i not in assigned])


def to_combines(combs):
    combs_out = []
    for comb in combs:
        for (lo, hi) in combs[comb]:
            combs_out.append((lo, hi, comb))
    combs_out.sort(key=lambda c: c[0])
    return combs_out


def format_table_content(f, content, indent):
    line = " " * indent
    first = True
    for chunk in content.split(","):
        if len(line) + len(chunk) < 98:
            if first:
                line += chunk
            else:
                line += ", " + chunk
            first = False
        else:
            f.write(line + ",\n")
            line = " " * indent + chunk
    f.write(line)


def load_properties(file_path, interestingprops):
    props = {}
    # "raw string" is necessary for \w not to be treated as escape char
    # (for the sake of compat with future Python versions)
    # see: https://docs.python.org/3.6/whatsnew/3.6.html#deprecated-python-behavior
    re1 = re.compile(r"^ *([0-9A-F]+) *; *(\w+)")
    re2 = re.compile(r"^ *([0-9A-F]+)\.\.([0-9A-F]+) *; *(\w+)")

    for line in fileinput.input(file_path):
        prop = None
        d_lo = 0
        d_hi = 0
        m = re1.match(line)
        if m:
            d_lo = m.group(1)
            d_hi = m.group(1)
            prop = m.group(2)
        else:
            m = re2.match(line)
            if m:
                d_lo = m.group(1)
                d_hi = m.group(2)
                prop = m.group(3)
            else:
                continue
        if interestingprops and prop not in interestingprops:
            continue
        d_lo = int(d_lo, 16)
        d_hi = int(d_hi, 16)
        if prop not in props:
            props[prop] = []
        props[prop].append((d_lo, d_hi))

    # optimize if possible
    for prop in props:
        props[prop] = group_cat(ungroup_cat(props[prop]))

    return props


def escape_char(c):
    return "'\\u{%x}'" % c if c != 0 else "'\\0'"


def emit_table(f, name, t_data, t_type="&[(char, char)]", is_pub=True,
        pfun=lambda x: "(%s,%s)" % (escape_char(x[0]), escape_char(x[1]))):
    pub_string = ""
    if is_pub:
        pub_string = "pub "
    f.write("    %sconst %s: %s = &[\n" % (pub_string, name, t_type))
    data = ""
    first = True
    for dat in t_data:
        if not first:
            data += ","
        first = False
        data += pfun(dat)
    format_table_content(f, data, 8)
    f.write("\n    ];\n\n")


def compute_trie(rawdata, chunksize):
    root = []
    childmap = {}
    child_data = []
    for i in range(len(rawdata) // chunksize):
        data = rawdata[i * chunksize: (i + 1) * chunksize]
        child = "|".join(map(str, data))
        if child not in childmap:
            childmap[child] = len(childmap)
            child_data.extend(data)
        root.append(childmap[child])
    return root, child_data


def emit_bool_trie(f, name, t_data, is_pub=True):
    chunk_size = 64
    rawdata = [False] * 0x110000
    for (lo, hi) in t_data:
        for cp in range(lo, hi + 1):
            rawdata[cp] = True

    # convert to bitmap chunks of 64 bits each
    chunks = []
    for i in range(0x110000 // chunk_size):
        chunk = 0
        for j in range(64):
            if rawdata[i * 64 + j]:
                chunk |= 1 << j
        chunks.append(chunk)

    pub_string = ""
    if is_pub:
        pub_string = "pub "
    f.write("    %sconst %s: &super::BoolTrie = &super::BoolTrie {\n" % (pub_string, name))
    f.write("        r1: [\n")
    data = ",".join("0x%016x" % chunk for chunk in chunks[0:0x800 // chunk_size])
    format_table_content(f, data, 12)
    f.write("\n        ],\n")

    # 0x800..0x10000 trie
    (r2, r3) = compute_trie(chunks[0x800 // chunk_size : 0x10000 // chunk_size], 64 // chunk_size)
    f.write("        r2: [\n")
    data = ",".join(str(node) for node in r2)
    format_table_content(f, data, 12)
    f.write("\n        ],\n")
    f.write("        r3: &[\n")
    data = ",".join("0x%016x" % chunk for chunk in r3)
    format_table_content(f, data, 12)
    f.write("\n        ],\n")

    # 0x10000..0x110000 trie
    (mid, r6) = compute_trie(chunks[0x10000 // chunk_size : 0x110000 // chunk_size], 64 // chunk_size)
    (r4, r5) = compute_trie(mid, 64)
    f.write("        r4: [\n")
    data = ",".join(str(node) for node in r4)
    format_table_content(f, data, 12)
    f.write("\n        ],\n")
    f.write("        r5: &[\n")
    data = ",".join(str(node) for node in r5)
    format_table_content(f, data, 12)
    f.write("\n        ],\n")
    f.write("        r6: &[\n")
    data = ",".join("0x%016x" % chunk for chunk in r6)
    format_table_content(f, data, 12)
    f.write("\n        ],\n")

    f.write("    };\n\n")


def emit_small_bool_trie(f, name, t_data, is_pub=True):
    last_chunk = max(hi // 64 for (lo, hi) in t_data)
    n_chunks = last_chunk + 1
    chunks = [0] * n_chunks
    for (lo, hi) in t_data:
        for cp in range(lo, hi + 1):
            if cp // 64 >= len(chunks):
                print(cp, cp // 64, len(chunks), lo, hi)
            chunks[cp // 64] |= 1 << (cp & 63)

    pub_string = ""
    if is_pub:
        pub_string = "pub "
    f.write("    %sconst %s: &super::SmallBoolTrie = &super::SmallBoolTrie {\n"
            % (pub_string, name))

    (r1, r2) = compute_trie(chunks, 1)

    f.write("        r1: &[\n")
    data = ",".join(str(node) for node in r1)
    format_table_content(f, data, 12)
    f.write("\n        ],\n")

    f.write("        r2: &[\n")
    data = ",".join("0x%016x" % node for node in r2)
    format_table_content(f, data, 12)
    f.write("\n        ],\n")

    f.write("    };\n\n")


def emit_property_module(f, mod, tbl, emit):
    f.write("pub mod %s {\n" % mod)
    for cat in sorted(emit):
        if cat in ["Cc", "White_Space", "Pattern_White_Space"]:
            emit_small_bool_trie(f, "%s_table" % cat, tbl[cat])
            f.write("    pub fn %s(c: char) -> bool {\n" % cat)
            f.write("        %s_table.lookup(c)\n" % cat)
            f.write("    }\n\n")
        else:
            emit_bool_trie(f, "%s_table" % cat, tbl[cat])
            f.write("    pub fn %s(c: char) -> bool {\n" % cat)
            f.write("        %s_table.lookup(c)\n" % cat)
            f.write("    }\n\n")
    f.write("}\n\n")


def emit_conversions_module(f, unicode_data):
    f.write("pub mod conversions {")
    f.write("""
    pub fn to_lower(c: char) -> [char; 3] {
        match bsearch_case_table(c, to_lowercase_table) {
            None        => [c, '\\0', '\\0'],
            Some(index) => to_lowercase_table[index].1,
        }
    }

    pub fn to_upper(c: char) -> [char; 3] {
        match bsearch_case_table(c, to_uppercase_table) {
            None        => [c, '\\0', '\\0'],
            Some(index) => to_uppercase_table[index].1,
        }
    }

    fn bsearch_case_table(c: char, table: &[(char, [char; 3])]) -> Option<usize> {
        table.binary_search_by(|&(key, _)| key.cmp(&c)).ok()
    }

""")
    t_type = "&[(char, [char; 3])]"
    pfun = lambda x: "(%s,[%s,%s,%s])" % (
        escape_char(x[0]), escape_char(x[1][0]), escape_char(x[1][1]), escape_char(x[1][2]))

    emit_table(f,
               name="to_lowercase_table",
               t_data=sorted(unicode_data.to_lower.items(), key=operator.itemgetter(0)),
               t_type=t_type,
               is_pub=False,
               pfun=pfun)

    emit_table(f,
               name="to_uppercase_table",
               t_data=sorted(unicode_data.to_upper.items(), key=operator.itemgetter(0)),
               t_type=t_type,
               is_pub=False,
               pfun=pfun)

    f.write("}\n")


def emit_norm_module(f, unicode_data, norm_props):
    canon_keys = sorted(unicode_data.canon_decomp.keys())

    canon_comp = {}
    comp_exclusions = norm_props["Full_Composition_Exclusion"]
    for char in canon_keys:
        if any(lo <= char <= hi for lo, hi in comp_exclusions):
            continue
        decomp = unicode_data.canon_decomp[char]
        if len(decomp) == 2:
            if decomp[0] not in canon_comp:
                canon_comp[decomp[0]] = []
            canon_comp[decomp[0]].append((decomp[1], char))


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("-v", "--version", default=None, type=str,
                        help="Unicode version to use (if not specified,"
                             " defaults to latest available final release).")

    return parser.parse_args()


def main():
    args = parse_args()

    unicode_version = fetch_files(args.version)
    print("Using Unicode version: {}".format(unicode_version.as_str))

    tables_rs_path = os.path.join(THIS_DIR, "tables.rs")

    # will overwrite the file if it exists
    with open(tables_rs_path, "w") as rf:
        rf.write(PREAMBLE)

        unicode_version_notice = textwrap.dedent("""
        /// The version of [Unicode](http://www.unicode.org/) that the Unicode parts of
        /// `char` and `str` methods are based on.
        #[unstable(feature = "unicode_version", issue = "49726")]
        pub const UNICODE_VERSION: UnicodeVersion = UnicodeVersion {{
            major: {version.major},
            minor: {version.minor},
            micro: {version.micro},
            _priv: (),
        }};
        """).format(version=unicode_version)
        rf.write(unicode_version_notice)

        get_path = lambda f: get_unicode_file_path(unicode_version, f)

        unicode_data = load_unicode_data(get_path(UnicodeFiles.UNICODE_DATA))
        load_special_casing(get_path(UnicodeFiles.SPECIAL_CASING), unicode_data)

        want_derived = ["XID_Start", "XID_Continue", "Alphabetic", "Lowercase", "Uppercase",
                        "Cased", "Case_Ignorable", "Grapheme_Extend"]
        derived = load_properties(get_path(UnicodeFiles.DERIVED_CORE_PROPERTIES), want_derived)

        # TODO scripts not used?
        scripts = load_properties(get_path(UnicodeFiles.SCRIPTS), [])
        props = load_properties(get_path(UnicodeFiles.PROPS),
                                ["White_Space", "Join_Control", "Noncharacter_Code_Point",
                                 "Pattern_White_Space"])
        norm_props = load_properties(get_path(UnicodeFiles.DERIVED_NORMALIZATION_PROPS),
                                     ["Full_Composition_Exclusion"])

        # category tables
        for (name, cat, pfuns) in (("general_category", unicode_data.gencats, ["N", "Cc"]),
                                   ("derived_property", derived, want_derived),
                                   ("property", props, ["White_Space", "Pattern_White_Space"])):
            emit_property_module(rf, name, cat, pfuns)

        # normalizations and conversions module
        emit_norm_module(rf, unicode_data, norm_props)
        emit_conversions_module(rf, unicode_data)

    print("Regenerated tables.rs.")


if __name__ == "__main__":
    main()
