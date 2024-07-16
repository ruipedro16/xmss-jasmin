#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
This script reads the JSON containing information about the template functions from stdin

It should be run something like the following

./jpp ...
./preprocessor -in ... --print_tasks | ./remove_sha256.py -d -in ...
"""


import json
import pprint
import re
import sys

import argparse
from argparse import Namespace

########################################################################################################################


def remove_proc(proc: str, input_text: str) -> str:
    """
    This functions removes a procedure from an EasyCrytpt module

    :param proc: Name of the procedure to remove
    :param input_text:
    :return:
    """

    assert input_text is not None
    assert proc is not None

    # 1st group: procedure to remove
    # 2nd group: Delimiter -- either the proc keyword of the next procedure or the end of the module -- }.
    #            We dont want to remove either of them
    proc_regex = rf"(proc {proc}[\s\S]+?)" + r"(proc|}\.)"

    output_text = re.sub(proc_regex, r"\2", input_text, count=1)  # r"\2": Keep the second group
    return output_text


def remove_functions(input_text: str, template_functions_dict, debug: bool) -> str:
    """
    Removes functions related to SHA256 from an EasyCrypt module

    :param input_text:
    :return:
    """

    assert input_text is not None

    # Regular expression to remove the global variable SHA256_K
    global_k_pattern = r"abbrev sHA256_K[\s\S]+\]\."

    generic_functions: list[str] = [
        # Hash functions: These are replaced by operators
        "__lastblocks_ref",
        "__sha256",
        "_blocks_0_ref",
        "__core_hash",
        "_core_hash",
        "__core_hash_",
    ]

    resolved_functions: list[str] = []

    for f in generic_functions:
        try:
            resolved_functions += [item.strip() for item in template_functions_dict[f]["resolved fn"].split(",")]
        except KeyError:  # "resolved fn" does not exist in the template functions_dict
            print(f"could not find {f} in template_functions_dict")

    regular_functions: list[str] = [
        # SHA256 FUNCTIONS
        "__initH_ref",
        "__load_H_ref",
        "__store_H_ref",
        "_blocks_1_ref",
        "__store_ref_array",
        "_blocks_0_ref",
        "__lastblocks_ref",
        "__Wt_ref",
        "__SSIG1_ref",
        "__SSIG0_ref",
        "__BSIG1_ref",
        "__BSIG0_ref",
        "__SHR_ref",
        "__MAJ_ref",
        "__ROTR_ref",
        "__CH_ref",
        "__sha256_in_ptr",
        # CORE HASH FUNCTIONS
        "__core_hash_in_ptr",
        "_core_hash_in_ptr",
        "__core_hash_in_ptr_",
        # _PRF_ FUNCTIONS
        "__prf_",
        "_prf",
        "__prf",
        "__prf_keygen_",
        "__prf_keygen",
        "_prf_keygen",
    ]

    functions_to_remove: list[str] = resolved_functions + regular_functions

    output_text = re.sub(global_k_pattern, "", input_text, flags=re.MULTILINE)

    for f in functions_to_remove:
        output_text = remove_proc(f, output_text)

        if debug:
            print(f"Removing procedure {f}")

    return output_text


def add_operators(text: str) -> str:
    assert text is not None

    string_to_add = """
require import XMSS_IMPL Generic.

op Hash : W8.t list -> W8.t list.
op Hash_ptr : W64.t -> W64.t -> W8.t Array32.t.

op _PRF_ : W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t.

op _PRF_KEYGEN_ : W8.t Array64.t -> W8.t Array32.t -> W8.t Array32.t.
"""

    t = text.rfind("module")
    return text[:t] + string_to_add + "\n" + text[t:]


def replace_calls(text: str) -> str:
    text = text.replace(
        "mhash <@ __core_hash_in_ptr_ (mhash, m_with_prefix_ptr, len);", "mhash <- Hash_ptr m_with_prefix_ptr len;"
    )

    text = text.replace(
"""
    aux <@ __prf_ ((Array32.init (fun i_0 => buf.[32 + i_0])), addr_as_bytes,
    pub_seed);
 """,
"""
    aux <- _PRF_ (Array32.init (fun i_0 => buf.[32 + i_0])) addr_as_bytes pub_seed; 
"""
    )

    text = text.replace(
"""
    aux <@ __prf_ ((Array32.init (fun i_0 => bitmask.[0 + i_0])),
    addr_as_bytes, pub_seed);
""",
"""
    aux <- _PRF_ (Array32.init (fun i_0 => bitmask.[0 + i_0])) addr_as_bytes pub_seed;
"""
    )

    text = text.replace(
'''
    aux <@ __prf_ ((Array32.init (fun i_0 => bitmask.[32 + i_0])),
    addr_as_bytes, pub_seed);
''',
'''
    aux <- _PRF_ (Array32.init (fun i_0 => bitmask.[32 + i_0])) addr_as_bytes pub_seed;
'''
        )
    
    text = text.replace(
'''
  proc __thash_h (out:W8.t Array32.t, in_0:W8.t Array64.t,
                  pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : W8.t Array32.t *
                                                                  W32.t Array8.t = {
    var aux: W8.t Array32.t;
''',
'''
  proc __thash_h (out:W8.t Array32.t, in_0:W8.t Array64.t,
                  pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : W8.t Array32.t *
                                                                  W32.t Array8.t = {
    var aux: W8.t Array32.t;
    var out_list : W8.t list;
'''
    )
    
    text = text.replace(
'''
    out <@ _core_hash_128 (out, buf);
''',
'''
    out_list <- Hash (to_list buf);
    out <- Array32.of_list witness out_list;
'''
    )

    text = text.replace(
'''
    bitmask <@ __prf_ (bitmask, addr_as_bytes, pub_seed);
''',
'''
    bitmask <-_PRF_ bitmask addr_as_bytes pub_seed;
'''
    )

    text = text.replace(
'''
  proc __thash_f (out:W8.t Array32.t, pub_seed:W8.t Array32.t,
                  addr:W32.t Array8.t) : W8.t Array32.t * W32.t Array8.t = {
    var aux: W8.t Array32.t;
''',
'''
  proc __thash_f (out:W8.t Array32.t, pub_seed:W8.t Array32.t,
                  addr:W32.t Array8.t) : W8.t Array32.t * W32.t Array8.t = {
    var aux: W8.t Array32.t;
    var out_list : W8.t list;
'''
    )

    text = text.replace(
'''
    out <@ __core_hash__96 (out, buf);
''',
'''

    out_list <- Hash (to_list buf);    
    out <- Array32.of_list witness out_list;
'''
    )

    text = text.replace(
'''
  proc __expand_seed (outseeds:W8.t Array2144.t, inseed:W8.t Array32.t,
                      pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array2144.t * W32.t Array8.t = {
    var aux_0: int;
    var aux: W8.t Array32.t;
''',
'''
  proc __expand_seed (outseeds:W8.t Array2144.t, inseed:W8.t Array32.t,
                      pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array2144.t * W32.t Array8.t = {
    var aux_0: int;
    var aux: W8.t Array32.t;
    var aux_list : W8.t list;
'''
    )

    text = text.replace('ith_seed <@ __prf_keygen_ (ith_seed, buf, inseed);', 
'''
    ith_seed <- _PRF_KEYGEN_ buf inseed;
''')

    text = text.replace('buf <@ __prf_ (buf, idx_bytes, sk_prf);', 'buf <- _PRF_ buf idx_bytes sk_prf;')

    return text


def preprocess_ec(ec_in: str, template_functions_dict, debug: bool) -> str:
    ec_out = ec_in.replace("module M(SC:Syscall_t)", "module M_Hop1(SC:Syscall_t)")

    ec_out = ec_out.replace(
'''
module type Syscall_t = {
  proc randombytes_96(_:W8.t Array96.t) : W8.t Array96.t
}.

module Syscall : Syscall_t = {
  proc randombytes_96(a:W8.t Array96.t) : W8.t Array96.t = {
    a <$ dmap WArray96.darray
         (fun a => Array96.init (fun i => WArray96.get8 a i));
    return a;
  }
}.
''',
''
)

# import the new file
    ec_out = ec_out.replace(
'''require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.
''',
'''require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

require import RandomBytes.
'''
)

    ec_out = ec_out.replace("(* Erased call to spill *)", "")
    ec_out = ec_out.replace("(* Erased call to unspill *)", "")

    ec_out = remove_functions(ec_out, template_functions_dict, debug)
    ec_out = add_operators(ec_out)
    ec_out = replace_calls(ec_out)

    ec_out = re.sub(r"\n\s*\n+", "\n\n", ec_out)  # Remove whitespace
    ec_out = re.sub(r"else\s*{\s*}", "", ec_out)  # Remove empty else statements

    return ec_out


def parse_args() -> Namespace:
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "-in",
        "--input_file",
        required=True,
        help="Input file path",
        type=str,
    )

    # if -out is not set, we print to stdout
    parser.add_argument(
        "-out",
        "--output_file",
        required=False,
        help="Output file path",
        type=str,
    )

    parser.add_argument(
        "-d",
        "--debug",
        help="Enable debugging",
        action="store_true",
    )

    return parser.parse_args()


def main():
    args: Namespace = parse_args()

    input_str: str = ""

    try:
        input_str = sys.stdin.read()

        if args.debug:
            print(input_str)

        template_functions_dict = json.loads(input_str)
    except TypeError:
        sys.stderr.write("[TypeError]: could not load JSON - the JSON object must be str, bytes or bytearray\n")

        if args.debug:
            sys.stderr.write(f"{input_str}\n")

        sys.exit(-1)
    except json.decoder.JSONDecodeError:
        sys.stderr.write("[JSONDecodeError]: could not decode JSON (malformed)\n")

        if args.debug:
            sys.stderr.write(f"{input_str}\n")

        sys.exit(-1)

    if args.debug:
        print("Generic Functions JSON:")
        pprint.pprint(template_functions_dict)
        print("\n")

    with open(args.input_file, "r", encoding="utf-8") as f:
        ec_in: str = f.read()

    ec_out = preprocess_ec(ec_in, template_functions_dict, args.debug)

    if out_f := args.output_file:
        with open(out_f, "w", encoding="utf-8") as f:
            f.write(ec_out)
    else:
        print(ec_out)


if __name__ == "__main__":
    main()
