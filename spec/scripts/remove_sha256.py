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
        # Generic Functions: These are replaced by a single functions that takes lists instead of arrays as arguments
        "__base_w"
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
        # PRF FUNCTIONS
        "__prf_",
        "_prf",
        "__prf",
    ]

    functions_to_remove: list[str] = resolved_functions + regular_functions

    output_text = re.sub(global_k_pattern, "", input_text, flags=re.MULTILINE)

    for f in functions_to_remove:
        output_text = remove_proc(f, output_text)

        if debug:
            print(f"Removing procedure {f}")

    return output_text


def add_operators(text: str) -> str:
    string_to_add = """
require import XMSS_IMPL Generic.

op Hash_96 : W8.t Array32.t -> W8.t Array96.t -> W8.t Array32.t.
op Hash_128 : W8.t Array32.t -> W8.t Array128.t -> W8.t Array32.t.
op Hash_ptr : W8.t Array32.t -> W64.t -> W64.t -> W8.t Array32.t.

op PRF : W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t.
"""
    t = text.rfind("module")
    return text[:t] + string_to_add + "\n" + text[t:]


def replace_calls(text: str) -> str:
    """
    Run 
        grep -nr "core_hash" | cut -d ' ' -f 4 | uniq | grep -v '^$' 
    to get this list

    """

    functions: list[str] = [
        "__core_hash_96",
        "_core_hash_96",
        "__core_hash__96",
        "__core_hash_128",
        "_core_hash_128",
        "__core_hash_in_ptr_",
        "__core_hash_in_ptr",
        "_core_hash_in_ptr",
    ]

    for f in functions:
        pattern = rf"<@ ({f}) \(([^)]+), ([^)]+)\);"
        replacement = r"<- \1 \2 \3;"
        text = re.sub(pattern, replacement, text)

    text = text.replace("__core_hash_96", "Hash_96")
    text = text.replace("_core_hash_96", "Hash_96")
    text = text.replace("__core_hash__96", "Hash_96")

    text = text.replace("__core_hash_128", "Hash_128")
    text = text.replace("_core_hash_128", "Hash_128")
    text = text.replace("__core_hash__128", "Hash_128")

    text = text.replace("__core_hash_in_ptr_", "Hash_ptr")
    text = text.replace("__core_hash_in_ptr", "Hash_ptr")
    text = text.replace("_core_hash_in_ptr", "Hash_ptr")

    text = text.replace(
        "mhash <- Hash_ptr mhash, m_with_prefix_ptr len;", "mhash <- Hash_ptr mhash m_with_prefix_ptr len;"
    )

    text = text.replace(
"""
    aux <@ __prf_ ((Array32.init (fun i_0 => buf.[32 + i_0])), addr_as_bytes,
    pub_seed);
""",
"""
    aux <- PRF (Array32.init (fun i_0 => buf.[32 + i_0])) addr_as_bytes pub_seed;
"""
)
    
    text = text.replace(
"""
    aux <@ __prf_ ((Array32.init (fun i_0 => bitmask.[0 + i_0])),
    addr_as_bytes, pub_seed);
""",
"""
    aux <- PRF (Array32.init (fun i_0 => bitmask.[0 + i_0])) addr_as_bytes pub_seed;
"""
    )

    text = text.replace(
"""
    aux <@ __prf_ ((Array32.init (fun i_0 => bitmask.[32 + i_0])),
    addr_as_bytes, pub_seed);
""",
"""
    aux <- PRF (Array32.init (fun i_0 => bitmask.[32 + i_0])) addr_as_bytes pub_seed;
"""
    )

    text = text.replace("bitmask <@ __prf_ (bitmask, addr_as_bytes, pub_seed);", "bitmask <- PRF bitmask addr_as_bytes pub_seed;")
    text = text.replace("buf <@ __prf_ (buf, idx_bytes, sk_prf);", "buf <- PRF buf idx_bytes sk_prf;")


    # Replace functions that take arrays as arguments with functions that take lists

    #1) Base W

    text = text.replace (
"""
  proc __wots_checksum (csum_base_w:W32.t Array3.t,
                        msg_base_w:W32.t Array67.t) : W32.t Array3.t = {
""",
"""  
  proc __wots_checksum (csum_base_w:W32.t Array3.t,
                        msg_base_w:W32.t Array67.t) : W32.t Array3.t = {
                        
    var t_list : W32.t list;
"""
    )
    text = text.replace("csum_base_w <@ __base_w_3_2 (csum_base_w, csum_bytes_p);",
    """
    t_list <@ BaseWGeneric.__base_w(list_of_array3 csum_base_w, list_of_array2 csum_bytes_p);
    csum_base_w <- array3_of_list t_list;
    """)
    # FIXME: Array3.ofarray and Array2.ofarray doesnt work

    text = text.replace(
"""
  proc __chain_lengths (lengths:W32.t Array67.t, msg:W8.t Array32.t) : 
  W32.t Array67.t = {
""",
"""
  proc __chain_lengths (lengths:W32.t Array67.t, msg:W8.t Array32.t) : 
  W32.t Array67.t = {
    var t_list : W32.t list;
"""
    )

    text = text.replace("lengths <@ __base_w_67_32 (lengths, msg);",
    """
    t_list <@ BaseWGeneric.__base_w(list_of_array67 lengths, list_of_array32 msg);
    lengths <- array67_of_list t_list;
    """)

    # 2) _x_memcpy_u8u8
    # 2.1 _x_memcpy_u8u8_128_32
    text = text.replace(
"""
  proc __prf_keygen (out:W8.t Array32.t, in_0:W8.t Array64.t,
                     key:W8.t Array32.t) : W8.t Array32.t = {
""",
"""
  proc __prf_keygen (out:W8.t Array32.t, in_0:W8.t Array64.t,
                     key:W8.t Array32.t) : W8.t Array32.t = {
    var buf_list : W8.t list;
    var in_0_list : W8.t list;
"""
    )

    text = text.replace(
"""
    (buf,  _0) <@ _x_memcpy_u8u8_128_32 (buf, offset, key);
""",
"""
    (buf_list, _0) <@ Memcpy._x_memcpy_u8u8 (list_of_array128 buf, 128, offset, list_of_array32 key, 32);
    buf <- array128_of_list buf_list;
"""
    )

    # 2.2 _x_memcpy_u8u8_128_64
    text = text.replace(
"""
    (buf,  _1) <@ _x_memcpy_u8u8_128_64 (buf, offset, in_0);
""",
"""
    (buf_list, _1) <@ Memcpy._x_memcpy_u8u8 (list_of_array128 buf, 128, offset, list_of_array64 in_0, 64);
    buf <- array128_of_list buf_list;
"""
    )

    # 2.3 _x_memcpy_u8u8_32_32
    text = text.replace(
"""
  proc __gen_chain_inplace (out:W8.t Array32.t, in_0:W8.t Array32.t,
                            start:W32.t, steps:W32.t,
                            pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {
""",
"""
  proc __gen_chain_inplace (out:W8.t Array32.t, in_0:W8.t Array32.t,
                            start:W32.t, steps:W32.t,
                            pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {
    var out_list : W8.t list;
"""
    )

    text = text.replace(
"""
    (out,  _0) <@ _x_memcpy_u8u8_32_32 (out, offset, in_0);
""",
"""
    (out_list,  _0) <@ Memcpy._x_memcpy_u8u8 (list_of_array32 out, 32, offset, list_of_array32 in_0, 32);
    out <- array32_of_list out_list;
"""
    )

    text = text.replace(
"""
  proc __expand_seed (outseeds:W8.t Array2144.t, inseed:W8.t Array32.t,
                      pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array2144.t * W32.t Array8.t = {
""",
"""
  proc __expand_seed (outseeds:W8.t Array2144.t, inseed:W8.t Array32.t,
                      pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array2144.t * W32.t Array8.t = {
    var aux_list : W8.t list;
"""
    )

    text = text.replace(
"""
    (aux,
    aux_0) <@ _x_memcpy_u8u8_32_32 ((Array32.init (fun i_0 => buf.[0 + i_0])),
    offset, pub_seed);
""",
"""
    (aux_list, aux_0) <@ Memcpy._x_memcpy_u8u8(list_of_array32 (Array32.init (fun i_0 => buf.[0 + i_0])), 32, offset, list_of_array32 pub_seed, 32);
    aux <- array32_of_list aux_list;
"""
    )

    text = text.replace(
"""
  proc __l_tree (leaf:W8.t Array32.t, wots_pk:W8.t Array2144.t,
                 pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : W8.t Array32.t *
                                                                 W8.t Array2144.t *
                                                                 W32.t Array8.t = {
""",
"""
  proc __l_tree (leaf:W8.t Array32.t, wots_pk:W8.t Array2144.t,
                 pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : W8.t Array32.t *
                                                                 W8.t Array2144.t *
                                                                 W32.t Array8.t = {
    var leaf_list : W8.t list;
""" 
    )

    text = text.replace(
"""
    (leaf,  _9) <@ _x_memcpy_u8u8_32_32 (leaf, offset_out,
    (Array32.init (fun i_0 => wots_pk.[0 + i_0])));
""",
"""
    (leaf_list, _9) <@ Memcpy._x_memcpy_u8u8(list_of_array32 leaf, 32, offset_out, list_of_array32 (Array32.init (fun i_0 => wots_pk.[0 + i_0])), 32);
    leaf <- array32_of_list leaf_list;
"""
    )

    return text


########################################################################################################################


def preprocess_ec(ec_in: str, template_functions_dict, debug: bool) -> str:
    ec_out = ec_in.replace("module M", "module Mp")

        # Remove module related to randombytes
    ec_out = ec_out.replace(
"""
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
""",
        ""
    )

    ec_out = remove_functions(ec_out, template_functions_dict, debug)
    ec_out = add_operators(ec_out)
    ec_out = replace_calls(ec_out)

    ec_out = ec_out.replace("(* Erased call to spill *)", "")
    ec_out = ec_out.replace("(* Erased call to unspill *)", "")

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
