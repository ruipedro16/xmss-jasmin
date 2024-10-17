#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# import the appropriate core hash file and parameter files

import sys

impl_str: str = sys.argv[1]

assert impl_str is not None

hash_dict = {
    "xmss-sha2_10_256": "core_hash/core_hash_sha256.jtmpl",
    "xmss-sha2_10_192": "core_hash/core_hash_sha256.jtmpl",
    "xmssmt-sha2_20_2_256": "core_hash/core_hash_sha256.jtmpl",
    "xmssmt-sha2_20_4_256": "core_hash/core_hash_sha256.jtmpl",
}

try:
    file = hash_dict[impl_str]
except KeyError:
    raise NotImplementedError(f"core_hash is not implemented for" + impl_str)

print(f'from XMSS require "params/params-{impl_str}.jinc"')
print(f'from XMSS require "{file}"')
