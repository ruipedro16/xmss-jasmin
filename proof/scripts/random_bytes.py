#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Removes the randombytes module and module type from the extracted EasyCrypt because all Hops will use it
This prevents having to import the extracted EasyCrypt just to use the module Syscall even when we are not 
working with module M
"""

import sys

ec_filename : str  = sys.argv[1]
randombytes_filename : str = sys.argv[2]

with open (ec_filename, 'r', encoding="utf-8") as f:
    text = f.read()

text = text.replace(
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
text = text.replace(
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

with open (ec_filename, 'w', encoding="utf-8") as f:
    f.write(text)

output_str = """
require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.

require import Array96 WArray96.

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

"""

with open (randombytes_filename, 'w', encoding="utf-8") as f:
    f.write(output_str)