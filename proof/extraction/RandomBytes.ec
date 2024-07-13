
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

