from Jasmin require import JModel.
require import XMSS_PRF XMSS_MT_PRF IntDiv XMSS_Params XMSS_MT_Params Int Ring XMSS_Address  XMSS_MT_Address Array8.
import IntID.

equiv keygen : XMSS_PRF.kg ~ XMSS_MT_PRF.kg : d = 1 ==> ={res}. 
proof. 
proc; inline *; sim.
by auto => /> /#. 
qed.

equiv sign : XMSS_PRF.sign ~ XMSS_MT_PRF.sign : d=1 /\ h < 32 /\ 0 < to_uint sk{2}.`Types.idx < 2^h - 1 /\ ={arg} ==> ={res}. 
proof. 
proc. 
rcondf {2} 24.
+ move => ?.
  wp;call(:true);1:by trivial.
  wp;call(:true);1:by trivial.
  by auto => /> /#.
wp;call(: true); 1: by sim.
wp;call(: true); 1: by sim.
auto => /> &2 => ->; rewrite !divz1 /=.
move => *; do split.
+ rewrite W32.and_mod /=;1:smt(ge0_h).
  by rewrite modz_small /=; 1:smt().

rewrite to_uint_shr;1:smt(ge0_h).
rewrite /zero_address /set_tree_addr /set_layer_addr /=.
have -> : (to_uint sk{2}.`Types.idx %/ 2 ^ h) = 0 by smt().
apply tP => i ib.
rewrite !initiE 1:/# /=.
rewrite !get_setE 1..3:/#.
by rewrite initiE 1:/# /=.

qed.

equiv verify : XMSS_PRF.verify ~ XMSS_MT_PRF.verify : d=1 /\ h < 32 /\ 0 < to_uint s{2}.`Types.sig_idx < 2^h - 1 /\ ={arg} ==> ={res}. 
proof. 
proc. 
rcondf {2} 16.
+ move => ?.
  wp;call(:true);1:by trivial.
  by auto => /> /#.
wp;call(: true); 1: by sim.
auto => /> &2 => ->; rewrite !divz1 /=.
move => *; do split.
+ rewrite W32.and_mod /=;1:smt(ge0_h).
  by rewrite modz_small /=; 1:smt().

rewrite to_uint_shr;1:smt(ge0_h).
rewrite /zero_address /set_tree_addr /set_layer_addr /=.
have -> : (to_uint s{2}.`Types.sig_idx %/ 2 ^ h) = 0 by smt().
apply tP => i ib.
rewrite !initiE 1:/# /=.
rewrite !get_setE 1..3:/#.
by rewrite initiE 1:/# /=.
qed.
