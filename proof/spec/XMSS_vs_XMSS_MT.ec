pragma Goals : printall.

from Jasmin require import JModel.

require import List DList IntDiv Int Ring.

require import Address Types Hash XMSS_Params LTree  XMSS_Types XMSS_PRF  XMSS_MT_Params XMSS_MT_Types XMSS_MT_PRF.
import IntID.

require import Array8.

equiv treehash_equiv : 
    XMSS_TreeHash.TreeHash.treehash ~  XMSS_MT_TreeHash.TreeHash.treehash :
    XMSS_Params.impl_oid = XMSS_MT_Params.impl_oid /\
    d = 1 /\ ={pub_seed, sk_seed, s, t, address}
    ==> 
    ={res}.
proof.
proc => /=. 
seq 5 5 : (={stack}); 2:auto.
seq 4 4 : (#pre /\ ={stack, heights, offset, i}).
- by auto => /> ? -> /=.
while (#pre).
- seq 2 2 : #pre; 1:auto.
  seq 1 1 : (#pre /\ ={pk}).
    + call (: ={arg} ==> ={res}); [sim | auto].
  seq 2 2 : #pre; 1:auto. 
  seq 1 1 : (#pre /\ ={node}).
    + call (: ={arg} ==> ={res}); [sim | auto].
  seq 4 4 : #pre; 1:auto.
  conseq />; seq 1 1 : (#post); 2:auto.
  while (#pre); 2:auto.
  seq 5 5 : (#pre /\ ={tree_index, node0, node1}); 1:auto.
  seq 1 1 : (#pre /\ ={new_node}); 2:auto.
  call (: ={arg} ==> ={res}); [sim | auto].
- auto.
qed.

equiv keygen : 
  XMSS_PRF.kg ~ XMSS_MT_PRF.kg : 
  XMSS_Params.impl_oid = XMSS_MT_Params.impl_oid /\ d = 1 
  ==> 
  ={res}. 
proof. 
proc. 
wp 7 7 => /=.
seq 6 6 : (#pre /\ ={pub_seed, sk_seed, address, sk_seed, sk_prf, pub_seed}).
- by inline; auto => /> /#.
call (treehash_equiv); auto => /> /#.
qed.

abbrev eqsig(sig : XMSS_Types.sig_t, sigmt : XMSS_MT_Types.sig_t) : bool =
   sig.`sig_idx = sigmt.`sig_idx /\
   sig.`r = sigmt.`r /\
   [sig.`r_sig] = sigmt.`r_sigs.

equiv sign : XMSS_PRF.sign ~ XMSS_MT_PRF.sign : 
    XMSS_Params.impl_oid = XMSS_MT_Params.impl_oid /\  
    d=1 /\ 
    h < 32 /\ 0 < to_uint sk{2}.`idx < 2^h - 1 /\ 
    arg{1}.`1 = arg{2}.`1 /\ arg{1}.`2 = arg{2}.`2 ==> 
     eqsig res{1}.`1 res{2}.`1 /\ res{1}.`2 = res{2}.`2. 
proof. 
proc => /=. 
rcondf {2} 18.
+ move => ?.
  wp;call(:true);1:by trivial.
  wp;call(:true);1:by trivial.
  by auto => /> /#.

wp => /=. 
call(: d=1 /\ ={arg} /\ 0 < to_uint idx{1} /\ to_uint idx{2} < 2 ^ h - 1 ==> ={res}).
+ proc. 
  call(: d=1  /\ ={arg} ==> ={res}).
  + by proc => /=; sim. 
  wp => /=. 
  call(: d=1 /\ ={arg} /\ 0 < to_uint idx{1} /\ to_uint idx{2} < 2 ^ h - 1 ==> ={res}).
  +  proc => /=. 
     while (#post /\ d = 1 /\ ={address,authentication_path, pub_seed,sk_seed,t,j,idx} /\ 0 <= j{1} <= h /\
       0 < to_uint idx{1} /\ to_uint idx{2} < 2 ^ h - 1). 
     + auto => />; conseq (:  ={authentication_path, j,t,address});1:smt().
     call(:d=1); 1: by conseq />;sim;auto => /> /#.
     by auto => />.
   by auto => />; 1: by smt(ge0_h).
by auto => />.

wp;call(:true); 1: by sim.


auto => /> &1 ? -> /= *; do split. 
+ rewrite and_mod;1:smt(ge0_h).
  by rewrite modz_small /=; smt(). 
+ rewrite /zero_address /set_tree_addr /set_layer_addr  to_uint_shr /=; 1: by smt(ge0_h). 
  have -> : (to_uint sk{1}.`idx %/ 2 ^ h) = 0 by smt().
  apply tP => i ib.
  rewrite !initiE 1:/# /=.
  rewrite !get_setE 1..3:/#.
  by rewrite initiE 1:/# /=.

+ rewrite and_mod;1:smt(ge0_h).
  by rewrite modz_small /=; smt().

qed.

equiv verify : XMSS_PRF.verify ~ XMSS_MT_PRF.verify : 
    d=1 /\ 
    h < 32 /\ 0 < to_uint s{2}.`sig_idx < 2^h - 1 /\ 
    arg{1}.`1 = arg{2}.`1 /\ arg{1}.`2 = arg{2}.`2 /\ eqsig arg{1}.`3 arg{2}.`3 ==> ={res}.
proc.
rcondf {2} 16.
+ move => ?.
  wp;call(:true);1:by trivial.
  by auto => /> /#.
wp;call(: true); 1: by sim.
auto => /> &1 &2 -> /=.
move => /> H H0 H1 H2 H3 H4; do split.
+ rewrite W32.and_mod /=;1:smt(ge0_h).
  by rewrite modz_small /=; 1:smt().
+ rewrite -H4 /=;by smt().
+ rewrite -H4 /=;by smt().
+ by smt().

+ rewrite to_uint_shr;1:smt(ge0_h).
  rewrite /zero_address /set_tree_addr /set_layer_addr /=.
  have -> : (to_uint s{2}.`sig_idx %/ 2 ^ h) = 0 by smt().
  apply tP => i ib.
  rewrite !initiE 1:/# /=.
  rewrite !get_setE 1..3:/#.
  by rewrite initiE 1:/# /=.
qed.
