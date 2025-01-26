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

pred eq_auth_path (a : XMSS_Types.AuthPath.auth_path) (a_mt : auth_path)  = 
    val a_mt = val a.

equiv root_from_sig_equiv : 
    XMSS_TreeHash.RootFromSig.rootFromSig ~ XMSS_MT_TreeHash.RootFromSig.rootFromSig :
    ={idx_sig, sig_ots, M, _seed, address} /\
    eq_auth_path auth{1} auth{2} /\
    d = 1
    ==> 
    ={res}.
proof.
proc => /=.
seq 2 2 : #pre; 1:auto.
seq 1 1 : (#pre /\ ={pk_ots}); first by call (: ={arg} ==> ={res}); [sim | auto].
seq 2 2 : #pre; 1:auto.
seq 1 1 : (#pre /\ ={nodes0}); first by call (: ={arg} ==> ={res}); [sim | auto].
seq 3 3 : (#pre /\ ={k}); 1:auto.
(while (#pre); auto) => [| /#].
seq 1 1 : #pre; 1:auto.
(if; first by auto); (call (: ={arg} ==> ={res}); 1: by sim); auto => /> /#. 
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

pred eq_r_sigs (x : wots_signature * XMSS_Types.AuthPath.auth_path)
               (y : (wots_signature * auth_path) list) = 
               size y = 1 /\ 
               x.`1 = (nth witness y 0).`1 /\ 
               eq_auth_path x.`2 (nth witness y 0).`2.

pred eqsig(sig : XMSS_Types.sig_t, sigmt : XMSS_MT_Types.sig_t) =
  sig.`sig_idx = sigmt.`sig_idx /\
  sig.`r = sigmt.`r /\  
  eq_r_sigs (sig.`r_sig) (sigmt.`r_sigs).


equiv sign : XMSS_PRF.sign ~ XMSS_MT_PRF.sign : 
    XMSS_Params.impl_oid = XMSS_MT_Params.impl_oid /\  
    d=1 /\ 
    h < 32 /\ 0 < to_uint sk{2}.`idx < 2^h - 1 /\ 
    arg{1}.`1 = arg{2}.`1 /\ 
    arg{1}.`2 = arg{2}.`2 
    ==> 
    eqsig res{1}.`1 res{2}.`1 /\ res{1}.`2 = res{2}.`2. 
proof. 
proc => /=. 
rcondf {2} 18.
+ move => ?.
  wp;call(:true);1:by trivial.
  wp;call(:true);1:by trivial.
  by auto => /> /#.
wp. conseq />.
call(: 
  XMSS_Params.impl_oid = XMSS_MT_Params.impl_oid /\ 
  d = 1 /\ ={arg} /\ 0 < to_uint idx{1} /\ to_uint idx{2} < 2 ^ h - 1 
  ==> 
  eq_auth_path res{1}.`2 res{2}.`2 /\ res{1}.`1 = res{2}.`1
).
+ proc => /=.
  call (: XMSS_Params.impl_oid = XMSS_MT_Params.impl_oid /\  ={arg} ==> ={res}); 1:sim.
  wp; conseq />.
  inline {1} 3; inline {2} 3.
  wp. 
  seq 9 9 : (
    #pre /\ 
    ={sk_seed, pub_seed, pub_seed0, sk_seed0, idx0, address0, j, t, authentication_path} /\
    size authentication_path{1} = h /\ 
    size authentication_path{2} =  h %/ d
  ); first by auto => /> &2 ?-> /= ??; rewrite !size_nseq; smt(ge0_h).
  while (#pre); auto => />.
     - call (treehash_equiv); auto => /> *; split => //; rewrite ?size_put /#. 
     - move => &2 d_val *; split => [/# |]. 
       by move => authpathR ?????; rewrite /eq_auth_path !insubdK // /P.
wp ; call(: true); 1: by sim.
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
    d = 1 /\ 
    h < 32 /\ 0 < to_uint s{2}.`sig_idx < 2^h - 1 /\ 
    arg{1}.`1 = arg{2}.`1 /\ arg{1}.`2 = arg{2}.`2 /\ eqsig arg{1}.`3 arg{2}.`3 
    ==> 
    ={res}.
proc => /=.
rcondf {2} 16.
+ move => ?.
  wp;call(:true);1:by trivial.
  by auto => /> /#.
wp => /=. 
call root_from_sig_equiv.
conseq />; 1:smt().
wp.
auto => /> &1 &2 -> /= *; do split. 
+ rewrite and_mod;1:smt(ge0_h).
  by rewrite modz_small /=; smt(). 
+ do congr. rewrite /zero_address /set_tree_addr /set_layer_addr to_uint_shr /=; 1: by smt(ge0_h). 
  apply tP => i ib.
  rewrite !initiE 1:/# /=.
  rewrite !get_setE 1..3:/#.
  rewrite (: (to_uint s{2}.`sig_idx %/ 2 ^ h) = 0) 1:/# /=. 
  case (i = 1) => //?; case (i = 2) => //?; case (i = 0) => //?.
  by rewrite initiE /=.
qed.
