from Jasmin require import JModel.
require import List DList IntDiv Int Ring.
require import Address Hash XMSS_Params  XMSS_Types  XMSS_TreeHash XMSS_PRF  XMSS_MT_Params XMSS_MT_TreeHash XMSS_MT_Types XMSS_MT_PRF.
import IntID.

require import Array8.

abbrev eqsk (sk : xmss_sk, skmt : xmss_mt_sk) : bool = 
    sk.`idx = skmt.`idx /\
    sk.`sk_seed = skmt.`sk_seed /\
    sk.`sk_prf = skmt.`sk_prf /\
    sk.`pub_seed_sk = skmt.`pub_seed_sk /\
    sk.`sk_root = skmt.`sk_root. 

abbrev eqpk (pk : xmss_pk, pkmt : xmss_mt_pk) : bool = 
    pk.`pk_oid = pkmt.`pk_oid /\
    pk.`pk_root = pkmt.`pk_root /\
    pk.`pk_pub_seed = pkmt.`pk_pub_seed. 

abbrev eqkp (kp : xmss_keypair, kpmt : xmss_mt_keypair) : bool = 
    kp.`1.`idx = kpmt.`1.`idx /\
    kp.`1.`sk_seed = kpmt.`1.`sk_seed /\
    kp.`1.`sk_prf = kpmt.`1.`sk_prf /\
    kp.`1.`pub_seed_sk = kpmt.`1.`pub_seed_sk /\
    kp.`1.`sk_root = kpmt.`1.`sk_root /\
    kp.`2.`pk_oid = kpmt.`2.`pk_oid /\
    kp.`2.`pk_root = kpmt.`2.`pk_root /\
    kp.`2.`pk_pub_seed = kpmt.`2.`pk_pub_seed. 


equiv keygen : XMSS_PRF.kg ~ XMSS_MT_PRF.kg : XMSS_Params.impl_oid = XMSS_MT_Params.impl_oid /\ d = 1 ==> eqkp res{1} res{2}. 
proof. 
proc. wp 11 11 => /=. 
call(:d=1);1: by conseq />; sim; auto => /> /#.
wp 9 9 => /=. 
call(:d=1);1: by conseq />; sim. 
by auto => /> /#.
qed.

abbrev eqsig(sig : XMSS_Types.sig_t, sigmt : XMSS_MT_Types.sig_t) : bool =
   sig.`sig_idx = sigmt.`sig_idx /\
   sig.`r = sigmt.`r /\
   sig.`r_sigs = sigmt.`r_sigs.

equiv sign : XMSS_PRF.sign ~ XMSS_MT_PRF.sign : 
    XMSS_Params.impl_oid = XMSS_MT_Params.impl_oid /\  
    d=1 /\ 
    h < 32 /\ 0 < to_uint sk{2}.`idx < 2^h - 1 /\ 
    eqsk arg{1}.`1 arg{2}.`1 /\ arg{1}.`2 = arg{2}.`2 ==> 
     eqsig res{1}.`1 res{2}.`1 /\ eqsk res{1}.`2 res{2}.`2. 
proof. 
proc => /=. 
rcondf {2} 22.
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
     while (#post /\ d = 1 /\ ={pub_seed,sk_seed,t,j,idx} /\ 0 <= j{1} <= h /\
       0 < to_uint idx{1} /\ to_uint idx{2} < 2 ^ h - 1).
     + auto => />;conseq (: ={j,t,address}). smt(). 
     call(:d=1); 1: by conseq />;sim;auto => /> /#.
     by auto => />.
   by auto => />;1: by smt(ge0_h).
by auto => />.

wp;call(:true); 1: by sim.
auto => /> &1 &2 ? -> /= *;split;1:smt(). 
move => *; do split;1: smt(). 
+ rewrite and_mod;1:smt(ge0_h).
  by rewrite modz_small /=; smt(). 
+ rewrite /zero_address /set_tree_addr /set_layer_addr  to_uint_shr /=; 1: by smt(ge0_h). 
  have -> : (to_uint sk{2}.`idx %/ 2 ^ h) = 0 by smt().
  apply tP => i ib.
  rewrite !initiE 1:/# /=.
  rewrite !get_setE 1..3:/#.
  by rewrite initiE 1:/# /=.

+ by smt().

+ rewrite and_mod;1:smt(ge0_h).
  by rewrite modz_small /=; smt(). 

by smt().
qed.

equiv verify : XMSS_PRF.verify ~ XMSS_MT_PRF.verify : 
    d=1 /\ 
    h < 32 /\ 0 < to_uint s{2}.`sig_idx < 2^h - 1 /\ 
    eqpk arg{1}.`1 arg{2}.`1 /\ arg{1}.`2 = arg{2}.`2 /\ eqsig arg{1}.`3 arg{2}.`3 ==> ={res}.
proc.
rcondf {2} 16.
+ move => ?.
  wp;call(:true);1:by trivial.
  by auto => /> /#.
wp;call(: true); 1: by sim.
auto => /> &1 &2 -> /=.
move => *; do split.
+ rewrite W32.and_mod /=;1:smt(ge0_h).
  by rewrite modz_small /=; 1:smt().
+ by smt().
+ by smt().
+ by smt().

+ rewrite to_uint_shr;1:smt(ge0_h).
  rewrite /zero_address /set_tree_addr /set_layer_addr /=.
  have -> : (to_uint s{2}.`sig_idx %/ 2 ^ h) = 0 by smt().
  apply tP => i ib.
  rewrite !initiE 1:/# /=.
  rewrite !get_setE 1..3:/#.
  by rewrite initiE 1:/# /=.

by smt().
qed.
