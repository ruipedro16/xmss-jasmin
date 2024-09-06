pragma Goals : printall.

from Jasmin require import JModel.

require import AllCore List Real RealExp IntDiv Distr DList.

require import Array96.
require import WArray96.

lemma dlist_cat1E ['a] (d: 'a distr) (l1 l2 : 'a list):
    mu1 (dlist d (size (l1 ++ l2))) (l1 ++ l2) =
      mu1 (dlist d (size l1)) l1 * mu1 (dlist d (size l2)) l2.
proof.
elim: l1 => /=.
  + by rewrite (dlist0 _ 0) // dunit1E.
move => x xs IH.
rewrite (: 1 + size (xs ++ l2) = size(x::(xs ++ l2))) //.
rewrite dlistS1E IH.
rewrite (: 1 + size xs = size(x::xs)) //.
by rewrite dlistS1E ; ring.
qed.

lemma darray_dlist:
    dmap darray (fun a => Array96.init (get8 a)) = 
      dmap (dlist W8.dword 96) (Array96.of_list W8.zero) .
proof.
rewrite /darray dmap_comp; apply eq_dmap_in.
move => l; rewrite supp_dlist // /(\o) /=; move => [??].
apply Array96.ext_eq => ??.
by rewrite /get8 initiE // get_of_list //= get_of_list.
qed.

abstract theory DListProgramX.

type t.
op d : t distr.

clone import DList.Program 
with type t <- t,
     op d <- d.

module SampleX = {
  proc samplecat(n1 n2: int): t list = {
   var x1, x2;

   x1 <$ dlist d n1;
   x2 <$ dlist d n2;

   return x1 ++ x2;
  }
}.

equiv sample_samplecat : 
    Sample.sample ~ SampleX.samplecat :
    0 <= n1{2} /\ 0 <= n2{2} /\ n{1} = n1{2} + n2{2}
    ==>
    ={res}.
proof.
bypr (res{1}) (res{2}) => /> &1 &2 l Hn1 Hn2 ->.
rewrite pr_Sample.
case: (size l = n1{2} + n2{2}) => El; last first.
  + rewrite dlist1E 1:/# ifF 1:/#.
    byphoare (: n1=n1{2} /\ n2=n2{2} ==> res=l) => />.
    hoare; proc; auto => /> l1.
    rewrite supp_dlist // => [[Hl1] _] l2.
    rewrite supp_dlist // => [[Hl2] _].
    by smt(size_cat).
byphoare (: n1=n1{2} /\ n2=n2{2} ==> res=l) => />.
proc; simplify.
have := cat_take_drop n1{2} l.
pose l1 := take n1{2} l.
pose l2 := drop n1{2} l; move => /eq_sym Hl.
have El1 : size l1 = n1{2} by smt(size_take).
have El2 : size l2 = n2{2} by smt(size_drop).
seq 1: (x1 = l1)
       (mu1 (dlist d n1{2}) l1)
       (mu1 (dlist d n2{2}) l2)
       _ 0%r (#pre) => //.
  + by auto.
  + by rnd (pred1 l1); auto.
  + rnd (pred1 l2); auto => /> x.
    rewrite supp_dlist 1://; move=> [Hx _].
    by smt(catsI).
  + hoare; auto => /> &m H1 x.
    rewrite supp_dlist //; move => [Hx _].
    smt(eqseq_cat size_cat).
move => />.
rewrite Hl (:n1{2}+n2{2}=size (l1++l2)).
  + rewrite size_cat /#.
by rewrite dlist_cat1E /#. 
qed.

end DListProgramX.
