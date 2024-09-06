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
