require import AllCore List Distr DList.

(* Generic tensor identities for lists. There is no CBD or hash idealization
   in this file; the input law is supplied by the caller. *)
lemma cbd_tensor_zip_law ['a 'b] (da:'a distr) (db:'b distr) n :
  0 <= n =>
  dmap (dlist da n `*` dlist db n)
    (fun ab:'a list * 'b list => zip ab.`1 ab.`2) = dlist (da `*` db) n.
proof.
  elim: n => [|n hn ih].
  + by rewrite !dlist0 // dprod_dunit dmap_dunit.
  rewrite !dlistS //= dmap_dprodE.
  have hx := dprod_dmap_cross da (dlist da n) db (dlist db n)
    (fun p:'a * 'a list => p.`1::p.`2)
    (fun p:'b * 'b list => p.`1::p.`2)
    (fun xs ys => zip xs ys)
    idfun (fun p:'a list * 'b list => zip p.`1 p.`2)
    (fun x xs => x::xs) _.
  + by move=> a xs b ys.
  rewrite hx dmap_id ih.
  by rewrite dmap_dprodE.
qed.

op cbd_tensor_halves ['a] (x0:'a) n (xs:'a list) =
  mkseq (fun i => (nth x0 xs i,nth x0 xs (i+n))) n.

lemma cbd_tensor_halves_cat ['a] (x0:'a) n (xs ys:'a list) :
  0 <= n => size xs=n => size ys=n =>
  cbd_tensor_halves x0 n (xs++ys)=zip xs ys.
proof.
  move=> hn hx hy.
  have hz:size(zip xs ys)=n by rewrite size1_zip 1:/# hx.
  rewrite /cbd_tensor_halves -(mkseq_nth (x0,x0) (zip xs ys)) hz.
  apply eq_in_mkseq => i hi.
  rewrite /= nth_zip 1:/# !nth_cat hx ifT 1:/# ifF 1:/#.
  congr; smt().
qed.

lemma cbd_tensor_halves_law ['a] (d:'a distr) (x0:'a) n :
  0 <= n =>
  dmap (dlist d (2*n)) (cbd_tensor_halves x0 n) = dlist (d `*` d) n.
proof.
  move=> hn; rewrite (_:2*n=n+n) 1:/# dlist_add // dmap_comp.
  rewrite -(cbd_tensor_zip_law d d n hn).
  apply eq_dmap_in => ab; rewrite supp_dprod /= => -[ha hb].
  rewrite /=.
  exact (cbd_tensor_halves_cat x0 n ab.`1 ab.`2 hn
    (supp_dlist_size d n _ hn ha) (supp_dlist_size d n _ hn hb)).
qed.

op paired_halves_tensor ['a] (x0:'a) n (perm:int -> int) (ab:'a list * 'a list) =
  mkseq (fun i =>
    ((nth x0 ab.`1 i,nth x0 ab.`1 (i+n)),
     (nth x0 ab.`2 (perm i),nth x0 ab.`2 (perm i+n)))) n.

lemma cbd_tensor_halves_permuted_law ['a] (d:'a distr) (x0:'a) n (perm:int -> int) :
  0 <= n => is_lossless d =>
  (forall i j,0 <= i < n => 0 <= j < n => perm i=perm j => i=j) =>
  (forall i,0 <= i < n => 0 <= perm i < n) =>
  dmap (dlist d (2*n))
    (fun xs => mkseq (fun i => nth (x0,x0) (cbd_tensor_halves x0 n xs) (perm i)) n) =
  dlist (d `*` d) n.
proof.
  move=> hn hd hi hr.
  rewrite -(dmap_comp (cbd_tensor_halves x0 n)
    (fun xs => mkseq (fun i => nth (x0,x0) xs (perm i)) n))
    (cbd_tensor_halves_law d x0 n hn).
  apply (dmap_dlist_partial_perm (x0,x0) (d `*` d) perm n n hn hn) => //.
  by apply dprod_ll.
qed.

lemma cbd_tensor_zip_mkseq ['a 'b] (f:int -> 'a) (g:int -> 'b) n :
  0 <= n =>
  zip (mkseq f n) (mkseq g n)=mkseq (fun i => (f i,g i)) n.
proof.
  move=> hn; apply (eq_from_nth (witness<:'a>,witness<:'b>)).
  + rewrite size_zip !size_mkseq; smt().
  move=> i hi; have hin:0 <= i < n by move:hi; rewrite size_zip !size_mkseq; smt().
  rewrite nth_zip; first by rewrite !size_mkseq.
  by rewrite !nth_mkseq.
qed.

lemma paired_halves_tensor_factor ['a] (x0:'a) n (perm:int -> int) ab :
  0 <= n => (forall i,0 <= i < n => 0 <= perm i < n) =>
  paired_halves_tensor x0 n perm ab =
  zip (cbd_tensor_halves x0 n ab.`1)
    (mkseq (fun i => nth (x0,x0) (cbd_tensor_halves x0 n ab.`2) (perm i)) n).
proof.
  move=> hn hr; rewrite /paired_halves_tensor /cbd_tensor_halves cbd_tensor_zip_mkseq //.
  apply eq_in_mkseq => i hi.
  by rewrite /= (nth_mkseq (x0,x0) _ n (perm i) (hr i hi)).
qed.

(* Each raw list has 2*n independent draws. Halves are paired within a
   list, then the second pair-list is permuted and zipped with the first.
   Losslessness is explicit because the library permutation lemma requires
   it. No finite-support or uniformity premise is needed. *)
lemma paired_halves_tensor_law ['a] (d:'a distr) (x0:'a) n (perm:int -> int) :
  0 <= n => is_lossless d =>
  (forall i j,0 <= i < n => 0 <= j < n => perm i=perm j => i=j) =>
  (forall i,0 <= i < n => 0 <= perm i < n) =>
  dmap (dlist d (2*n) `*` dlist d (2*n)) (paired_halves_tensor x0 n perm) =
  dlist ((d `*` d) `*` (d `*` d)) n.
proof.
  move=> hn hd hi hr.
  rewrite (eq_dmap _ _
    (fun ab:'a list * 'a list => zip (cbd_tensor_halves x0 n ab.`1)
      (mkseq (fun i => nth (x0,x0) (cbd_tensor_halves x0 n ab.`2) (perm i)) n))).
  + by move=> ab; apply paired_halves_tensor_factor.
  rewrite (dmap_dprod_comp (dlist d (2*n)) (dlist d (2*n))
    (cbd_tensor_halves x0 n)
    (fun xs => mkseq (fun i => nth (x0,x0) (cbd_tensor_halves x0 n xs) (perm i)) n)
    (fun xs ys => zip xs ys)) (cbd_tensor_halves_law d x0 n hn)
    (cbd_tensor_halves_permuted_law d x0 n perm hn hd hi hr).
  exact (cbd_tensor_zip_law (d `*` d) (d `*` d) n hn).
qed.
