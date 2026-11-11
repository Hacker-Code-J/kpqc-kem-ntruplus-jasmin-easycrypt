require import AllCore List Distr DList.

(* Applying a different deterministic function to each independent block
   preserves the product construction. The input law may be a
   subdistribution; neither losslessness nor uniformity is assumed. *)
lemma independent_blocks_mapi_rec ['a 'b]
    (d:'a distr) (f:int -> 'a -> 'b) n k :
  0 <= n =>
  dmap (dlist d n) (fun xs => mapi_rec f xs k) =
  djoin (map (fun i => dmap d (f i)) (range k (k+n))).
proof.
  move=> hn; elim: n hn k => [k|n hn ih k].
  + by rewrite dlist0 // dmap_dunit /= range_geq // djoin_nil.
  rewrite dlistS //= dmap_comp /(\o) /=.
  rewrite range_ltn 1:/# /= djoin_cons.
  rewrite (_:k+(n+1)=(k+1)+n) 1:/# -(ih (k+1)).
  by rewrite /= -dmap_dprod_comp.
qed.

lemma independent_blocks_mapi ['a 'b]
    (d:'a distr) (f:int -> 'a -> 'b) n :
  0 <= n =>
  dmap (dlist d n) (mapi f) =
  djoin (map (fun i => dmap d (f i)) (range 0 n)).
proof.
  move=> hn.
  exact (independent_blocks_mapi_rec d f n 0 hn).
qed.

(* Any subsequent observable, including a sum of integer noise blocks,
   has the same law. This generic identity contains no failure bound. *)
lemma independent_blocks_observation ['a 'b 'c]
    (d:'a distr) (f:int -> 'a -> 'b) (g:'b list -> 'c) n :
  0 <= n =>
  dmap (dlist d n) (fun xs => g (mapi f xs)) =
  dmap (djoin (map (fun i => dmap d (f i)) (range 0 n))) g.
proof.
  move=> hn; rewrite -(independent_blocks_mapi d f n hn) dmap_comp.
  done.
qed.
