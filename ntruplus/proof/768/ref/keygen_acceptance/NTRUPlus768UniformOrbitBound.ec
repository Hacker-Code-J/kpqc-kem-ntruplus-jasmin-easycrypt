require import AllCore Distr StdOrder.
from Jasmin require import JWord.
require import Array192 NTRUPlus768ROMDistributions.
import RealOrder RField.

op uniform192_xor (mask buf:W8.t Array192.t) : W8.t Array192.t =
 Array192.init (fun i=>buf.[i] +^ mask.[i]).

lemma uniform192_xor_get mask buf i :
 0<=i<192 => (uniform192_xor mask buf).[i]=buf.[i] +^ mask.[i].
proof. by move=>hi; rewrite /uniform192_xor Array192.initiE. qed.

lemma uniform192_xor_involution mask buf :
 uniform192_xor mask (uniform192_xor mask buf)=buf.
proof.
 apply Array192.tP=>i hi.
 rewrite !uniform192_xor_get 1,2:hi.
 by rewrite -W8.xorwA W8.xorwK W8.xorw0.
qed.
lemma uniform192_xor_uniform mask :
 dmap uniform192 (uniform192_xor mask)=uniform192.
proof.
 apply eq_distr=>buf.
 rewrite (dmap1E_can _ _ (uniform192_xor mask)).
 + exact (uniform192_xor_involution mask).
 + move=>x _; exact (uniform192_xor_involution mask x).
 by rewrite !uniform192_point.
qed.
lemma uniform192_xor_event mask (event:W8.t Array192.t -> bool) :
 mu uniform192 (fun buf=>event(uniform192_xor mask buf))=mu uniform192 event.
proof.
 have h:=congr1 (fun d=>mu d event) _ _ (uniform192_xor_uniform mask).
 by rewrite /= dmapE /(\o) in h.
qed.

op indexed_event_union ['a] (n:int) (events:int -> 'a -> bool) (x:'a) =
 exists i, 0<=i<n /\ events i x.

lemma indexed_event_union_zero ['a] (events:int -> 'a -> bool) :
 indexed_event_union 0 events=pred0.
proof. apply fun_ext=>x; rewrite /indexed_event_union /pred0; smt(). qed.
lemma indexed_event_union_succ ['a] n (events:int -> 'a -> bool) :
 0<=n => indexed_event_union (n+1) events=
 predU (indexed_event_union n events) (events n).
proof. move=>hn; apply fun_ext=>x; rewrite /indexed_event_union /predU; smt(). qed.

(* This finite union calculation applies to subdistributions as well. *)
lemma disjoint_indexed_event_mass ['a] (d:'a distr) (events:int -> 'a -> bool) n p :
 0<=n =>
 (forall i, 0<=i<n => mu d (events i)=p) =>
 (forall i j x, 0<=i<n => 0<=j<n => events i x => events j x => i=j) =>
 mu d (indexed_event_union n events)=n%r*p.
proof.
 elim: n => [|n hn ih] hm hd.
 + by rewrite indexed_event_union_zero mu0 /=.
 rewrite indexed_event_union_succ 1:hn.
 rewrite mu_disjointL.
 + move=>x [i [hi hix]]; apply/negP=>hnx.
   have hij:=hd i n x _ _ hix hnx; smt().
 rewrite (ih _ _) 1,2:/# (hm n _) 1:/#.
 by rewrite fromintD /=; ring.
qed.

lemma disjoint_equal_event_bound ['a] (d:'a distr) (events:int -> 'a -> bool) n p :
 0<n =>
 (forall i, 0<=i<n => mu d (events i)=p) =>
 (forall i j x, 0<=i<n => 0<=j<n => events i x => events j x => i=j) =>
 p<=1%r/n%r.
proof.
 move=>hn hm hd.
 have hmass:=disjoint_indexed_event_mass d events n p _ hm hd; first smt().
 have hb:=mu_bounded d (indexed_event_union n events).
 have hreal:0%r<n%r by rewrite lt_fromint.
 rewrite (ler_pdivl_mulr n%r p 1%r hreal).
 rewrite mulrC; smt().
qed.

lemma finite_uniform_orbit_bound n (transforms:int -> W8.t Array192.t -> W8.t Array192.t)
 (bad:W8.t Array192.t -> bool) :
 0<n =>
 (forall i, 0<=i<n => dmap uniform192 (transforms i)=uniform192) =>
 (forall i j buf, 0<=i<n => 0<=j<n =>
  bad(transforms i buf) => bad(transforms j buf) => i=j) =>
 mu uniform192 bad<=1%r/n%r.
proof.
 move=>hn hp hd.
 apply(disjoint_equal_event_bound uniform192 (fun i buf=>bad(transforms i buf)) n
   (mu uniform192 bad) hn _ hd).
 move=>i hi.
 have he:=congr1 (fun d=>mu d bad) _ _ (hp i hi).
 by rewrite /= dmapE /(\o) in he.
qed.

lemma xor_disjoint_event_bound n (masks:int -> W8.t Array192.t)
 (bad:W8.t Array192.t -> bool) :
 0<n =>
 (forall i j buf, 0<=i<n => 0<=j<n =>
  bad(uniform192_xor (masks i) buf) => bad(uniform192_xor (masks j) buf) => i=j) =>
 mu uniform192 bad<=1%r/n%r.
proof.
 move=>hn hd.
 apply(finite_uniform_orbit_bound n (fun i=>uniform192_xor (masks i)) bad hn _ hd).
 by move=>i hi; apply uniform192_xor_uniform.
qed.

lemma xor1024_disjoint_event_bound (masks:int -> W8.t Array192.t)
 (bad:W8.t Array192.t -> bool) :
 (forall i j buf, 0<=i<1024 => 0<=j<1024 =>
  bad(uniform192_xor (masks i) buf) => bad(uniform192_xor (masks j) buf) => i=j) =>
 mu uniform192 bad<=1%r/1024%r.
proof. move=>hd; exact (xor_disjoint_event_bound 1024 masks bad _ hd). qed.

lemma indexed_event_union_bound ['a] (d:'a distr) (events:int -> 'a -> bool) n b :
 0<=n =>
 (forall i, 0<=i<n => mu d (events i)<=b) =>
 mu d (indexed_event_union n events)<=n%r*b.
proof.
 elim: n => [|n hn ih] hm.
 + by rewrite indexed_event_union_zero mu0 /=.
 rewrite indexed_event_union_succ 1:hn mu_or.
 have hb:=ih _; first smt().
 have hl:=hm n _; first smt().
 have hz:=mu_bounded d (predI (indexed_event_union n events) (events n)).
 rewrite fromintD /= mulrDl mul1r; smt().
qed.

(* The premise below must be supplied by the actual determinant failure
   bridge.  This generic aggregation does not assume a numerical acceptance
   bound or independence between the different block-failure events. *)
lemma uniform192_acceptance_from_384_bad
 (accept:W8.t Array192.t -> bool) (bad:int -> W8.t Array192.t -> bool) :
 (forall i, 0<=i<384 => mu uniform192 (bad i)<=1%r/1024%r) =>
 (forall buf, !accept buf => indexed_event_union 384 bad buf) =>
 5%r/8%r<=mu uniform192 accept.
proof.
 move=>hbad hcover.
 have hu:=indexed_event_union_bound uniform192 bad 384 (1%r/1024%r) _ hbad;
   first trivial.
 have hm:mu uniform192 (predC accept)<=mu uniform192 (indexed_event_union 384 bad).
 + apply mu_sub=>buf; exact (hcover buf).
 have hn:=mu_not uniform192 accept.
 have hl:=uniform192_ll.
 smt().
qed.
