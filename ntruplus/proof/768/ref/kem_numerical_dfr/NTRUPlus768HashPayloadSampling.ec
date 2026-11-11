require import AllCore Distr StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMSOTPMaskLaw.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768PolySOTPEncodeAlgebra.
import RField.

op hash_head (h:W8.t Array224.t) : W8.t Array32.t =
 Array32.init(fun i=>h.[i]).
op hash_split (h:W8.t Array224.t) = (hash_head h,complete_hash_tail h).
op hash_join (p:W8.t Array32.t*W8.t Array192.t) : W8.t Array224.t =
 Array224.init(fun i=>if i<32 then p.`1.[i] else p.`2.[i-32]).

lemma hash_join_head p : hash_head(hash_join p)=p.`1.
proof.
 apply Array32.tP=>i hi.
 rewrite /hash_head Array32.initiE //= .
 rewrite /hash_join Array224.initiE 1:/#; smt().
qed.
lemma hash_join_tail p : complete_hash_tail(hash_join p)=p.`2.
proof.
 apply Array192.tP=>i hi.
 rewrite /complete_hash_tail Array192.initiE //= .
 rewrite /hash_join Array224.initiE 1:/#; smt().
qed.
lemma hash_split_join p : hash_split(hash_join p)=p.
proof. by rewrite /hash_split hash_join_head hash_join_tail; case p. qed.
lemma hash_join_split h : hash_join(hash_split h)=h.
proof.
 apply Array224.tP=>i hi.
 rewrite /hash_join /hash_split /= Array224.initiE //.
 case(i<32)=>hc.
 + by rewrite hc /hash_head Array32.initiE 1:/#.
 rewrite hc /complete_hash_tail Array192.initiE 1:/#; smt().
qed.

lemma uniform224_join_law :
 dmap (uniform32 `*` uniform192) hash_join = uniform224.
proof.
 apply eq_distr=>h.
 rewrite (dmap1E_can _ _ hash_split).
 + exact hash_join_split.
 + move=>p _; exact(hash_split_join p).
 rewrite /hash_split dprod1E uniform32_point uniform192_point uniform224_point.
 by rewrite -exprD_nneg //.
qed.

lemma uniform224_tail_law : dmap uniform224 complete_hash_tail=uniform192.
proof.
 rewrite -uniform224_join_law (dmap_comp hash_join complete_hash_tail (uniform32 `*` uniform192)).
 have he : (complete_hash_tail \o hash_join) =
  (fun p:W8.t Array32.t*W8.t Array192.t => p.`2).
 + apply fun_ext=>p; exact(hash_join_tail p).
 rewrite he (dprod_marginalR uniform32 uniform192 idfun) uniform32_ll dmap_id.
 by rewrite dscalar1.
qed.

(* For arbitrary fixed coins, the two actual payload buffers have product
   uniform192 law. The G pad is independent of the fresh H reply. *)
lemma fresh_payload_buffer_pair_law coins :
 dmap (uniform224 `*` uniform192)
   (fun hp:W8.t Array224.t*W8.t Array192.t =>
     (complete_hash_tail hp.`1,poly_sotp_encode_input coins hp.`2)) =
 (uniform192 `*` uniform192).
proof.
 have h:=dmap_dprod uniform224 uniform192 complete_hash_tail (poly_sotp_encode_input coins).
 rewrite uniform224_tail_law sotp_xor_head_uniform in h.
 apply/eq_sym; exact h.
qed.
