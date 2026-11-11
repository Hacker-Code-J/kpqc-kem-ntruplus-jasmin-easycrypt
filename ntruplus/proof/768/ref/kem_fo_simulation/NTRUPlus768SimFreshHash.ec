require import AllCore Distr StdOrder.
from Jasmin require import JWord.
require import Array192 Array224 Array1152.
require import NTRUPlus768ROMDistributions NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768RRecCodec.
require import NTRUPlus768RRecNativeComparison.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOAlgebra.
require import NTRUPlus768SpreadCache.
import RealOrder.

(* The complete 224-byte H answer is fresh in this leaf law. Its actual
   tail/CBD/NTT/serialization is reused; no statement about an unlogged
   but physically cached H entry, or conditioning on !bad, is made here. *)
lemma sim_fresh_hash_bytes_probability bs :
 mu uniform224(fun hout=>complete_regenerated hout=bs)=
 mu pke_psi1(fun r=>rr_G_input r=bs).
proof.
 rewrite -fo_randomness_law
   (dmapE uniform224 fo_randomness (fun r=>rr_G_input r=bs)).
 apply mu_eq=>hout; by rewrite /(\o) fo_regenerated_input.
qed.

lemma sim_fresh_hash_bytes_bound bs :
 mu uniform224(fun hout=>complete_regenerated hout=bs)<=1%r/(2%r^768).
proof.
 rewrite sim_fresh_hash_bytes_probability.
 exact(spread_g_input_point_bound bs).
qed.

(* The recovered byte string and decode status are fixed before H.
   Dropping the entry/decode guards only enlarges the event, so no valid
   key, successful decode, prepared G, or no-wrap premise is necessary. *)
lemma sim_native_fresh_hash_bound w ct pad :
 mu uniform224(fo_native_accept w ct pad)<=1%r/(2%r^768).
proof.
 apply(ler_trans _ _ _ _ (sim_fresh_hash_bytes_bound (rrec_native_bytes w ct))).
 apply mu_le=>hout hh; rewrite /fo_native_accept.
 move=>[_ [_ he]]; by rewrite /= -he.
qed.
