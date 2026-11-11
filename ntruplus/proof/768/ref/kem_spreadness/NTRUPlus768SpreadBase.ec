require import AllCore Distr StdOrder.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel NTRUPlus768PKEAlgebra.
require import NTRUPlus768PKEKeyDistribution NTRUPlus768ACWC2Domains.
require import NTRUPlus768RRecModel NTRUPlus768RRecAlgebra.
import RealOrder.

(* Injectivity is restricted to the ternary randomness domain and actual
   valid keys. Public-key canonicity alone would not imply this property. *)
lemma spread_some_injective ['a] (x y:'a) : Some x=Some y=>x=y.
proof. by smt(). qed.

lemma spread_base_recover w m r ct :
 pke_key_relation w=>pke_domain m=>pke_domain r=>
 pke_enc_spec w.`kg_pk m r=Some ct=>rrec_spec w.`kg_pk m ct=Some r.
proof.
 move=>hk hm hr he.
 have hp:=pke_key_canonical w hk.
 have hf:=rrec_keyed_forward w m r hk hm hr.
 move:he; rewrite /pke_enc_spec hp /= =>he.
 by rewrite -he.
qed.

lemma spread_base_fiber_unique w m ct r1 r2 :
 pke_key_relation w=>pke_domain m=>pke_domain r1=>pke_domain r2=>
 pke_enc_spec w.`kg_pk m r1=Some ct=>pke_enc_spec w.`kg_pk m r2=Some ct=>r1=r2.
proof.
 move=>hk hm h1 h2 e1 e2.
 have f1:=spread_base_recover w m r1 ct hk hm h1 e1.
 have f2:=spread_base_recover w m r2 ct hk hm h2 e2.
 apply(spread_some_injective r1 r2); by rewrite -f1 -f2.
qed.

lemma spread_base_fiber_singleton w m ct :
 pke_key_relation w=>pke_domain m=>
 mu pke_psi1 (fun r=>pke_enc_spec w.`kg_pk m r=Some ct)<=
 mu1 pke_psi1 (oget(rrec_spec w.`kg_pk m ct)).
proof.
 move=>hk hm; apply mu_le=>r hs he.
 have hr:pke_domain r by move:hs; rewrite acwc2_psi1_support.
 have hf:=spread_base_recover w m r ct hk hm hr he.
 by rewrite /pred1 hf.
qed.

(* Every attainable ciphertext has precisely the atom mass of its unique
   randomness. No decryption-correctness or coefficient no-wrap premise
   occurs: RRec is the unconditional randomness-recovery contract. *)
lemma spread_base_ciphertext_mass w m r0 :
 pke_key_relation w=>pke_domain m=>pke_domain r0=>
 mu pke_psi1 (fun r=>pke_enc_spec w.`kg_pk m r=Some(pke_ciphertext w.`kg_pk m r0))=
 mu1 pke_psi1 r0.
proof.
 move=>hk hm hr0.
 have he0:pke_enc_spec w.`kg_pk m r0=Some(pke_ciphertext w.`kg_pk m r0).
 + by rewrite /pke_enc_spec (pke_key_canonical w hk).
 apply mu_eq_support=>r hs; rewrite /pred1.
 have hr:pke_domain r by move:hs; rewrite acwc2_psi1_support.
 apply eq_iff_imp; split.
 + move=>he; exact(spread_base_fiber_unique w m (pke_ciphertext w.`kg_pk m r0) r r0 hk hm hr hr0 he he0).
 by move=>->.
qed.

require import NTRUPlus768SpreadCBD.

lemma spread_base_bound w m ct :
 pke_key_relation w=>pke_domain m=>
 mu pke_psi1 (fun r=>pke_enc_spec w.`kg_pk m r=Some ct)<=1%r/(2%r^768).
proof.
 move=>hk hm.
 exact(ler_trans _ _ _ (spread_base_fiber_singleton w m ct hk hm)
   (spread_cbd_point_bound (oget(rrec_spec w.`kg_pk m ct)))).
qed.

(* The zero-randomness ciphertext attains the upper bound for every valid
   key and every fixed ternary message. *)
lemma spread_base_zero_tight w m :
 pke_key_relation w=>pke_domain m=>
 mu pke_psi1 (fun r=>pke_enc_spec w.`kg_pk m r=
   Some(pke_ciphertext w.`kg_pk m spread_cbd_zero))=1%r/(2%r^768).
proof.
 move=>hk hm.
 rewrite(spread_base_ciphertext_mass w m spread_cbd_zero hk hm spread_cbd_zero_domain).
 exact spread_cbd_zero_point.
qed.
