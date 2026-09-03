(* Abstract valid-key decap m1 semantics before crepmod3. *)
require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array4 Array768.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics.
require import NTRUPlus768TerminalRepresentation.
require import NTRUPlus768NTTSchedule.
require import NTRUPlus768EncapPolyBasemulAddAlgebra.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBasemulInvNTTAlgebra.
require import NTRUPlus768InvNTTAlgebra.
require import NTRUPlus768InverseNTTSemantics.

import Ring.IntID IntOrder.

instance ring with poly
  op rzero = NTRUPoly.PolyComRing.zeror
  op rone = NTRUPoly.PolyComRing.oner
  op add = NTRUPoly.PolyComRing.( + )
  op mul = NTRUPoly.PolyComRing.( * )
  op opp = NTRUPoly.PolyComRing.([-])
  op expr = NTRUPoly.PolyComRing.exp
  op ofint = NTRUPoly.PolyComRing.ofint

  proof oner_neq0 by exact NTRUPoly.PolyComRing.oner_neq0
  proof addr0 by exact NTRUPoly.PolyComRing.addr0
  proof addrA by exact NTRUPoly.PolyComRing.addrA
  proof addrC by exact NTRUPoly.PolyComRing.addrC
  proof addrN by exact NTRUPoly.PolyComRing.addrN
  proof mulr1 by exact NTRUPoly.PolyComRing.mulr1
  proof mulrA by exact NTRUPoly.PolyComRing.mulrA
  proof mulrC by exact NTRUPoly.PolyComRing.mulrC
  proof mulrDl by exact NTRUPoly.PolyComRing.mulrDl
  proof expr0 by exact NTRUPoly.PolyComRing.expr0
  proof exprS by exact NTRUPoly.PolyComRing.exprS
  proof ofint0 by exact NTRUPoly.PolyComRing.ofint0
  proof ofint1 by exact NTRUPoly.PolyComRing.ofint1
  proof ofintS by exact NTRUPoly.PolyComRing.ofintS
  proof ofintN by exact NTRUPoly.PolyComRing.ofintN.

lemma lift_int_coeff_addE (x : int) (w : W16.t) :
  lift_int (x + coeff w) = CycloFq.( + ) (lift_int x) (lift_word w).
proof.
  by rewrite /lift_int /lift_word CycloFq.incyclocoeffD.
qed.

lemma block_poly_fq_addE
    (a0 a1 a2 a3 b0 b1 b2 b3 : CycloFq.cyclocoeff) :
  block_poly_fq
    (CycloFq.( + ) a0 b0) (CycloFq.( + ) a1 b1)
    (CycloFq.( + ) a2 b2) (CycloFq.( + ) a3 b3) =
  block_poly_fq a0 a1 a2 a3 + block_poly_fq b0 b1 b2 b3.
proof.
  rewrite /block_poly_fq !NTRUPoly.polyCD.
  have D1 :
      (polyC a1 + polyC b1) * X =
      polyC a1 * X + polyC b1 * X.
  + exact (NTRUPoly.PolyComRing.mulrDl (polyC a1) (polyC b1) X).
  have D2 :
      (polyC a2 + polyC b2) * exp X 2 =
      polyC a2 * exp X 2 + polyC b2 * exp X 2.
  + exact
      (NTRUPoly.PolyComRing.mulrDl
        (polyC a2) (polyC b2) (exp X 2)).
  have D3 :
      (polyC a3 + polyC b3) * exp X 3 =
      polyC a3 * exp X 3 + polyC b3 * exp X 3.
  + exact
      (NTRUPoly.PolyComRing.mulrDl
        (polyC a3) (polyC b3) (exp X 3)).
  have A01 :
      (polyC a0 + polyC b0) +
        (polyC a1 * X + polyC b1 * X) =
      (polyC a0 + polyC a1 * X) +
        (polyC b0 + polyC b1 * X).
  + exact
      (NTRUPoly.PolyComRing.addrACA
        (polyC a0) (polyC b0) (polyC a1 * X) (polyC b1 * X)).
  have A012 :
      ((polyC a0 + polyC a1 * X) +
        (polyC b0 + polyC b1 * X)) +
        (polyC a2 * exp X 2 + polyC b2 * exp X 2) =
      ((polyC a0 + polyC a1 * X) + polyC a2 * exp X 2) +
        ((polyC b0 + polyC b1 * X) + polyC b2 * exp X 2).
  + exact
      (NTRUPoly.PolyComRing.addrACA
        (polyC a0 + polyC a1 * X)
        (polyC b0 + polyC b1 * X)
        (polyC a2 * exp X 2) (polyC b2 * exp X 2)).
  have A0123 :
      (((polyC a0 + polyC a1 * X) + polyC a2 * exp X 2) +
        ((polyC b0 + polyC b1 * X) + polyC b2 * exp X 2)) +
        (polyC a3 * exp X 3 + polyC b3 * exp X 3) =
      (((polyC a0 + polyC a1 * X) + polyC a2 * exp X 2) +
        polyC a3 * exp X 3) +
      (((polyC b0 + polyC b1 * X) + polyC b2 * exp X 2) +
        polyC b3 * exp X 3).
  + exact
      (NTRUPoly.PolyComRing.addrACA
        ((polyC a0 + polyC a1 * X) + polyC a2 * exp X 2)
        ((polyC b0 + polyC b1 * X) + polyC b2 * exp X 2)
        (polyC a3 * exp X 3) (polyC b3 * exp X 3)).
  rewrite D1 D2 D3 A01 A012 A0123.
  done.
qed.

lemma poly_basemul_add_qring_block_eqm4
    (ap bp add output : W16.t Array768.t) (k : int) :
  poly_basemul_add_qring ap bp add output 192 =>
  0 <= k < 192 =>
  eqm4 k
    (block_poly (block4 output k))
    (block_poly (block4 ap k) * block_poly (block4 bp k) +
     block_poly (block4 add k)).
proof.
  move=> Hcontract Hk.
  rewrite /poly_basemul_add_qring in Hcontract.
  have [_ [H0 [H1 [H2 H3]]]] := Hcontract k Hk.
  have E0 :
      lift_word (block4 output k).[0] =
      lift_int
        (coeff0 (block4 ap k) (block4 bp k) (terminal_value k) +
         coeff (block4 add k).[0]).
  + apply lift_int_eq.
    exact H0.
  have E1 :
      lift_word (block4 output k).[1] =
      lift_int
        (coeff1 (block4 ap k) (block4 bp k) (terminal_value k) +
         coeff (block4 add k).[1]).
  + apply lift_int_eq.
    exact H1.
  have E2 :
      lift_word (block4 output k).[2] =
      lift_int
        (coeff2 (block4 ap k) (block4 bp k) (terminal_value k) +
         coeff (block4 add k).[2]).
  + apply lift_int_eq.
    exact H2.
  have E3 :
      lift_word (block4 output k).[3] =
      lift_int
        (coeff3 (block4 ap k) (block4 bp k) (terminal_value k) +
         coeff (block4 add k).[3]).
  + apply lift_int_eq.
    exact H3.
  have Eout :
      block_poly (block4 output k) =
      block_poly_fq
        (lift_int
          (coeff0 (block4 ap k) (block4 bp k) (terminal_value k) +
           coeff (block4 add k).[0]))
        (lift_int
          (coeff1 (block4 ap k) (block4 bp k) (terminal_value k) +
           coeff (block4 add k).[1]))
        (lift_int
          (coeff2 (block4 ap k) (block4 bp k) (terminal_value k) +
           coeff (block4 add k).[2]))
        (lift_int
          (coeff3 (block4 ap k) (block4 bp k) (terminal_value k) +
           coeff (block4 add k).[3])).
  + apply block_poly_eq_of_lifts.
    + exact E0.
    + exact E1.
    + exact E2.
    + exact E3.
  have Ered :
      block_poly_fq
        (lift_int
          (coeff0 (block4 ap k) (block4 bp k) (terminal_value k) +
           coeff (block4 add k).[0]))
        (lift_int
          (coeff1 (block4 ap k) (block4 bp k) (terminal_value k) +
           coeff (block4 add k).[1]))
        (lift_int
          (coeff2 (block4 ap k) (block4 bp k) (terminal_value k) +
           coeff (block4 add k).[2]))
        (lift_int
          (coeff3 (block4 ap k) (block4 bp k) (terminal_value k) +
           coeff (block4 add k).[3])) =
      reduced_block_poly (block4 ap k) (block4 bp k) (terminal_value k) +
      block_poly (block4 add k).
  + rewrite /reduced_block_poly /block_poly !lift_int_coeff_addE.
    exact (block_poly_fq_addE
      (lift_int
        (coeff0 (block4 ap k) (block4 bp k) (terminal_value k)))
      (lift_int
        (coeff1 (block4 ap k) (block4 bp k) (terminal_value k)))
      (lift_int
        (coeff2 (block4 ap k) (block4 bp k) (terminal_value k)))
      (lift_int
        (coeff3 (block4 ap k) (block4 bp k) (terminal_value k)))
      (lift_word (block4 add k).[0])
      (lift_word (block4 add k).[1])
      (lift_word (block4 add k).[2])
      (lift_word (block4 add k).[3])).
  rewrite Eout Ered.
  apply (eqm4_add k
    (reduced_block_poly (block4 ap k) (block4 bp k) (terminal_value k))
    (block_poly (block4 ap k) * block_poly (block4 bp k))
    (block_poly (block4 add k)) (block_poly (block4 add k))).
  + rewrite /eqm4.
    exists (high_block_poly (block4 ap k) (block4 bp k)).
    rewrite /quartic_modulus /terminal_root_field.
    exact
      (reduced_product_factor
        (block4 ap k) (block4 bp k) (terminal_value k)).
  exact (eqm4_refl k (block_poly (block4 add k))).
qed.

lemma poly_basemul_add_qring_represents_product_plus
    (ap bp add output : W16.t Array768.t)
    (P Q M : poly) :
  terminal_represents ap P =>
  terminal_represents bp Q =>
  terminal_represents add M =>
  poly_basemul_add_qring ap bp add output 192 =>
  terminal_represents output (P * Q + M).
proof.
  move=> Hap Hbp Hadd Hcontract.
  rewrite /terminal_represents.
  move=> k Hk.
  have HPQ :
      eqm4 k (P * Q)
        (block_poly (block4 ap k) * block_poly (block4 bp k)).
  + exact
      (eqm4_mul k P (block_poly (block4 ap k)) Q (block_poly (block4 bp k))
        (Hap k Hk) (Hbp k Hk)).
  have Hplus :
      eqm4 k (P * Q + M)
        (block_poly (block4 ap k) * block_poly (block4 bp k) +
         block_poly (block4 add k)).
  + exact
      (eqm4_add k (P * Q)
        (block_poly (block4 ap k) * block_poly (block4 bp k))
        M (block_poly (block4 add k))
        HPQ (Hadd k Hk)).
  have Hout :=
    poly_basemul_add_qring_block_eqm4 ap bp add output k Hcontract Hk.
  exact (eqm4_trans k (P * Q + M)
    (block_poly (block4 ap k) * block_poly (block4 bp k) +
     block_poly (block4 add k))
    (block_poly (block4 output k))
    Hplus (eqm4_sym k (block_poly (block4 output k))
      (block_poly (block4 ap k) * block_poly (block4 bp k) +
       block_poly (block4 add k))
      Hout)).
qed.

lemma terminal_valid_key_decap_product_local
    (h f g r m c product_ntt : W16.t Array768.t)
    (F G R M : poly) :
  terminal_represents f F =>
  terminal_represents g G =>
  terminal_represents r R =>
  terminal_represents m M =>
  poly_basemul_qring h f g 192 =>
  poly_basemul_add_qring h r m c 192 =>
  poly_basemul_qring c f product_ntt 192 =>
  terminal_represents product_ntt (G * R + M * F).
proof.
  move=> Hf Hg Hr Hm Hhf Hcrm Hcf.
  rewrite /terminal_represents.
  move=> k Hk.
  have HGR :
      eqm4 k (G * R)
        (block_poly (block4 g k) * block_poly (block4 r k)).
  + exact
      (eqm4_mul k G (block_poly (block4 g k))
        R (block_poly (block4 r k))
        (Hg k Hk) (Hr k Hk)).
  have HMF :
      eqm4 k (M * F)
        (block_poly (block4 m k) * block_poly (block4 f k)).
  + exact
      (eqm4_mul k M (block_poly (block4 m k))
        F (block_poly (block4 f k))
        (Hm k Hk) (Hf k Hk)).
  have Hrepresented :
      eqm4 k (G * R + M * F)
        (block_poly (block4 g k) * block_poly (block4 r k) +
         block_poly (block4 m k) * block_poly (block4 f k)).
  + exact
      (eqm4_add k (G * R)
        (block_poly (block4 g k) * block_poly (block4 r k))
        (M * F)
        (block_poly (block4 m k) * block_poly (block4 f k))
        HGR HMF).
  have Hgf := poly_basemul_qring_block_eqm4 h f g k Hhf Hk.
  have Hgf_times_r :
      eqm4 k
        (block_poly (block4 g k) * block_poly (block4 r k))
        ((block_poly (block4 h k) * block_poly (block4 f k)) *
         block_poly (block4 r k)).
  + exact
      (eqm4_mul k
        (block_poly (block4 g k))
        (block_poly (block4 h k) * block_poly (block4 f k))
        (block_poly (block4 r k)) (block_poly (block4 r k))
        Hgf (eqm4_refl k (block_poly (block4 r k)))).
  have Hexpanded_add :
      eqm4 k
        (block_poly (block4 g k) * block_poly (block4 r k) +
         block_poly (block4 m k) * block_poly (block4 f k))
        (((block_poly (block4 h k) * block_poly (block4 f k)) *
          block_poly (block4 r k)) +
         block_poly (block4 m k) * block_poly (block4 f k)).
  + exact
      (eqm4_add k
        (block_poly (block4 g k) * block_poly (block4 r k))
        ((block_poly (block4 h k) * block_poly (block4 f k)) *
         block_poly (block4 r k))
        (block_poly (block4 m k) * block_poly (block4 f k))
        (block_poly (block4 m k) * block_poly (block4 f k))
        Hgf_times_r
        (eqm4_refl k
          (block_poly (block4 m k) * block_poly (block4 f k)))).
  have Hexpanded :
      eqm4 k
        (block_poly (block4 g k) * block_poly (block4 r k) +
         block_poly (block4 m k) * block_poly (block4 f k))
        ((block_poly (block4 h k) * block_poly (block4 r k) +
          block_poly (block4 m k)) * block_poly (block4 f k)).
  + have -> :
        ((block_poly (block4 h k) * block_poly (block4 r k) +
          block_poly (block4 m k)) * block_poly (block4 f k)) =
        (((block_poly (block4 h k) * block_poly (block4 f k)) *
          block_poly (block4 r k)) +
         block_poly (block4 m k) * block_poly (block4 f k)) by ring.
    exact Hexpanded_add.
  have Hc :=
    poly_basemul_add_qring_block_eqm4 h r m c k Hcrm Hk.
  have Hc_times_f :
      eqm4 k
        ((block_poly (block4 h k) * block_poly (block4 r k) +
          block_poly (block4 m k)) * block_poly (block4 f k))
        (block_poly (block4 c k) * block_poly (block4 f k)).
  + exact
      (eqm4_mul k
        (block_poly (block4 h k) * block_poly (block4 r k) +
         block_poly (block4 m k))
        (block_poly (block4 c k))
        (block_poly (block4 f k)) (block_poly (block4 f k))
        (eqm4_sym k (block_poly (block4 c k))
          (block_poly (block4 h k) * block_poly (block4 r k) +
           block_poly (block4 m k)) Hc)
        (eqm4_refl k (block_poly (block4 f k)))).
  have Hproduct :=
    poly_basemul_qring_block_eqm4 c f product_ntt k Hcf Hk.
  have Hto_expanded :=
    eqm4_trans k (G * R + M * F)
      (block_poly (block4 g k) * block_poly (block4 r k) +
       block_poly (block4 m k) * block_poly (block4 f k))
      ((block_poly (block4 h k) * block_poly (block4 r k) +
        block_poly (block4 m k)) * block_poly (block4 f k))
      Hrepresented Hexpanded.
  have Hto_product_input :=
    eqm4_trans k (G * R + M * F)
      ((block_poly (block4 h k) * block_poly (block4 r k) +
        block_poly (block4 m k)) * block_poly (block4 f k))
      (block_poly (block4 c k) * block_poly (block4 f k))
      Hto_expanded Hc_times_f.
  exact
    (eqm4_trans k (G * R + M * F)
      (block_poly (block4 c k) * block_poly (block4 f k))
      (block_poly (block4 product_ntt k))
      Hto_product_input
      (eqm4_sym k (block_poly (block4 product_ntt k))
        (block_poly (block4 c k) * block_poly (block4 f k)) Hproduct)).
qed.

lemma terminal_valid_key_decap_product
    (h f g r m c product_ntt : W16.t Array768.t)
    (H F G R M : poly) :
  terminal_represents h H =>
  terminal_represents f F =>
  terminal_represents g G =>
  terminal_represents r R =>
  terminal_represents m M =>
  poly_basemul_qring h f g 192 =>
  poly_basemul_add_qring h r m c 192 =>
  poly_basemul_qring c f product_ntt 192 =>
  terminal_represents product_ntt (G * R + M * F).
proof.
  move=> _ Hf Hg Hr Hm Hhf Hcrm Hcf.
  exact
    (terminal_valid_key_decap_product_local
      h f g r m c product_ntt F G R M
      Hf Hg Hr Hm Hhf Hcrm Hcf).
qed.

op valid_key_decap_m1_semantics
    (G R M F : poly) (output : W16.t Array768.t) : bool =
  NTRUPlus768InverseNTTSemantics.invntt_semantics
    (G * R + M * F) output.

lemma valid_key_decap_m1_local_spec_semantics
    (h f g r m c product_ntt : W16.t Array768.t)
    (F G R M : poly) :
  terminal_represents f F =>
  terminal_represents g G =>
  terminal_represents r R =>
  terminal_represents m M =>
  poly_basemul_qring h f g 192 =>
  poly_basemul_add_qring h r m c 192 =>
  poly_basemul_qring c f product_ntt 192 =>
  valid_key_decap_m1_semantics G R M F
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec product_ntt).
proof.
  move=> Hf Hg Hr Hm Hhf Hcrm Hcf.
  rewrite /valid_key_decap_m1_semantics.
  apply
    (NTRUPlus768InverseNTTSemantics.inverse_invntt_spec_semantics
      (G * R + M * F) product_ntt).
  + exact
      (terminal_valid_key_decap_product_local
        h f g r m c product_ntt F G R M
        Hf Hg Hr Hm Hhf Hcrm Hcf).
  have Hready :=
    NTRUPlus768PolyBasemulInvNTTAlgebra.poly_basemul_qring_implies_invntt_ready
      c f product_ntt Hcf.
  by move: Hready => [_ Hshape].
qed.

lemma valid_key_decap_m1_spec_semantics
    (h f g r m c product_ntt : W16.t Array768.t)
    (H F G R M : poly) :
  terminal_represents h H =>
  terminal_represents f F =>
  terminal_represents g G =>
  terminal_represents r R =>
  terminal_represents m M =>
  poly_basemul_qring h f g 192 =>
  poly_basemul_add_qring h r m c 192 =>
  poly_basemul_qring c f product_ntt 192 =>
  valid_key_decap_m1_semantics G R M F
    (NTRUPlus768InvNTTAlgebra.inverse_invntt_spec product_ntt).
proof.
  move=> _ Hf Hg Hr Hm Hhf Hcrm Hcf.
  exact
    (valid_key_decap_m1_local_spec_semantics
      h f g r m c product_ntt F G R M
      Hf Hg Hr Hm Hhf Hcrm Hcf).
qed.
