require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array4 Array768 Array1152.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyBasemul.
require import NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBasemulAlgebra.
require import NTRUPlus768PolyBasemulInvNTTAlgebra.
require import NTRUPlus768PolyFromBytesAlgebra.
require import NTRUPlus768PolyToBytesProof.
require import NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768PolySubProof.
require import NTRUPlus768PolySubAlgebra.
require import NTRUPlus768PolySubDecapBridge.
require import NTRUPlus768Crepmod3DecapBridge.
require import NTRUPlus768NTTAlgebra.
require import NTRUPlus768NTTStage1Algebra.

import Ring.IntID IntOrder.

op decap_sub_spec
    (ciphertext first_basemul_output : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768PolySubProof.poly_sub_spec ciphertext
    (NTRUPlus768NTTAlgebra.forward_ntt_spec
      (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec
        first_basemul_output)).

op decoded_hinv_spec (hinv : W16.t Array768.t) : W16.t Array768.t =
  NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec
    (NTRUPlus768PolyToBytesProof.poly_tobytes_spec hinv).

op valid_hinv_roundtrip (hinv : W16.t Array768.t) : bool =
  decoded_hinv_spec hinv =
    NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec hinv /\
  NTRUPlus768PolyBasemulAlgebra.in_canonical_range768
    (decoded_hinv_spec hinv) /\
  (forall j, 0 <= j < 768 =>
    coeff (decoded_hinv_spec hinv).[j] %% q = coeff hinv.[j] %% q).

op decap_r2_value_flow
    (ciphertext first_ap first_bp first_basemul_output hinv r2_output :
      W16.t Array768.t) : bool =
  poly_basemul_qring first_ap first_bp first_basemul_output 192 /\
  NTRUPlus768PolySubDecapBridge.decap_m1_poly_sub_value_flow
    ciphertext first_basemul_output
    (decap_sub_spec ciphertext first_basemul_output) /\
  valid_hinv_roundtrip hinv /\
  poly_basemul_qring
    (decap_sub_spec ciphertext first_basemul_output)
    (decoded_hinv_spec hinv)
    r2_output 192.

lemma poly_basemul_qring_output_in_qrange768
    (ap bp rp : W16.t Array768.t) :
  poly_basemul_qring ap bp rp 192 =>
  NTRUPlus768PolyBasemulAlgebra.in_qrange768 rp.
proof.
  move=> Hqring k Hk.
  have Hblock := Hqring k Hk.
  by move: Hblock => [Hrange _].
qed.

lemma in_qrange768_coeff
    (p : W16.t Array768.t) (j : int) :
  NTRUPlus768PolyBasemulAlgebra.in_qrange768 p =>
  0 <= j < 768 =>
  -q <= coeff p.[j] < q.
proof.
  move=> Hp Hj.
  have Hshape :=
    NTRUPlus768PolyBasemulInvNTTAlgebra.in_qrange768_implies_invntt_input_shape
      p Hp.
  exact (Hshape j Hj).
qed.

lemma in_qrange768_poly_tobytes_input_qrange
    (p : W16.t Array768.t) :
  NTRUPlus768PolyBasemulAlgebra.in_qrange768 p =>
  NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange p.
proof.
  move=> Hp j Hj.
  exact (in_qrange768_coeff p j Hp Hj).
qed.

lemma poly_frombytes_specsE (a : W8.t Array1152.t) :
  NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec a =
  NTRUPlus768PolyToBytesAlgebra.poly_frombytes_spec a.
proof.
  rewrite /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec
    /NTRUPlus768PolyToBytesAlgebra.poly_frombytes_spec
    /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_int
    /NTRUPlus768PolyToBytesAlgebra.poly_frombytes_int
    /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_even_int
    /NTRUPlus768PolyToBytesAlgebra.poly_frombytes_even_int
    /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_odd_int
    /NTRUPlus768PolyToBytesAlgebra.poly_frombytes_odd_int.
  done.
qed.

lemma decoded_hinv_specE (hinv : W16.t Array768.t) :
  decoded_hinv_spec hinv =
  NTRUPlus768PolyToBytesAlgebra.poly_frombytes_spec
    (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv).
proof.
  rewrite /decoded_hinv_spec
    NTRUPlus768PolyToBytesAlgebra.poly_tobytes_procedure_specE.
  exact
    (poly_frombytes_specsE
      (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec hinv)).
qed.

lemma poly_sub_spec_in_asymrange768
    (ciphertext forward_output : W16.t Array768.t) :
  NTRUPlus768PolySubAlgebra.decoder_range ciphertext =>
  NTRUPlus768NTTStage1Algebra.input_qrange forward_output =>
  NTRUPlus768PolyBasemulAlgebra.in_asymrange768
    (NTRUPlus768PolySubProof.poly_sub_spec ciphertext forward_output).
proof.
  move=> Hcipher Hforward k Hk.
  rewrite /in_asymrange4 /block4.
  split.
  + rewrite /in_asymrange Array4.initiE 1:/#.
    have Hrange :=
      NTRUPlus768PolySubAlgebra.poly_sub_spec_decoder_forward_range
        ciphertext forward_output (4 * k) Hcipher Hforward _.
    + smt().
    move: Hrange; rewrite /asym_bound_hi /q; smt().
  split.
  + rewrite /in_asymrange Array4.initiE 1:/#.
    have Hrange :=
      NTRUPlus768PolySubAlgebra.poly_sub_spec_decoder_forward_range
        ciphertext forward_output (4 * k + 1) Hcipher Hforward _.
    + smt().
    move: Hrange; rewrite /asym_bound_hi /q; smt().
  split.
  + rewrite /in_asymrange Array4.initiE 1:/#.
    have Hrange :=
      NTRUPlus768PolySubAlgebra.poly_sub_spec_decoder_forward_range
        ciphertext forward_output (4 * k + 2) Hcipher Hforward _.
    + smt().
    move: Hrange; rewrite /asym_bound_hi /q; smt().
  rewrite /in_asymrange Array4.initiE 1:/#.
  have Hrange :=
    NTRUPlus768PolySubAlgebra.poly_sub_spec_decoder_forward_range
      ciphertext forward_output (4 * k + 3) Hcipher Hforward _.
  + smt().
  move: Hrange; rewrite /asym_bound_hi /q; smt().
qed.

lemma valid_hinv_roundtrip_of_qrange
    (hinv : W16.t Array768.t) :
  NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange hinv =>
  valid_hinv_roundtrip hinv.
proof.
  move=> Hhinv.
  have Hhinv_algebra :
      NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange hinv.
  + rewrite -NTRUPlus768PolyToBytesAlgebra.poly_tobytes_procedure_input_qrangeE.
    exact Hhinv.
  rewrite /valid_hinv_roundtrip decoded_hinv_specE.
  split.
  + exact
      (NTRUPlus768PolyToBytesAlgebra.poly_frombytes_poly_tobytes_roundtrip
        hinv Hhinv_algebra).
  split.
  + move=> k Hk.
    rewrite /in_canonical_range4 /block4.
    split.
    - rewrite /in_canonical_range Array4.initiE 1:/#.
      have Hrange :=
        NTRUPlus768PolyToBytesAlgebra.poly_frombytes_poly_tobytes_roundtrip_coeff_range
          hinv (4 * k) Hhinv_algebra _.
      + smt().
      move: Hrange; smt().
    split.
    - rewrite /in_canonical_range Array4.initiE 1:/#.
      have Hrange :=
        NTRUPlus768PolyToBytesAlgebra.poly_frombytes_poly_tobytes_roundtrip_coeff_range
          hinv (4 * k + 1) Hhinv_algebra _.
      + smt().
      move: Hrange; smt().
    split.
    - rewrite /in_canonical_range Array4.initiE 1:/#.
      have Hrange :=
        NTRUPlus768PolyToBytesAlgebra.poly_frombytes_poly_tobytes_roundtrip_coeff_range
          hinv (4 * k + 2) Hhinv_algebra _.
      + smt().
      move: Hrange; smt().
    rewrite /in_canonical_range Array4.initiE 1:/#.
    have Hrange :=
      NTRUPlus768PolyToBytesAlgebra.poly_frombytes_poly_tobytes_roundtrip_coeff_range
        hinv (4 * k + 3) Hhinv_algebra _.
    + smt().
    move: Hrange; smt().
  move=> j Hj.
  exact
    (NTRUPlus768PolyToBytesAlgebra.poly_frombytes_poly_tobytes_roundtrip_coeff_mod_q
      hinv j Hhinv_algebra Hj).
qed.

(* This key-generation value theorem stops at the verified poly_tobytes spec.
   It assumes q-range f/ginv arrays and does not model the surrounding C
   keypair procedure, pointer offsets, or sampler/inversion provenance. *)
lemma keygen_hinv_poly_basemul_roundtrip_provenance
    (rp0 f ginv : W16.t Array768.t) :
  NTRUPlus768PolyBasemulAlgebra.in_qrange768 f =>
  NTRUPlus768PolyBasemulAlgebra.in_qrange768 ginv =>
  phoare [NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\ ap = f /\ bp = ginv ==>
    poly_basemul_qring f ginv res 192 /\ valid_hinv_roundtrip res] = 1%r.
proof.
  move=> Hf Hginv.
  conseq NTRUPlus768PolyBasemulProof.poly_basemul_lossless
    (NTRUPlus768PolyBasemulProof.poly_basemul_functional rp0 f ginv).
  move=> &hr _ result; split.
  + move=> [_ Hword].
    split.
    - trivial.
    exact Hword.
  move=> [_ Hword]; split.
  + have Hqring :=
      NTRUPlus768PolyBasemulAlgebra.poly_basemul_word_to_qring
        f ginv result Hf Hginv Hword.
    split; first exact Hqring.
    apply valid_hinv_roundtrip_of_qrange.
    apply in_qrange768_poly_tobytes_input_qrange.
    exact (poly_basemul_qring_output_in_qrange768 f ginv result Hqring).
  exact Hword.
qed.

lemma valid_hinv_decap_r2_value_flow
    (ciphertext first_ap first_bp first_basemul_output hinv r2_output :
      W16.t Array768.t) :
  NTRUPlus768PolySubAlgebra.decoder_range ciphertext =>
  poly_basemul_qring first_ap first_bp first_basemul_output 192 =>
  NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange hinv =>
  poly_basemul_qring
    (decap_sub_spec ciphertext first_basemul_output)
    (decoded_hinv_spec hinv) r2_output 192 =>
  decap_r2_value_flow ciphertext first_ap first_bp
    first_basemul_output hinv r2_output.
proof.
  move=> Hcipher Hfirst Hhinv Hr2.
  have Hvalid := valid_hinv_roundtrip_of_qrange hinv Hhinv.
  have Hprior :=
    NTRUPlus768PolySubDecapBridge.poly_basemul_qring_decap_m1_poly_sub_value_flow
      ciphertext first_ap first_bp first_basemul_output Hcipher Hfirst.
  rewrite /decap_r2_value_flow.
  split; first exact Hfirst.
  split.
  + rewrite /decap_sub_spec.
    exact Hprior.
  split; first exact Hvalid.
  exact Hr2.
qed.

lemma valid_hinv_decap_r2_poly_basemul_correct
    (ciphertext first_ap first_bp first_basemul_output hinv rp0 :
      W16.t Array768.t) :
  NTRUPlus768PolySubAlgebra.decoder_range ciphertext =>
  poly_basemul_qring first_ap first_bp first_basemul_output 192 =>
  NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange hinv =>
  phoare [NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\
    ap = decap_sub_spec ciphertext first_basemul_output /\
    bp = decoded_hinv_spec hinv ==>
    poly_basemul_qring
      (decap_sub_spec ciphertext first_basemul_output)
      (decoded_hinv_spec hinv) res 192] = 1%r.
proof.
  move=> Hcipher Hfirst Hhinv.
  have Hready :=
    NTRUPlus768PolyBasemulInvNTTAlgebra.poly_basemul_qring_implies_invntt_ready
      first_ap first_bp first_basemul_output Hfirst.
  move: Hready => [_ Hshape].
  have Hforward :
      NTRUPlus768NTTStage1Algebra.input_qrange
        (NTRUPlus768NTTAlgebra.forward_ntt_spec
          (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec
            first_basemul_output)).
  + exact
      (NTRUPlus768PolySubDecapBridge.inverse_invntt_crepmod3_spec_forward_ntt_qrange
        first_basemul_output Hshape).
  have Hsub :
      NTRUPlus768PolyBasemulAlgebra.in_asymrange768
        (decap_sub_spec ciphertext first_basemul_output).
  + rewrite /decap_sub_spec.
    exact
      (poly_sub_spec_in_asymrange768 ciphertext
        (NTRUPlus768NTTAlgebra.forward_ntt_spec
          (NTRUPlus768Crepmod3DecapBridge.inverse_invntt_crepmod3_spec
            first_basemul_output)) Hcipher Hforward).
  have Hvalid := valid_hinv_roundtrip_of_qrange hinv Hhinv.
  have Hcanonical :
      NTRUPlus768PolyBasemulAlgebra.in_canonical_range768
        (decoded_hinv_spec hinv).
  + move: Hvalid => [_ [Hcanonical _]].
    exact Hcanonical.
  exact
    (NTRUPlus768PolyBasemulAlgebra.poly_basemul_correct_qring_asym rp0
      (decap_sub_spec ciphertext first_basemul_output)
      (decoded_hinv_spec hinv) Hsub Hcanonical).
qed.

(* Procedure theorem for the concrete second decapsulation product. *)
lemma poly_frombytes_two_decoder_specs_keygen_hinv_decap_r2_poly_basemul_correct
    (f_bytes ciphertext_bytes : W8.t Array1152.t)
    (first_basemul_output hinv rp0 : W16.t Array768.t) :
  poly_basemul_qring
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f_bytes)
    first_basemul_output 192 =>
  NTRUPlus768PolyBasemulAlgebra.in_qrange768 hinv =>
  phoare [NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\
    ap = decap_sub_spec
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
      first_basemul_output /\
    bp = decoded_hinv_spec hinv ==>
    poly_basemul_qring
      (decap_sub_spec
        (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
        first_basemul_output)
      (decoded_hinv_spec hinv) res 192] = 1%r.
proof.
  move=> Hfirst Hhinv.
  exact
    (valid_hinv_decap_r2_poly_basemul_correct
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f_bytes)
      first_basemul_output hinv rp0
      (NTRUPlus768PolySubDecapBridge.poly_frombytes_spec_decoder_range
        ciphertext_bytes)
      Hfirst (in_qrange768_poly_tobytes_input_qrange hinv Hhinv)).
qed.

(* Terminal array-value theorem for the concrete decapsulation order through
   poly_basemul(&r2,&c,&hinv). The procedure theorem above supplies its final
   q-ring premise; the key-generation provenance theorem supplies the valid
   serialized hinv premise when its f/ginv premises hold. *)
lemma poly_frombytes_two_decoder_specs_keygen_hinv_decap_r2_value_flow
    (f_bytes ciphertext_bytes : W8.t Array1152.t)
    (first_basemul_output hinv r2_output : W16.t Array768.t) :
  poly_basemul_qring
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f_bytes)
    first_basemul_output 192 =>
  NTRUPlus768PolyBasemulAlgebra.in_qrange768 hinv =>
  poly_basemul_qring
    (decap_sub_spec
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
      first_basemul_output)
    (decoded_hinv_spec hinv) r2_output 192 =>
  decap_r2_value_flow
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
    (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f_bytes)
    first_basemul_output hinv r2_output.
proof.
  move=> Hfirst Hhinv Hr2.
  exact
    (valid_hinv_decap_r2_value_flow
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec ciphertext_bytes)
      (NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec f_bytes)
      first_basemul_output hinv r2_output
      (NTRUPlus768PolySubDecapBridge.poly_frombytes_spec_decoder_range
        ciphertext_bytes)
      Hfirst (in_qrange768_poly_tobytes_input_qrange hinv Hhinv) Hr2).
qed.
