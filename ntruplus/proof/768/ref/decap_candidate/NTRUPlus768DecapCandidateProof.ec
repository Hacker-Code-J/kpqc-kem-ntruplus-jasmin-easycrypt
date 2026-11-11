require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 NTRUPlus768DecapCandidate.
require import NTRUPlus768PolyBasemul NTRUPlus768PolyBasemulProof.
require import NTRUPlus768InvNTT NTRUPlus768InvNTTProof.
require import NTRUPlus768Crepmod3 NTRUPlus768Crepmod3Proof.
require import NTRUPlus768DecapCandidateSpec.

lemma candidate_product_eq :
  equiv [NTRUPlus768DecapCandidate.M.product__jade_ntruplus_ntruplus768_amd64_ref_poly_basemul ~
    NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    ={rp,ap,bp} ==> ={res}].
proof. by proc; inline *; sim. qed.

lemma candidate_product_functional (rp0 ap0 bp0 : W16.t Array768.t) :
  hoare [NTRUPlus768DecapCandidate.M.product__jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==> is_poly_basemul ap0 bp0 res 192].
proof.
  conseq candidate_product_eq (poly_basemul_functional rp0 ap0 bp0); smt().
qed.

lemma candidate_product_lossless : islossless NTRUPlus768DecapCandidate.M.product__jade_ntruplus_ntruplus768_amd64_ref_poly_basemul.
proof. conseq candidate_product_eq poly_basemul_lossless; smt(). qed.

lemma candidate_inverse_eq :
  equiv [NTRUPlus768DecapCandidate.M.inverse__jade_ntruplus_ntruplus768_amd64_ref_invntt ~
    NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt :
    ={rp,ap} ==> ={res}].
proof. by proc; inline *; sim. qed.

lemma candidate_inverse_functional (rp0 ap0 : W16.t Array768.t) :
  hoare [NTRUPlus768DecapCandidate.M.inverse__jade_ntruplus_ntruplus768_amd64_ref_invntt :
    rp = rp0 /\ ap = ap0 ==> res = invntt_spec ap0].
proof.
  conseq candidate_inverse_eq (invntt_functional rp0 ap0); smt().
qed.

lemma candidate_inverse_lossless : islossless NTRUPlus768DecapCandidate.M.inverse__jade_ntruplus_ntruplus768_amd64_ref_invntt.
proof. conseq candidate_inverse_eq invntt_lossless; smt(). qed.

lemma candidate_ternary_eq :
  equiv [NTRUPlus768DecapCandidate.M.ternary__jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3 ~
    NTRUPlus768Crepmod3.M.jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3 :
    ={rp,ap} ==> ={res}].
proof. by proc; inline *; sim. qed.

lemma candidate_ternary_functional (rp0 ap0 : W16.t Array768.t) :
  hoare [NTRUPlus768DecapCandidate.M.ternary__jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3 :
    rp = rp0 /\ ap = ap0 ==> res = poly_crepmod3_spec ap0].
proof.
  conseq candidate_ternary_eq (poly_crepmod3_functional rp0 ap0); smt().
qed.

lemma candidate_ternary_lossless : islossless NTRUPlus768DecapCandidate.M.ternary__jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3.
proof. conseq candidate_ternary_eq poly_crepmod3_lossless; smt(). qed.

lemma candidate_product_exact (rp0 cp0 fp0 : W16.t Array768.t) :
  hoare [NTRUPlus768DecapCandidate.M.product__jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\ ap = cp0 /\ bp = fp0 ==> res = candidate_product_spec cp0 fp0].
proof.
  conseq (candidate_product_functional rp0 cp0 fp0) => />.
  move=> &hr result hp; exact (candidate_product_unique _ _ result hp).
qed.

lemma decap_candidate_functional (rp0 cp0 fp0 : W16.t Array768.t) :
  hoare [NTRUPlus768DecapCandidate.M.jade_ntruplus_ntruplus768_amd64_ref_decap_candidate :
    rp = rp0 /\ cp = cp0 /\ fp = fp0 ==> res = decap_candidate_spec cp0 fp0].
proof.
  proc.
  call (candidate_ternary_functional rp0 (invntt_spec (candidate_product_spec cp0 fp0))).
  ecall (candidate_inverse_functional inversep (candidate_product_spec cp0 fp0)).
  ecall (candidate_product_exact productp cp0 fp0).
  wp; while (rp = rp0 /\ cp = cp0 /\ fp = fp0); auto => />.
qed.

lemma decap_candidate_lossless : islossless
    NTRUPlus768DecapCandidate.M.jade_ntruplus_ntruplus768_amd64_ref_decap_candidate.
proof.
  proc; call candidate_ternary_lossless; call candidate_inverse_lossless;
    call candidate_product_lossless; wp.
  while (0 <= i <= 768) (768 - i).
  + move=> z; auto => />; smt().
  auto => />; smt().
qed.

lemma decap_candidate_correct (rp0 cp0 fp0 : W16.t Array768.t) :
  phoare [NTRUPlus768DecapCandidate.M.jade_ntruplus_ntruplus768_amd64_ref_decap_candidate :
    rp = rp0 /\ cp = cp0 /\ fp = fp0 ==> res = decap_candidate_spec cp0 fp0] = 1%r.
proof. by conseq decap_candidate_lossless (decap_candidate_functional rp0 cp0 fp0). qed.
