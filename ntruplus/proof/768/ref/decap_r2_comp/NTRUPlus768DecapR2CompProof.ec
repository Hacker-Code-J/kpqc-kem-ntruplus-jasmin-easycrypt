require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 NTRUPlus768DecapR2Comp.
require import NTRUPlus768NTT NTRUPlus768NTTProof.
require import NTRUPlus768PolySub NTRUPlus768PolySubProof.
require import NTRUPlus768PolyBasemul NTRUPlus768PolyBasemulProof.
require import NTRUPlus768DecapCandidateSpec NTRUPlus768DecapR2CompSpec.

lemma r2_forward_eq :
  equiv [NTRUPlus768DecapR2Comp.M.forward__jade_ntruplus_ntruplus768_amd64_ref_ntt ~
    NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt :
    ={rp,ap} ==> ={res}].
proof. by proc; inline *; sim. qed.

lemma r2_forward_functional (rp0 ap0 : W16.t Array768.t) :
  hoare [NTRUPlus768DecapR2Comp.M.forward__jade_ntruplus_ntruplus768_amd64_ref_ntt :
    rp = rp0 /\ ap = ap0 ==> res = ntt_spec ap0].
proof. conseq r2_forward_eq (ntt_functional rp0 ap0); smt(). qed.

lemma r2_forward_lossless : islossless NTRUPlus768DecapR2Comp.M.forward__jade_ntruplus_ntruplus768_amd64_ref_ntt.
proof. conseq r2_forward_eq ntt_lossless; smt(). qed.

lemma r2_difference_eq :
  equiv [NTRUPlus768DecapR2Comp.M.difference__jade_ntruplus_ntruplus768_amd64_ref_poly_sub ~
    NTRUPlus768PolySub.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sub :
    ={rp,ap,bp} ==> ={res}].
proof. by proc; inline *; sim. qed.

lemma r2_difference_functional (rp0 ap0 bp0 : W16.t Array768.t) :
  hoare [NTRUPlus768DecapR2Comp.M.difference__jade_ntruplus_ntruplus768_amd64_ref_poly_sub :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==> res = poly_sub_spec ap0 bp0].
proof. conseq r2_difference_eq (poly_sub_functional rp0 ap0 bp0); smt(). qed.

lemma r2_difference_lossless : islossless NTRUPlus768DecapR2Comp.M.difference__jade_ntruplus_ntruplus768_amd64_ref_poly_sub.
proof. conseq r2_difference_eq poly_sub_lossless; smt(). qed.

lemma r2_product_eq :
  equiv [NTRUPlus768DecapR2Comp.M.product__jade_ntruplus_ntruplus768_amd64_ref_poly_basemul ~
    NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    ={rp,ap,bp} ==> ={res}].
proof. by proc; inline *; sim. qed.

lemma r2_product_functional (rp0 ap0 bp0 : W16.t Array768.t) :
  hoare [NTRUPlus768DecapR2Comp.M.product__jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==> is_poly_basemul ap0 bp0 res 192].
proof. conseq r2_product_eq (poly_basemul_functional rp0 ap0 bp0); smt(). qed.

lemma r2_product_lossless : islossless NTRUPlus768DecapR2Comp.M.product__jade_ntruplus_ntruplus768_amd64_ref_poly_basemul.
proof. conseq r2_product_eq poly_basemul_lossless; smt(). qed.

lemma r2_product_exact (rp0 ap0 bp0 : W16.t Array768.t) :
  hoare [NTRUPlus768DecapR2Comp.M.product__jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==> res = candidate_product_spec ap0 bp0].
proof.
  conseq (r2_product_functional rp0 ap0 bp0) => />.
  move=> &hr result hp; exact (candidate_product_unique _ _ result hp).
qed.

lemma decap_r2_functional (rp0 cp0 mp0 hp0 : W16.t Array768.t) :
  hoare [NTRUPlus768DecapR2Comp.M.jade_ntruplus_ntruplus768_amd64_ref_decap_r2 :
    rp = rp0 /\ cp = cp0 /\ mp = mp0 /\ hp = hp0 ==>
    res = decap_r2_spec cp0 mp0 hp0].
proof.
  proc.
  call (r2_product_exact rp0 (r2_difference_spec cp0 mp0) hp0).
  ecall (r2_difference_functional differencep cp0 (ntt_spec mp0)).
  ecall (r2_forward_functional transformedp mp0).
  wp; while (rp = rp0 /\ cp = cp0 /\ mp = mp0 /\ hp = hp0); auto => />.
qed.

lemma decap_r2_lossless : islossless
    NTRUPlus768DecapR2Comp.M.jade_ntruplus_ntruplus768_amd64_ref_decap_r2.
proof.
  proc; call r2_product_lossless; call r2_difference_lossless;
    call r2_forward_lossless; wp.
  while (0 <= i <= 768) (768 - i).
  + move=> z; auto => />; smt().
  auto => />; smt().
qed.

lemma decap_r2_correct (rp0 cp0 mp0 hp0 : W16.t Array768.t) :
  phoare [NTRUPlus768DecapR2Comp.M.jade_ntruplus_ntruplus768_amd64_ref_decap_r2 :
    rp = rp0 /\ cp = cp0 /\ mp = mp0 /\ hp = hp0 ==>
    res = decap_r2_spec cp0 mp0 hp0] = 1%r.
proof. by conseq decap_r2_lossless (decap_r2_functional rp0 cp0 mp0 hp0). qed.
