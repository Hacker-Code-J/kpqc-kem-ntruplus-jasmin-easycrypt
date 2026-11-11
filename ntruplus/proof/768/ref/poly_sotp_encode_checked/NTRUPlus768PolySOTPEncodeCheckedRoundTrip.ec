require import AllCore Distr.
from Jasmin require import JWord JModel_x86.
require import Array96 Array192 Array768.
require import NTRUPlus768PolySOTPEncodeCheckedProof.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768PolySOTPRoundTrip.
require import NTRUPlus768PolySOTPDecodeAlgebra NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768PolySOTPDecodeCheckedProof NTRUPlus768PolySOTPDecodeCheckedLossless.

(* Composition of the two actual extracted procedures.  This theorem is
   local to SOTP with the same pad; it does not assert that Decaps recovers
   that pad from a KEM ciphertext. *)

lemma poly_sotp_encode_spec_trit_input msg pad :
  poly_sotp_trit_input (poly_sotp_encode_spec msg pad).
proof.
  rewrite /poly_sotp_encode_spec.
  exact (poly_cbd1_spec_sotp_trit_input (poly_sotp_encode_input msg pad)).
qed.

lemma poly_sotp_decode_encoded_correct out0 msg0 pad0 :
  phoare [NTRUPlus768PolySOTPDecodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode :
    msg = out0 /\ ap = poly_sotp_encode_spec msg0 pad0 /\ buf = pad0 ==>
    res = (msg0, W32.zero)] = 1%r.
proof.
  have ht := poly_sotp_encode_spec_trit_input msg0 pad0.
  have hm := poly_sotp_encode_decode_msg msg0 pad0.
  have hf := poly_sotp_encode_fail_spec_false msg0 pad0.
  conseq (poly_sotp_decode_correct out0 (poly_sotp_encode_spec msg0 pad0) pad0) => />.
  smt().
qed.

module PolySOTPRoundTripChecked = {
  proc run(rp : W16.t Array768.t, out : W8.t Array96.t,
           msg : W8.t Array96.t, pad : W8.t Array192.t) :
           W8.t Array96.t * W32.t = {
    var flag : W32.t;
    rp <@ NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(rp,msg,pad);
    (out,flag) <@ NTRUPlus768PolySOTPDecodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode(out,rp,pad);
    return (out,flag);
  }
}.

lemma poly_sotp_encode_decode_actual_lossless :
  islossless PolySOTPRoundTripChecked.run.
proof.
  proc; call poly_sotp_decode_lossless; call poly_sotp_encode_lossless; auto.
qed.

lemma poly_sotp_encode_decode_actual_correct rp0 out0 msg0 pad0 :
  phoare [PolySOTPRoundTripChecked.run :
    rp = rp0 /\ out = out0 /\ msg = msg0 /\ pad = pad0 ==>
    res = (msg0,W32.zero)] = 1%r.
proof.
  proc.
  call (poly_sotp_decode_encoded_correct out0 msg0 pad0).
  call (poly_sotp_encode_correct rp0 msg0 pad0).
  auto => />.
qed.
