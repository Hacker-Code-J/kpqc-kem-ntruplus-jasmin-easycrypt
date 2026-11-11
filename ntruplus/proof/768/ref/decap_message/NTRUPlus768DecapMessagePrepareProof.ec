require import AllCore IntDiv List Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array1153 NTRUPlus768DecapMessagePrepare.
require import NTRUPlus768PolyToBytes NTRUPlus768PolyToBytesProof.

op message_hash_input (bs : W8.t Array1152.t) : W8.t Array1153.t =
  Array1153.init (fun j => if j = 0 then W8.of_int 1 else bs.[j - 1]).

lemma message_serialize_eq :
  equiv [NTRUPlus768DecapMessagePrepare.M.serialize__jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes ~
    NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    ={rp,ap} ==> ={res}].
proof. by proc; sim. qed.

lemma message_serialize_functional bs0 rp0 : poly_tobytes_input_qrange rp0 =>
  hoare [NTRUPlus768DecapMessagePrepare.M.serialize__jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = bs0 /\ ap = rp0 ==> res = poly_tobytes_spec rp0].
proof.
  move=> hr; conseq message_serialize_eq (poly_tobytes_functional bs0 rp0 hr); smt().
qed.

lemma message_serialize_lossless : islossless
  NTRUPlus768DecapMessagePrepare.M.serialize__jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes.
proof. conseq message_serialize_eq poly_tobytes_lossless; smt(). qed.

lemma message_prepare_functional bs0 input0 rp0 : poly_tobytes_input_qrange rp0 =>
  hoare [NTRUPlus768DecapMessagePrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare :
    serialized = bs0 /\ input = input0 /\ r2 = rp0 ==>
    res = (poly_tobytes_spec rp0, message_hash_input (poly_tobytes_spec rp0))].
proof.
  move=> hr; proc.
  seq 2 : (serialized = poly_tobytes_spec rp0).
  + call (message_serialize_functional bs0 rp0 hr); auto.
  while (serialized = poly_tobytes_spec rp0 /\ 0 <= W64.to_uint i <= 1152 /\
    input.[0] = W8.of_int 1 /\
    forall j, 0 <= j < W64.to_uint i => input.[j+1] = serialized.[j]); last first.
  + auto => /> &hr.
    split; first smt().
    move=> i1 inp1 hdone hlo hhi hzero hprefix.
    rewrite W64.ultE /= in hdone.
    have hi : W64.to_uint i1 = 1152 by smt().
    apply Array1153.tP => j hj.
    rewrite /message_hash_input Array1153.initiE //.
    case (j = 0) => hz; first by rewrite hz hzero.
    have hp := hprefix (j-1) _; first smt().
    rewrite (_ : j-1+1 = j) 1:/# in hp.
    by rewrite hz hp.
  auto => /> &hr hlo hhi hzero hprefix hloop.
  rewrite W64.ultE /= in hloop.
  have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite hn !Array1153.get_setE 1:/# /=.
  split; first smt().
  split; first smt().
  move=> j hjlo hjhi.
  rewrite Array1153.get_setE 1:/# /=; smt().
qed.

lemma message_prepare_lossless : islossless
  NTRUPlus768DecapMessagePrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare.
proof.
  proc.
  while (0 <= W64.to_uint i <= 1152) (1152 - W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  wp; call message_serialize_lossless; auto => />.
  move=> i hlo hhi hd; rewrite W64.ultE /=; smt().
qed.

lemma message_prepare_correct bs0 input0 rp0 : poly_tobytes_input_qrange rp0 =>
  phoare [NTRUPlus768DecapMessagePrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare :
    serialized = bs0 /\ input = input0 /\ r2 = rp0 ==>
    res = (poly_tobytes_spec rp0, message_hash_input (poly_tobytes_spec rp0))] = 1%r.
proof. move=> hr; by conseq message_prepare_lossless (message_prepare_functional bs0 input0 rp0 hr). qed.
