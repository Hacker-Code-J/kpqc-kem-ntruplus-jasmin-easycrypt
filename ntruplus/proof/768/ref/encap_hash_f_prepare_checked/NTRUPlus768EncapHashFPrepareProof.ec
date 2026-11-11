require import AllCore IntDiv List Distr.
from Jasmin require import JWord JModel_x86.
require import Array1152 Array1153 NTRUPlus768EncapHashFPrepare.

op encap_hash_f_input_spec (pk : W8.t Array1152.t) : W8.t Array1153.t =
  Array1153.init (fun j => if j = 0 then W8.zero else pk.[j-1]).

lemma encap_hash_f_prepare_functional input0 pk0 :
  hoare [NTRUPlus768EncapHashFPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_encap_hash_f_prepare :
    input = input0 /\ pk = pk0 ==> res = encap_hash_f_input_spec pk0].
proof.
  proc.
  while (pk = pk0 /\ 0 <= W64.to_uint i <= 1152 /\
    input.[0] = W8.zero /\
    forall j, 0 <= j < W64.to_uint i => input.[j+1] = pk0.[j]); last first.
  + auto => />.
    split; first smt().
    move=> i1 inp1 hdone hlo hhi hzero hprefix.
    rewrite W64.ultE /= in hdone.
    have hi : W64.to_uint i1 = 1152 by smt().
    apply Array1153.tP => j hj.
    rewrite /encap_hash_f_input_spec Array1153.initiE //.
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

lemma encap_hash_f_prepare_lossless : islossless
  NTRUPlus768EncapHashFPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_encap_hash_f_prepare.
proof.
  proc.
  while (0 <= W64.to_uint i <= 1152) (1152 - W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  auto => /> i hlo hhi hd; rewrite W64.ultE /=; smt().
qed.

lemma encap_hash_f_prepare_correct input0 pk0 :
  phoare [NTRUPlus768EncapHashFPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_encap_hash_f_prepare :
    input = input0 /\ pk = pk0 ==> res = encap_hash_f_input_spec pk0] = 1%r.
proof. by conseq encap_hash_f_prepare_lossless (encap_hash_f_prepare_functional input0 pk0). qed.

lemma encap_hash_f_input_to_list pk :
  Array1153.to_list (encap_hash_f_input_spec pk) =
  [W8.zero] ++ Array1152.to_list pk.
proof.
  apply (eq_from_nth witness).
  + by rewrite Array1153.size_to_list size_cat Array1152.size_to_list.
  move=> j; rewrite Array1153.size_to_list => hj.
  rewrite Array1153.get_to_list /encap_hash_f_input_spec Array1153.initiE //.
qed.
