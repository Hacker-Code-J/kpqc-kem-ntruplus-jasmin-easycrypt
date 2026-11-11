require import AllCore IntDiv List Distr.
from Jasmin require import JWord JModel_x86.
require import Array32 Array224 NTRUPlus768EncapCopyKey.

op encap_copy_key_spec (hash_output : W8.t Array224.t) : W8.t Array32.t =
  Array32.init (fun j => hash_output.[j]).

lemma encap_copy_key_functional ss0 hash0 :
  hoare [NTRUPlus768EncapCopyKey.M.jade_ntruplus_ntruplus768_amd64_ref_encap_copy_key :
    ss = ss0 /\ hash_output = hash0 ==> res = encap_copy_key_spec hash0].
proof.
  proc.
  while (hash_output = hash0 /\ 0 <= W64.to_uint i <= 32 /\
    forall j, 0 <= j < W64.to_uint i => ss.[j] = hash0.[j]); last first.
  + auto => />.
    split; first smt().
    move=> i1 ss1 hdone hlo hhi hprefix.
    rewrite W64.ultE /= in hdone.
    have hi : W64.to_uint i1 = 32 by smt().
    apply Array32.tP => j hj.
    rewrite /encap_copy_key_spec Array32.initiE //.
    apply hprefix; smt().
  auto => /> &hr hlo hhi hprefix hloop.
  rewrite W64.ultE /= in hloop.
  have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite hn.
  split; first smt().
  move=> j hjlo hjhi.
  rewrite Array32.get_setE 1:/# /=; smt().
qed.

lemma encap_copy_key_lossless : islossless
  NTRUPlus768EncapCopyKey.M.jade_ntruplus_ntruplus768_amd64_ref_encap_copy_key.
proof.
  proc.
  while (0 <= W64.to_uint i <= 32) (32 - W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  auto => /> i hlo hhi hd; rewrite W64.ultE /=; smt().
qed.

lemma encap_copy_key_correct ss0 hash0 :
  phoare [NTRUPlus768EncapCopyKey.M.jade_ntruplus_ntruplus768_amd64_ref_encap_copy_key :
    ss = ss0 /\ hash_output = hash0 ==> res = encap_copy_key_spec hash0] = 1%r.
proof. by conseq encap_copy_key_lossless (encap_copy_key_functional ss0 hash0). qed.

lemma encap_copy_key_bytes hash0 j : 0 <= j < 32 =>
  (encap_copy_key_spec hash0).[j] = hash0.[j].
proof. by move=> hj; rewrite /encap_copy_key_spec Array32.initiE. qed.
