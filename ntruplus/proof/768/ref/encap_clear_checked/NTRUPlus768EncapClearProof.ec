require import AllCore IntDiv List Distr.
from Jasmin require import JWord JModel_x86.
require import Array13634 NTRUPlus768EncapClear.

op encap_clear_zero_spec : W8.t Array13634.t = Array13634.init (fun _ => W8.zero).

lemma encap_clear_functional workspace0 :
  hoare [NTRUPlus768EncapClear.M.jade_ntruplus_ntruplus768_amd64_ref_encap_clear :
    workspace = workspace0 ==> res = encap_clear_zero_spec].
proof.
  proc.
  while (0 <= W64.to_uint i <= 13634 /\
    forall j, 0 <= j < W64.to_uint i => workspace.[j] = W8.zero); last first.
  + auto => />.
    split; first smt().
    move=> i1 w1 hdone hlo hhi hprefix.
    rewrite W64.ultE /= in hdone.
    have hi : W64.to_uint i1 = 13634 by smt().
    apply Array13634.tP => j hj.
    rewrite /encap_clear_zero_spec Array13634.initiE //.
    apply hprefix; smt().
  auto => /> &hr hlo hhi hprefix hloop.
  rewrite W64.ultE /= in hloop.
  have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite hn.
  split; first smt().
  move=> j hjlo hjhi.
  rewrite Array13634.get_setE 1:/# /=; smt().
qed.

lemma encap_clear_lossless : islossless
  NTRUPlus768EncapClear.M.jade_ntruplus_ntruplus768_amd64_ref_encap_clear.
proof.
  proc.
  while (0 <= W64.to_uint i <= 13634) (13634 - W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  auto => /> i hlo hhi hd; rewrite W64.ultE /=; smt().
qed.

lemma encap_clear_correct workspace0 :
  phoare [NTRUPlus768EncapClear.M.jade_ntruplus_ntruplus768_amd64_ref_encap_clear :
    workspace = workspace0 ==> res = encap_clear_zero_spec] = 1%r.
proof. by conseq encap_clear_lossless (encap_clear_functional workspace0). qed.

lemma encap_clear_zero_bytes j : 0 <= j < 13634 => encap_clear_zero_spec.[j] = W8.zero.
proof. by move=> hj; rewrite /encap_clear_zero_spec Array13634.initiE. qed.
