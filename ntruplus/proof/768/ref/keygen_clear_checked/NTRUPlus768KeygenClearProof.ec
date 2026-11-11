require import AllCore IntDiv List Distr.
from Jasmin require import JWord JModel_x86.
require import Array14466 NTRUPlus768KeygenClear.

op keygen_clear_zero_spec : W8.t Array14466.t = Array14466.init (fun _ => W8.zero).

lemma keygen_clear_functional workspace0 :
  hoare [NTRUPlus768KeygenClear.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_clear :
    workspace = workspace0 ==> res = keygen_clear_zero_spec].
proof.
  proc.
  while (0 <= W64.to_uint i <= 14466 /\
    forall j, 0 <= j < W64.to_uint i => workspace.[j] = W8.zero); last first.
  + auto => />.
    split; first smt().
    move=> i1 w1 hdone hlo hhi hprefix.
    rewrite W64.ultE /= in hdone.
    have hi : W64.to_uint i1 = 14466 by smt().
    apply Array14466.tP => j hj.
    rewrite /keygen_clear_zero_spec Array14466.initiE //.
    apply hprefix; smt().
  auto => /> &hr hlo hhi hprefix hloop.
  rewrite W64.ultE /= in hloop.
  have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite hn.
  split; first smt().
  move=> j hjlo hjhi.
  rewrite Array14466.get_setE 1:/# /=; smt().
qed.

lemma keygen_clear_lossless : islossless
  NTRUPlus768KeygenClear.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_clear.
proof.
  proc.
  while (0 <= W64.to_uint i <= 14466) (14466 - W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  auto => /> i hlo hhi hd; rewrite W64.ultE /=; smt().
qed.

lemma keygen_clear_correct workspace0 :
  phoare [NTRUPlus768KeygenClear.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_clear :
    workspace = workspace0 ==> res = keygen_clear_zero_spec] = 1%r.
proof. by conseq keygen_clear_lossless (keygen_clear_functional workspace0). qed.

lemma keygen_clear_zero_bytes j : 0 <= j < 14466 => keygen_clear_zero_spec.[j] = W8.zero.
proof. by move=> hj; rewrite /keygen_clear_zero_spec Array14466.initiE. qed.
