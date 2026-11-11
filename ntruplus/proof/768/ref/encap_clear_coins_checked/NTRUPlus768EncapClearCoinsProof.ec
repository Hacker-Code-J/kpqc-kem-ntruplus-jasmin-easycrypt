require import AllCore IntDiv List Distr.
from Jasmin require import JWord JModel_x86.
require import Array96 NTRUPlus768EncapClearCoins.

op encap_clear_coins_zero_spec : W8.t Array96.t = Array96.init (fun _ => W8.zero).

lemma encap_clear_coins_functional coins0 :
  hoare [NTRUPlus768EncapClearCoins.M.jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins :
    coins = coins0 ==> res = encap_clear_coins_zero_spec].
proof.
  proc.
  while (0 <= W64.to_uint i <= 96 /\
    forall j, 0 <= j < W64.to_uint i => coins.[j] = W8.zero); last first.
  + auto => />.
    split; first smt().
    move=> w1 i1 hdone hlo hhi hprefix.
    rewrite W64.ultE /= in hdone.
    have hi : W64.to_uint i1 = 96 by smt().
    apply Array96.tP => j hj.
    rewrite /encap_clear_coins_zero_spec Array96.initiE //.
    apply hprefix; smt().
  auto => /> &hr hlo hhi hprefix hloop.
  rewrite W64.ultE /= in hloop.
  have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite hn.
  split; first smt().
  move=> j hjlo hjhi.
  rewrite Array96.get_setE 1:/# /=; smt().
qed.

lemma encap_clear_coins_lossless : islossless
  NTRUPlus768EncapClearCoins.M.jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins.
proof.
  proc.
  while (0 <= W64.to_uint i <= 96) (96 - W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  auto => /> i hlo hhi hd; rewrite W64.ultE /=; smt().
qed.

lemma encap_clear_coins_correct coins0 :
  phoare [NTRUPlus768EncapClearCoins.M.jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins :
    coins = coins0 ==> res = encap_clear_coins_zero_spec] = 1%r.
proof. by conseq encap_clear_coins_lossless (encap_clear_coins_functional coins0). qed.

lemma encap_clear_coins_zero_bytes j : 0 <= j < 96 => encap_clear_coins_zero_spec.[j] = W8.zero.
proof. by move=> hj; rewrite /encap_clear_coins_zero_spec Array96.initiE. qed.
