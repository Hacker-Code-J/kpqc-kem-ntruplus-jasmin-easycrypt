require import AllCore IntDiv List Distr.
from Jasmin require import JWord JModel_x86.
require import Array32 Array96 Array129 NTRUPlus768DecapHashHPrepare.

op hash_h_prepare_spec (msg : W8.t Array96.t) (suffix : W8.t Array32.t) :
  W8.t Array129.t = Array129.init (fun j =>
    if j = 0 then W8.of_int 2 else
    if j <= 96 then msg.[j-1] else suffix.[j-97]).

lemma hash_h_prepare_functional input0 msg0 suffix0 :
  hoare [NTRUPlus768DecapHashHPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare :
    input = input0 /\ msg = msg0 /\ suffix = suffix0 ==>
    res = hash_h_prepare_spec msg0 suffix0].
proof.
  proc.
  seq 4 : (msg = msg0 /\ suffix = suffix0 /\ input.[0] = W8.of_int 2 /\
    forall j, 0 <= j < 96 => input.[j+1] = msg0.[j]).
  + while (msg = msg0 /\ suffix = suffix0 /\ 0 <= W64.to_uint i <= 96 /\
      input.[0] = W8.of_int 2 /\
      forall j, 0 <= j < W64.to_uint i => input.[j+1] = msg0.[j]); last first.
    - auto => />.
      split; first smt().
      move=> i1 inp1 hdone hlo hhi hz hp.
      rewrite W64.ultE /= in hdone; smt().
    auto => /> &hr hlo hhi hz hp hloop.
    rewrite W64.ultE /= in hloop.
    have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
    - rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
    rewrite hn !Array129.get_setE 1:/# /=.
    split; first smt().
    split; first smt().
    move=> j hjlo hjhi.
    rewrite Array129.get_setE 1:/# /=; smt().
  while (msg = msg0 /\ suffix = suffix0 /\ 0 <= W64.to_uint i <= 32 /\
    input.[0] = W8.of_int 2 /\
    (forall j, 0 <= j < 96 => input.[j+1] = msg0.[j]) /\
    forall j, 0 <= j < W64.to_uint i => input.[j+97] = suffix0.[j]); last first.
  + auto => /> &hr hz hm.
    split; first smt().
    move=> i1 inp1 hdone hlo hhi hz1 hm1 hs.
    rewrite W64.ultE /= in hdone.
    have hi : W64.to_uint i1 = 32 by smt().
    apply Array129.tP => j hj.
    rewrite /hash_h_prepare_spec Array129.initiE //.
    case (j = 0) => hzero; first by rewrite hzero hz1.
    case (j <= 96) => hmsg.
    - have hp := hm1 (j-1) _; first smt().
      rewrite (_ : j-1+1 = j) 1:/# in hp.
      smt().
    have hp := hs (j-97) _; first smt().
    rewrite (_ : j-97+97 = j) 1:/# in hp.
    smt().
  auto => /> &hr hlo hhi hz hm hs hloop.
  rewrite W64.ultE /= in hloop.
  have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  have h97 : W64.to_uint (i{hr} + W64.of_int 97) = W64.to_uint i{hr} + 97.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite hn h97 !Array129.get_setE 1:/# /=.
  split; first smt().
  split; first smt().
  split.
  + move=> j hjlo hjhi; rewrite Array129.get_setE 1:/# /=; smt().
  move=> j hjlo hjhi; rewrite Array129.get_setE 1:/# /=; smt().
qed.

lemma hash_h_prepare_lossless : islossless
  NTRUPlus768DecapHashHPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare.
proof.
  proc.
  while (0 <= W64.to_uint i <= 32) (32 - W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  wp.
  while (0 <= W64.to_uint i <= 96) (96 - W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  auto => />.
  move=> i; split.
  + rewrite W64.ultE /=; smt().
  move=> hd hlo hhi i1.
  rewrite W64.ultE /=; smt().
qed.

lemma hash_h_prepare_correct input0 msg0 suffix0 :
  phoare [NTRUPlus768DecapHashHPrepare.M.jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare :
    input = input0 /\ msg = msg0 /\ suffix = suffix0 ==>
    res = hash_h_prepare_spec msg0 suffix0] = 1%r.
proof. by conseq hash_h_prepare_lossless (hash_h_prepare_functional input0 msg0 suffix0). qed.

lemma hash_h_prepare_to_list msg suffix :
  Array129.to_list (hash_h_prepare_spec msg suffix) =
  [W8.of_int 2] ++ Array96.to_list msg ++ Array32.to_list suffix.
proof.
  apply (eq_from_nth witness).
  + by rewrite Array129.size_to_list !size_cat Array96.size_to_list Array32.size_to_list.
  move=> j; rewrite Array129.size_to_list => hj.
  rewrite Array129.get_to_list /hash_h_prepare_spec Array129.initiE //.
  case (j = 0) => hz; first by rewrite hz /=.
  rewrite /= nth_cat Array96.size_to_list.
  smt(Array96.get_to_list Array32.get_to_list).
qed.
