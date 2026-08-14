require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.

require import Array768 WArray1536 NTRUPlus768InvNTTFinal.
require import NTRUPlus768BasemulProof.

op half : int = 384.
op zminusz5inv : W16.t = W16.of_int (-1665).
op ninv : W16.t = W16.of_int (-811).
op twoninv : W16.t = W16.of_int (-1622).

op invntt_final_mul (z a : W16.t) : W16.t =
  montgomery_reduce (mul_i16 z a).

op invntt_final_pair (lo hi : W16.t) : W16.t * W16.t =
  let t1 = lo + hi in
  let t2 = invntt_final_mul zminusz5inv (lo - hi) in
  (invntt_final_mul ninv (t1 - t2), invntt_final_mul twoninv t2).

op invntt_final_pair_at (p : W16.t Array768.t) (k : int) : W16.t * W16.t =
  invntt_final_pair p.[k] p.[k + half].

op invntt_final_prefix_spec
    (p : W16.t Array768.t) (upto : int) : W16.t Array768.t =
  Array768.init (fun j =>
    if 0 <= j < upto then
      (invntt_final_pair_at p j).`1
    else if half <= j < half + upto then
      (invntt_final_pair_at p (j - half)).`2
    else p.[j]).

op invntt_final_spec (p : W16.t Array768.t) : W16.t Array768.t =
  invntt_final_prefix_spec p half.

lemma invntt_final_mul_i16_functional (a0 b0 : W16.t) :
  hoare [NTRUPlus768InvNTTFinal.M.__mul_i16 :
    a = a0 /\ b = b0 ==> res = mul_i16 a0 b0].
proof.
  proc; auto => />.
qed.

lemma invntt_final_montgomery_reduce_functional (a0 : W32.t) :
  hoare [NTRUPlus768InvNTTFinal.M.__montgomery_reduce :
    a = a0 ==> res = montgomery_reduce a0].
proof.
  proc; auto => />.
qed.

lemma invntt_final_prefix_zero (p : W16.t Array768.t) :
  invntt_final_prefix_spec p 0 = p.
proof.
  apply Array768.tP => j Hj.
  rewrite /invntt_final_prefix_spec Array768.initiE 1:Hj.
  smt().
qed.

lemma invntt_final_prefix_curr0
    (p : W16.t Array768.t) (upto : int) :
  0 <= upto < half =>
  (invntt_final_prefix_spec p upto).[upto] = p.[upto].
proof.
  move=> Hupto.
  rewrite /invntt_final_prefix_spec Array768.initiE 1:/#.
  smt().
qed.

lemma invntt_final_prefix_curr1
    (p : W16.t Array768.t) (upto : int) :
  0 <= upto < half =>
  (invntt_final_prefix_spec p upto).[half + upto] = p.[half + upto].
proof.
  move=> Hupto.
  rewrite /invntt_final_prefix_spec Array768.initiE 1:/#.
  smt().
qed.

lemma invntt_final_prefix_step
    (p : W16.t Array768.t) (upto : int) :
  0 <= upto < half =>
  (invntt_final_prefix_spec p upto)
    .[upto <- (invntt_final_pair_at p upto).`1]
    .[half + upto <- (invntt_final_pair_at p upto).`2] =
  invntt_final_prefix_spec p (upto + 1).
proof.
  move=> Hupto.
  apply Array768.tP => j Hj.
  rewrite /invntt_final_prefix_spec.
  rewrite Array768.initiE 1:Hj.
  case (j = upto) => [-> | Hneq0].
  + by rewrite !Array768.get_setE; smt().
  case (j = half + upto) => [-> | Hneq1].
  + by rewrite !Array768.get_setE; smt().
  rewrite !Array768.get_setE.
  + smt().
  + smt().
  rewrite Array768.initiE 1:Hj.
  smt().
qed.

lemma invntt_final_functional (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768InvNTTFinal.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_final :
    rp = rp0 ==> res = invntt_final_spec rp0].
proof.
  proc.
  seq 2 : (rp = invntt_final_prefix_spec rp0 0 /\ i = W64.of_int 0).
  + auto => />.
    by rewrite invntt_final_prefix_zero.
  while (0 <= W64.to_uint i <= half /\
         rp = invntt_final_prefix_spec rp0 (W64.to_uint i)); last first.
  + skip => &hr [Hi Hrp].
    split.
    + split; smt(W64.to_uint0).
    move=> i1 rp1 Hexit [Hi1 Hrp1].
    rewrite W64.ultE /= in Hexit.
    have Hiend : W64.to_uint i1 = half by smt().
    rewrite /invntt_final_spec.
    smt().
  inline NTRUPlus768InvNTTFinal.M.__mul_i16
         NTRUPlus768InvNTTFinal.M.__montgomery_reduce.
  auto => /> &hr Hi Hrp Hloop.
  rewrite W64.ultE /= in Hloop.
  have Hidx : 0 <= W64.to_uint i{hr} < half by smt().
  have Hget0 :
      (invntt_final_prefix_spec rp0 (W64.to_uint i{hr})).[W64.to_uint i{hr}] =
      rp0.[W64.to_uint i{hr}].
  + apply invntt_final_prefix_curr0; smt().
  have Hget1 :
      (invntt_final_prefix_spec rp0 (W64.to_uint i{hr})).[W64.to_uint i{hr} + half] =
      rp0.[W64.to_uint i{hr} + half].
  + have -> : W64.to_uint i{hr} + half = half + W64.to_uint i{hr} by smt().
    apply invntt_final_prefix_curr1; smt().
  have Hnext : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  have Haddr : W64.to_uint (i{hr} + W64.of_int half) =
      W64.to_uint i{hr} + half.
  + rewrite W64.to_uintD_small /= /half; smt(W64.to_uint_cmp).
  have Hstep :
      (invntt_final_prefix_spec rp0 (W64.to_uint i{hr}))
        .[W64.to_uint i{hr} <-
          (invntt_final_pair_at rp0 (W64.to_uint i{hr})).`1]
        .[half + W64.to_uint i{hr} <-
          (invntt_final_pair_at rp0 (W64.to_uint i{hr})).`2] =
      invntt_final_prefix_spec rp0 (W64.to_uint i{hr} + 1).
  + apply invntt_final_prefix_step; smt().
  split.
  + rewrite Hnext; smt(W64.to_uint_cmp).
  rewrite Hnext.
  rewrite -Hstep.
  rewrite /invntt_final_pair_at /invntt_final_pair /invntt_final_mul /half.
  rewrite Hget0 Haddr Hget1.
  rewrite /zminusz5inv /ninv /twoninv /mul_i16 /montgomery_reduce /=.
  smt().
qed.

lemma invntt_final_lossless :
  islossless
    NTRUPlus768InvNTTFinal.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_final.
proof.
  proc.
  while (0 <= W64.to_uint i <= half) (half - W64.to_uint i); last first.
  + auto => /> i0 Hi Hdone.
    rewrite W64.ultE /= /half.
    smt().
  move=> *.
  inline NTRUPlus768InvNTTFinal.M.__mul_i16
         NTRUPlus768InvNTTFinal.M.__montgomery_reduce.
  auto => /> &hr Hi Hhigh Hloop.
  rewrite W64.ultE /= in Hloop.
  rewrite W64.to_uintD_small /= /half; smt(W64.to_uint_cmp).
qed.

lemma invntt_final_correct (rp0 : W16.t Array768.t) :
  phoare [NTRUPlus768InvNTTFinal.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_final :
    rp = rp0 ==> res = invntt_final_spec rp0] = 1%r.
proof.
  by conseq invntt_final_lossless (invntt_final_functional rp0).
qed.
