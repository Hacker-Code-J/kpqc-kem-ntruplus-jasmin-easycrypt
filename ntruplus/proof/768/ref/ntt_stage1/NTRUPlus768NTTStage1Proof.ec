require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.

require import Array768 WArray1536 NTRUPlus768NTTStage1.
require import NTRUPlus768BasemulProof.

op half : int = 384.
op stage1_zeta : W16.t = W16.of_int (-1033).

op stage1_mul (hi : W16.t) : W16.t =
  montgomery_reduce (mul_i16 stage1_zeta hi).

op stage1_pair (lo hi : W16.t) : W16.t * W16.t =
  (lo + stage1_mul hi, lo + hi - stage1_mul hi).

op stage1_spec (p : W16.t Array768.t) : W16.t Array768.t =
  Array768.init (fun j =>
    if j < half then (stage1_pair p.[j] p.[j + half]).`1
    else (stage1_pair p.[j - half] p.[j]).`2).

lemma stage1_mul_i16_functional (a0 b0 : W16.t) :
  hoare [NTRUPlus768NTTStage1.M.__mul_i16 :
    a = a0 /\ b = b0 ==> res = mul_i16 a0 b0].
proof.
  proc; auto => />.
qed.

lemma stage1_montgomery_reduce_functional (a0 : W32.t) :
  hoare [NTRUPlus768NTTStage1.M.__montgomery_reduce :
    a = a0 ==> res = montgomery_reduce a0].
proof.
  proc; auto => />.
qed.

op stage1_prefix
    (ap rp : W16.t Array768.t) (upto : int) : bool =
  (forall j, 0 <= j < upto =>
     rp.[j] = (stage1_pair ap.[j] ap.[j + half]).`1 /\
     rp.[j + half] = (stage1_pair ap.[j] ap.[j + half]).`2).

lemma stage1_prefix_extend
    (ap rp : W16.t Array768.t) (i : int) (lo hi : W16.t) :
  0 <= i < half =>
  stage1_prefix ap rp i =>
  lo = (stage1_pair ap.[i] ap.[i + half]).`1 =>
  hi = (stage1_pair ap.[i] ap.[i + half]).`2 =>
  stage1_prefix ap (rp.[i <- lo].[i + half <- hi]) (i + 1).
proof.
  move=> Hi Hprefix Hlo Hhi j Hj.
  case (j = i) => [-> | Hneq].
  + split.
    - smt(Array768.get_setE).
    smt(Array768.get_setE).
  have Hjold : 0 <= j < i by smt().
  have [Hjlo Hjhi] := Hprefix j Hjold.
  split.
  + smt(Array768.get_setE).
  smt(Array768.get_setE).
qed.

lemma stage1_prefix_full
    (ap rp : W16.t Array768.t) :
  stage1_prefix ap rp half => rp = stage1_spec ap.
proof.
  move=> Hprefix.
  apply Array768.tP => j Hj.
  rewrite /stage1_spec Array768.initiE 1:Hj.
  case (j < half) => Hjhalf.
  + have [Hlo _] := Hprefix j _; first smt().
    smt().
  have Hj' : 0 <= j - half < half by smt().
  have [_ Hhi] := Hprefix (j - half) Hj'.
  smt().
qed.

lemma ntt_stage1_functional
    (rp0 ap0 : W16.t Array768.t) :
  hoare [NTRUPlus768NTTStage1.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1 :
    rp = rp0 /\ ap = ap0 ==> res = stage1_spec ap0].
proof.
  proc.
  seq 2 : (ap = ap0 /\ i = W64.of_int 0 /\ stage1_prefix ap0 rp 0).
  + auto => />; rewrite /stage1_prefix; smt().
  while (0 <= W64.to_uint i <= half /\ ap = ap0 /\
         stage1_prefix ap0 rp (W64.to_uint i)); last first.
  + skip => &hr [Hap [Hi0 Hprefix0]].
    split.
    - split; first by rewrite Hi0 W64.to_uint0; smt().
      split; first exact Hap.
      by rewrite Hi0 W64.to_uint0.
    move=> i1 rp1 Hexit [Hi [Hap1 Hprefix1]].
    rewrite W64.ultE /= in Hexit.
    apply stage1_prefix_full.
    have Hiend : W64.to_uint i1 = half by rewrite /half; smt().
    by rewrite -Hiend.
  inline NTRUPlus768NTTStage1.M.__mul_i16
         NTRUPlus768NTTStage1.M.__montgomery_reduce.
  auto => /> &hr HiLow HiHigh Hprefix Hloop.
  rewrite W64.ultE /= in Hloop.
  have Hi384 : 0 <= W64.to_uint i{hr} < half by rewrite /half; smt().
  have Hplus384 :
      W64.to_uint (i{hr} + W64.of_int (768 %/ 2)) =
      W64.to_uint i{hr} + half.
  + rewrite W64.to_uintD_small /= /half; smt(W64.to_uint_cmp).
  have Hnext : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  split.
  + rewrite Hnext; smt(W64.to_uint_cmp).
  rewrite Hplus384 Hnext.
  apply stage1_prefix_extend; 1: exact Hi384; 1: exact Hprefix.
  + by rewrite /stage1_pair /stage1_zeta /mul_i16 /montgomery_reduce.
  by rewrite /stage1_pair /stage1_zeta /mul_i16 /montgomery_reduce.
qed.

lemma ntt_stage1_lossless :
  islossless
    NTRUPlus768NTTStage1.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1.
proof.
  proc.
  while (0 <= W64.to_uint i <= half) (half - W64.to_uint i);
    last first.
  + auto => /> i0 Hi Hdone.
    rewrite W64.ultE /= /half.
    smt().
  move=> *.
  inline NTRUPlus768NTTStage1.M.__mul_i16
         NTRUPlus768NTTStage1.M.__montgomery_reduce.
  auto => /> &hr Hi Hhigh Hloop.
  rewrite W64.ultE /= in Hloop.
  rewrite W64.to_uintD_small /= /half; smt(W64.to_uint_cmp).
qed.

lemma ntt_stage1_correct
    (rp0 ap0 : W16.t Array768.t) :
  phoare [NTRUPlus768NTTStage1.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1 :
    rp = rp0 /\ ap = ap0 ==> res = stage1_spec ap0] = 1%r.
proof.
  by conseq ntt_stage1_lossless (ntt_stage1_functional rp0 ap0).
qed.
