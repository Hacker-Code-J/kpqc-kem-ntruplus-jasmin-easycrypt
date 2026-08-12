require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import W16extra.
require import Array768.
require import NTRUPlus768NTTStage1Proof.
require import NTRUPlus768BasemulProof.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768NTTSchedule.

import Ring.IntID IntOrder.

op stage1_root : int = (zeta_root ^ 96) %% q.

op input_qrange (p : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 => in_qrange p.[j].

op stage1_math (p : W16.t Array768.t) (j : int) : int =
  if j < half then
    coeff p.[j] + coeff p.[j + half] * stage1_root
  else
    coeff p.[j - half] + coeff p.[j] - coeff p.[j] * stage1_root.

op stage1_algebra
    (input output : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 =>
    (if j < half then -2 * q <= coeff output.[j] < 2 * q
     else -3 * q <= coeff output.[j] < 3 * q) /\
    coeff output.[j] %% q = stage1_math input j %% q.

lemma stage1_zeta_schedule_index :
  coeff stage1_zeta = zetas192_coeff 1 /\ zetas192_exp 1 = 96.
proof.
  split.
  + rewrite /coeff /stage1_zeta /zetas192_coeff /zetas192_coeffs /=.
    rewrite W16.of_sintK /W16.smod /=.
    done.
  by rewrite /zetas192_exp /zetas192_exponents /=.
qed.

lemma stage1_zeta_montgomery_meaning :
  (coeff stage1_zeta * Rinv) %% q = stage1_root.
proof.
  have Hschedule := zetas192_relation 1 _; first smt().
  move: Hschedule.
  rewrite /decode_mont /stage1_root /zetas192_coeff /zetas192_exp.
  rewrite /zetas192_coeffs /zetas192_exponents /coeff /stage1_zeta /=.
  rewrite W16.of_sintK /W16.smod /=.
  done.
qed.

lemma stage1_zeta_in_qrange : in_qrange stage1_zeta.
proof.
  rewrite /in_qrange /coeff /stage1_zeta W16.of_sintK /W16.smod /q /=.
  done.
qed.

lemma stage1_pair_algebra (lo hi : W16.t) :
  in_qrange lo =>
  in_qrange hi =>
  -2 * q <= coeff (lo + stage1_mul hi) < 2 * q /\
  -3 * q <= coeff (lo + hi - stage1_mul hi) < 3 * q /\
  coeff (lo + stage1_mul hi) %% q =
    (coeff lo + coeff hi * stage1_root) %% q /\
  coeff (lo + hi - stage1_mul hi) %% q =
    (coeff lo + coeff hi - coeff hi * stage1_root) %% q.
proof.
  move=> Hlo Hhi.
  have Hz := stage1_zeta_in_qrange.
  have Hproduct := product_bound (coeff stage1_zeta) (coeff hi) Hz Hhi.
  have Hreduce := montgomery_reduce_of_int (coeff stage1_zeta * coeff hi) Hproduct.
  have Hmul : mul_i16 stage1_zeta hi =
      W32.of_int (coeff stage1_zeta * coeff hi) by apply mul_i16E.
  have Ht : stage1_mul hi = montgomery_reduce
      (W32.of_int (coeff stage1_zeta * coeff hi))
    by rewrite /stage1_mul Hmul.
  have [Hreduce_range Hreduce_congr] := Hreduce.
  have Htrange : -q <= coeff (stage1_mul hi) < q by rewrite Ht.
  have Htcongr : coeff (stage1_mul hi) %% q =
      (coeff stage1_zeta * coeff hi * Rinv) %% q by rewrite Ht.
  have Htroot : coeff (stage1_mul hi) %% q =
      (coeff hi * stage1_root) %% q.
  + rewrite Htcongr
      (_ : coeff stage1_zeta * coeff hi * Rinv =
           coeff hi * (coeff stage1_zeta * Rinv)) 1:/#.
    rewrite -modzMmr stage1_zeta_montgomery_meaning.
    done.
  have Hsumlo : coeff (lo + stage1_mul hi) =
      coeff lo + coeff (stage1_mul hi).
  + apply W16extra.to_sintD_small.
    rewrite /coeff /q /=.
    smt().
  have Hsumhi : coeff (lo + hi) = coeff lo + coeff hi.
  + apply W16extra.to_sintD_small.
    rewrite /coeff /q /=.
    smt().
  have Hsumhi_range : -2 * q <= coeff (lo + hi) < 2 * q.
  + move: Hsumhi Hlo Hhi.
    rewrite /in_qrange.
    smt().
  have Hsubhi : coeff (lo + hi - stage1_mul hi) =
      coeff lo + coeff hi - coeff (stage1_mul hi).
  + rewrite (_ : coeff lo + coeff hi - coeff (stage1_mul hi) =
                 coeff (lo + hi) - coeff (stage1_mul hi)) 1:/#.
    apply W16extra.to_sintB_small.
    move: Hsumhi_range Htrange.
    rewrite /coeff /q /=.
    smt().
  have Hlowcongr : coeff (lo + stage1_mul hi) %% q =
      (coeff lo + coeff hi * stage1_root) %% q.
  + rewrite Hsumlo -modzDmr Htroot modzDmr.
    done.
  have Hhighcongr : coeff (lo + hi - stage1_mul hi) %% q =
      (coeff lo + coeff hi - coeff hi * stage1_root) %% q.
  + rewrite Hsubhi -modzBm Htroot modzBm.
    done.
  have Hlowrange : -2 * q <= coeff (lo + stage1_mul hi) < 2 * q.
  + move: Hsumlo Hlo Htrange; rewrite /in_qrange; smt().
  have Hhighrange :
      -3 * q <= coeff (lo + hi - stage1_mul hi) < 3 * q.
  + move: Hsubhi Hlo Hhi Htrange; rewrite /in_qrange; smt().
  split; first exact Hlowrange.
  split; first exact Hhighrange.
  split; first exact Hlowcongr.
  exact Hhighcongr.
qed.

lemma stage1_spec_algebra (p : W16.t Array768.t) :
  input_qrange p => stage1_algebra p (stage1_spec p).
proof.
  move=> Hinput j Hj.
  have Hjrange : in_qrange p.[j] by apply Hinput.
  rewrite /stage1_algebra /stage1_spec Array768.initiE 1:Hj /stage1_math.
  case (j < half) => Hjhalf.
  + have Hpair := stage1_pair_algebra p.[j] p.[j + half]
        (Hinput j _) (Hinput (j + half) _); 1,2: smt().
    move: Hpair; rewrite /stage1_pair /=; smt().
  have Hpair := stage1_pair_algebra p.[j - half] p.[j]
      (Hinput (j - half) _) Hjrange; first smt().
  move: Hpair; rewrite /stage1_pair /=; smt().
qed.

lemma ntt_stage1_algebra_functional
    (rp0 ap0 : W16.t Array768.t) :
  input_qrange ap0 =>
  hoare [NTRUPlus768NTTStage1.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1 :
    rp = rp0 /\ ap = ap0 ==> stage1_algebra ap0 res].
proof.
  move=> Hinput.
  conseq (ntt_stage1_functional rp0 ap0) => /> &hr Hap j.
  rewrite Hap.
  move=> Hj.
  have Hspec := stage1_spec_algebra ap0 Hinput.
  rewrite /stage1_algebra in Hspec.
  exact (Hspec j Hj).
qed.

lemma ntt_stage1_correct_algebra
    (rp0 ap0 : W16.t Array768.t) :
  input_qrange ap0 =>
  phoare [NTRUPlus768NTTStage1.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1 :
    rp = rp0 /\ ap = ap0 ==> stage1_algebra ap0 res] = 1%r.
proof.
  move=> Hinput.
  have Hfunctional := ntt_stage1_algebra_functional rp0 ap0 Hinput.
  by conseq ntt_stage1_lossless Hfunctional.
qed.
