require import AllCore IntDiv Distr StdOrder.
from Jasmin require import JWord JUtils.

require import Array1152.

import IntOrder.

op verify_prefix_eq
    (buf1 buf2 : W8.t Array1152.t)
    (n : int) : bool =
  forall k, 0 <= k < n => buf1.[k] = buf2.[k].

lemma verify_prefix_eq_full
    (buf1 buf2 : W8.t Array1152.t) :
  verify_prefix_eq buf1 buf2 1152 <=> buf1 = buf2.
proof.
  split.
  + move=> Hprefix.
    apply Array1152.tP => k Hk.
    exact (Hprefix k Hk).
  + move=> -> k _.
    done.
qed.

lemma array1152_neq_exists_mismatch
    (buf1 buf2 : W8.t Array1152.t) :
  buf1 <> buf2 <=> exists k, 0 <= k < 1152 /\ buf1.[k] <> buf2.[k].
proof. by smt(verify_prefix_eq_full). qed.

op verify_spec
    (buf1 buf2 : W8.t Array1152.t) : W64.t =
  if buf1 = buf2 then W64.of_int 0 else W64.of_int 1.

lemma w64_zero_neq_one : W64.of_int 0 <> W64.of_int 1.
proof. by rewrite W64.to_uint_eq !W64.of_uintK /=. qed.

lemma pow2_63 : 2 ^ 63 = 9223372036854775808 by [].

lemma normalize_nonzero_byte (x : int) :
  0 < x < 256 =>
  ((-x) %% (2 ^ 64)) %/ (2 ^ 63) = 1.
proof.
  rewrite pow2_63 pow2_64.
  move=> Hx.
  have Hmod :
      (-x) %% 18446744073709551616 = 18446744073709551616 - x.
  + have Hrange :
        0 <= 18446744073709551616 - x < 18446744073709551616 by smt().
    have Hcanonical :=
      emodz_eq 18446744073709551616 (-1)
        (18446744073709551616 - x) Hrange.
    have Heq :
        (-1) * 18446744073709551616 +
          (18446744073709551616 - x) = -x by ring.
    by rewrite -Heq; exact Hcanonical.
  rewrite Hmod.
  have Hrange :
      0 <= 9223372036854775808 - x < 9223372036854775808 by smt().
  have -> :
      18446744073709551616 - x =
        1 * 9223372036854775808 + (9223372036854775808 - x) by ring.
  exact (edivz_eq 9223372036854775808 1
    (9223372036854775808 - x) Hrange).
qed.

lemma verify_spec_range
    (buf1 buf2 : W8.t Array1152.t) :
  verify_spec buf1 buf2 = W64.of_int 0 \/
  verify_spec buf1 buf2 = W64.of_int 1.
proof.
  rewrite /verify_spec.
  by case (buf1 = buf2).
qed.

lemma verify_spec_eq
    (buf1 buf2 : W8.t Array1152.t) :
  buf1 = buf2 =>
  verify_spec buf1 buf2 = W64.of_int 0.
proof. by move=> ->; rewrite /verify_spec. qed.

lemma verify_spec_eq_iff
    (buf1 buf2 : W8.t Array1152.t) :
  verify_spec buf1 buf2 = W64.of_int 0 <=> buf1 = buf2.
proof.
  rewrite /verify_spec.
  case (buf1 = buf2) => Heq /=; smt(w64_zero_neq_one).
qed.

lemma verify_spec_neq
    (buf1 buf2 : W8.t Array1152.t) :
  buf1 <> buf2 =>
  verify_spec buf1 buf2 = W64.of_int 1.
proof.
  move=> Hneq.
  rewrite /verify_spec.
  case (buf1 = buf2) => Heq.
  + by smt().
  + done.
qed.

lemma verify_spec_neq_iff
    (buf1 buf2 : W8.t Array1152.t) :
  verify_spec buf1 buf2 = W64.of_int 1 <=> buf1 <> buf2.
proof.
  rewrite /verify_spec.
  case (buf1 = buf2) => Heq /=; smt(w64_zero_neq_one).
qed.

lemma verify_spec_mismatch_iff
    (buf1 buf2 : W8.t Array1152.t) :
  verify_spec buf1 buf2 = W64.of_int 1 <=>
  exists k, 0 <= k < 1152 /\ buf1.[k] <> buf2.[k].
proof.
  rewrite verify_spec_neq_iff array1152_neq_exists_mismatch.
  done.
qed.

module Verify = {
  (* Fixed-length array model of the C helper's uint8 XOR/OR accumulator and
     final uint64 negation/shift normalization.  This is not an extracted-C,
     pointer, timing, or binary-equivalence theorem. *)
  proc verify(buf1 : W8.t Array1152.t,
              buf2 : W8.t Array1152.t) : W64.t = {
    var acc : W8.t;
    var i : int;

    acc <- W8.zero;
    i <- 0;
    while (i < 1152) {
      acc <- acc `|` (buf1.[i] `^` buf2.[i]);
      i <- i + 1;
    }
    return ((- (zeroextu64 acc)) `>>` (W8.of_int 63));
  }
}.

lemma verify_correct_h
    (buf10 buf20 : W8.t Array1152.t) :
  hoare [Verify.verify :
    arg = (buf10, buf20) ==>
      (buf10 = buf20 => res = W64.of_int 0) /\
      (buf10 <> buf20 => res = W64.of_int 1)].
proof.
  proc => /=.
  wp; while (#pre /\ 0 <= i{hr} <= 1152 /\
             (to_uint acc{hr} = 0 <=>
              verify_prefix_eq buf10 buf20 i{hr})); last first.
  + auto => />; split; first by smt().
    move=> acc i il ih HL HR.
    have Hi : i = 1152 by smt().
    split.
    + move=> Heq.
      have Hacc0 : to_uint acc = 0.
      + apply HR.
        rewrite Hi verify_prefix_eq_full.
        exact Heq.
      have Hzero : zeroextu64 acc = W64.zero.
      + apply W64.to_uint_eq.
        by rewrite to_uint_zeroextu64 Hacc0.
      rewrite Hzero.
      apply W64.to_uint_eq.
      by rewrite /(`>>`) /= to_uint_shr 1:/# to_uintNE /=.
    + move=> Hneq.
      have Haccnz : to_uint acc <> 0 by
        smt(verify_prefix_eq_full).
      apply W64.to_uint_eq.
      rewrite /(`>>`) /= to_uint_shr 1:/# to_uintNE /=.
      rewrite to_uint_zeroextu64.
      have [Hge0 Hlt256] := W8.to_uint_cmp acc.
      have Hgt0 : 0 < to_uint acc.
      + rewrite ltr_neqAle.
        split.
        - by rewrite eq_sym.
        - exact Hge0.
      have Hpos : 0 < to_uint acc < 256.
      + split; first exact Hgt0.
        by move: Hlt256 => /= /#.
      have Hnorm := normalize_nonzero_byte (to_uint acc) Hpos.
      by smt(W64.of_uintK).
  auto => /> &hr il ih [HL HR] hguard.
  pose x := buf10.[i{hr}] `^` buf20.[i{hr}].
  split; first by smt().
  split.
  + move=> H0 k Hk.
    have Hor0 : (acc{hr} `|` x) = W8.zero.
    + rewrite -(W8.to_uintK' (acc{hr} `|` x)) /x H0.
      done.
    have Hacc0 : acc{hr} = W8.zero.
    + move: Hor0.
      by rewrite !wordP; smt(orwE zerowE).
    have Haccu0 : to_uint acc{hr} = 0 by rewrite Hacc0 /=.
    have Hx0 : x = W8.zero.
    + move: Hor0.
      by rewrite !wordP; smt(orwE zerowE).
    case (k < i{hr}).
    + move=> Hlt.
      apply (HL Haccu0) => /#.
    move=> Hnlt.
    have -> : k = i{hr} by smt().
    move: Hx0.
    rewrite /x W8.WRing.addr_eq0 /oppw /=.
    by smt().
  + move=> Hprefix.
    have Hacc0 : to_uint acc{hr} = 0.
    + apply HR => k Hk.
      apply Hprefix => /#.
    have Hx0 : x = W8.zero.
    + have Hi : 0 <= i{hr} < i{hr} + 1 by smt().
      move: (Hprefix i{hr} Hi).
      rewrite /x.
      move=> Heq.
      by rewrite Heq W8.WRing.addNr.
    have Haccword0 : acc{hr} = W8.zero.
    + rewrite -(W8.to_uintK' acc{hr}) Hacc0.
      done.
    by rewrite Haccword0 or0w Hx0 /=.
qed.

lemma verify_functional
    (buf10 buf20 : W8.t Array1152.t) :
  hoare [Verify.verify :
    arg = (buf10, buf20) ==> res = verify_spec buf10 buf20].
proof.
  conseq (verify_correct_h buf10 buf20) => />.
  rewrite /verify_spec.
  by case (buf10 = buf20) => Heq; smt(w64_zero_neq_one).
qed.

lemma verify_ll : islossless Verify.verify.
proof.
  proc.
  wp; while (0 <= i{hr} <= 1152) (1152 - i{hr}); last by auto => /> /#.
  by auto => /> /#.
qed.

lemma verify_correct
    (buf10 buf20 : W8.t Array1152.t) :
  phoare [Verify.verify :
    arg = (buf10, buf20) ==> res = verify_spec buf10 buf20] = 1%r.
proof. by conseq verify_ll (verify_functional buf10 buf20). qed.
