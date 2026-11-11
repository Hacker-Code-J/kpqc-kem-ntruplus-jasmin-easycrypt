require import AllCore IntDiv List.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152.
require NTRUPlus768PolyFromBytesAlgebra NTRUPlus768PolyToBytesAlgebra.

(* Arithmetic model of the canonical-validation additions in the official
   3991b2a NTRU+768 reference poly_frombytes. This is a validation-component
   proof, not a C-AST/Jasmin extraction theorem or an IND-CCA reduction. *)
abbrev decoded_even = NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_even_int.
abbrev decoded_odd = NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_odd_int.
abbrev decoded_coeff = NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_int.
abbrev decoded_poly = NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec.

op canonical_sub (t : int) : W32.t = W32.of_int 3456 - W32.of_int t.

lemma canonical_sub_uint t : 0 <= t < 4096 =>
  W32.to_uint (canonical_sub t) =
    if t < 3457 then 3456 - t else 4294967296 + 3456 - t.
proof.
  move=> ht; rewrite /canonical_sub W32.of_intS' W32.of_uintK /=.
  case (t < 3457) => hc.
  + rewrite modz_small; smt().
  rewrite -(modzDl (3456 - t) 4294967296).
  rewrite modz_small; smt().
qed.

lemma canonical_sub_high t : 0 <= t < 4096 =>
  (canonical_sub t).[31] = (3457 <= t).
proof.
  move=> ht; rewrite W32.get_to_uint (canonical_sub_uint t ht) /=.
  case (t < 3457) => hc /=.
  + rewrite divz_small; smt().
  have hd : (4294967296 + 3456 - t) %/ 2147483648 = 1.
  + rewrite divz_eqP; smt().
  rewrite hd /=; smt().
qed.

lemma canonical_shift31_bit (w : W32.t) :
  W32.to_uint (w `>>>` 31) = b2i w.[31].
proof.
  rewrite W32.to_uint_shr 1:// W32.b2i_get 1:// /=.
  have /= hw := W32.to_uint_cmp w.
  rewrite modz_small; smt(divz_cmp).
qed.

lemma canonical_or_high (x y : W32.t) :
  (x `|` y).[31] = (x.[31] \/ y.[31]).
proof. by rewrite W32.orwE. qed.

(* One iteration is the two consecutive fail |= ... statements in the C loop. *)
op canonical_acc (a : W8.t Array1152.t) (n : int) : W32.t =
  foldl (fun flags i =>
    (flags `|` canonical_sub (decoded_even a i)) `|`
      canonical_sub (decoded_odd a i)) W32.zero (iota_ 0 n).

op canonical_prefix (a : W8.t Array1152.t) (n : int) : bool =
  forall i, 0 <= i < n => decoded_even a i < 3457 /\ decoded_odd a i < 3457.

lemma canonical_acc0 a : canonical_acc a 0 = W32.zero.
proof. by rewrite /canonical_acc iota0. qed.

lemma canonical_accS a n : 0 <= n =>
  canonical_acc a (n + 1) =
    (canonical_acc a n `|` canonical_sub (decoded_even a n)) `|`
      canonical_sub (decoded_odd a n).
proof. by move=> hn; rewrite /canonical_acc iotaSr 1:hn foldl_rcons /=. qed.

lemma canonical_prefix0 a : canonical_prefix a 0.
proof. rewrite /canonical_prefix; smt(). qed.

lemma canonical_prefixS a n : 0 <= n =>
  canonical_prefix a (n + 1) =
    (canonical_prefix a n /\ decoded_even a n < 3457 /\ decoded_odd a n < 3457).
proof. move=> hn; rewrite /canonical_prefix; smt(). qed.

lemma canonical_acc_high a n : 0 <= n => n <= 384 =>
  (!(canonical_acc a n).[31]) = canonical_prefix a n.
proof.
  move: n; apply intind.
  + by rewrite /= canonical_acc0 W32.zerowE canonical_prefix0.
  move=> n hn ih; rewrite /= in ih; rewrite /= => hcap.
  have hi : 0 <= n < 384 by smt().
  have he := NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_even_int_range a n hi.
  have ho := NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_odd_int_range a n hi.
  have hprev := ih _; first smt().
  rewrite canonical_accS 1:hn !canonical_or_high
    (canonical_sub_high _ he) (canonical_sub_high _ ho)
    canonical_prefixS 1:hn.
  rewrite !negb_or hprev.
  move: (canonical_prefix a n) (decoded_even a n) (decoded_odd a n) => b x y.
  clear ih hcap hi he ho hprev hn a n.
  smt().
qed.

lemma decoded_even_index a i :
  decoded_coeff a (2 * i) = decoded_even a i.
proof.
  rewrite /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_int.
  have hm : (2 * i) %% 2 = 0 by smt().
  have hd : (2 * i) %/ 2 = i by smt().
  by rewrite hm hd.
qed.

lemma decoded_odd_index a i :
  decoded_coeff a (2 * i + 1) = decoded_odd a i.
proof.
  rewrite /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_int.
  have hm : (2 * i + 1) %% 2 = 1 by smt().
  have hd : (2 * i + 1) %/ 2 = i by smt().
  by rewrite hm hd.
qed.

lemma canonical_prefix_all a :
  canonical_prefix a 384 = (forall j, 0 <= j < 768 => decoded_coeff a j < 3457).
proof.
  rewrite eq_iff; split.
  + move=> hp j hj.
    have hi : 0 <= j %/ 2 < 384 by smt().
    have h := hp (j %/ 2) hi.
    rewrite /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_int.
    smt().
  move=> hp i hi.
  have he := hp (2 * i) _; first smt().
  have ho := hp (2 * i + 1) _; first smt().
  rewrite decoded_even_index in he; rewrite decoded_odd_index in ho.
  by split.
qed.

op canonical_return (a : W8.t Array1152.t) : int =
  W32.to_uint (canonical_acc a 384 `>>>` 31).

lemma canonical_return_binary a : canonical_return a = 0 \/ canonical_return a = 1.
proof. rewrite /canonical_return canonical_shift31_bit; smt(b2i0 b2i1). qed.

lemma canonical_return_success_iff a :
  canonical_return a = 0 <=>
    forall j, 0 <= j < 768 => W16.to_uint (decoded_poly a).[j] < 3457.
proof.
  have h := canonical_acc_high a 384 _ _; first 2 trivial.
  rewrite canonical_prefix_all in h.
  rewrite /canonical_return canonical_shift31_bit.
  have he : (forall j, 0 <= j < 768 => W16.to_uint (decoded_poly a).[j] < 3457) =
      (forall j, 0 <= j < 768 => decoded_coeff a j < 3457).
  + rewrite eq_iff; split => hp j hj.
    - have hjp := hp j hj.
      by rewrite NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec_coeff_uint 1:hj in hjp.
    rewrite NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec_coeff_uint 1:hj.
    exact (hp j hj).
  by rewrite he b2i_eq0 h.
qed.

(* The repository contains the same 12-bit decoder specification in the
   frombytes and tobytes developments. Keep this bridge explicit. *)
lemma canonical_decoder_specs_agree a :
  decoded_poly a = NTRUPlus768PolyToBytesAlgebra.poly_frombytes_spec a.
proof.
  by rewrite /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_spec
    /NTRUPlus768PolyToBytesAlgebra.poly_frombytes_spec
    /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_int
    /NTRUPlus768PolyToBytesAlgebra.poly_frombytes_int
    /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_even_int
    /NTRUPlus768PolyToBytesAlgebra.poly_frombytes_even_int
    /NTRUPlus768PolyFromBytesAlgebra.poly_frombytes_odd_int
    /NTRUPlus768PolyToBytesAlgebra.poly_frombytes_odd_int.
qed.

lemma canonical_tobytes_roundtrip (p : W16.t Array768.t) :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p =>
  decoded_poly (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p) =
    NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec p /\
  canonical_return (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p) = 0.
proof.
  move=> hp.
  have hr := NTRUPlus768PolyToBytesAlgebra.poly_frombytes_poly_tobytes_roundtrip p hp.
  split.
  + by rewrite canonical_decoder_specs_agree hr.
  rewrite canonical_return_success_iff => j hj.
  rewrite canonical_decoder_specs_agree hr
    /NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_spec
    Array768.initiE 1:hj W16.of_uintK /=.
  have hc := NTRUPlus768PolyToBytesAlgebra.poly_tobytes_canonical_coeff_range p j hp hj.
  rewrite /NTRUPlus768BasemulAlgebra.q in hc.
  rewrite modz_small; smt().
qed.

(* A manually written EasyCrypt loop for the validation accumulator only.
   Its coefficient expressions are the existing arithmetic decoder spec.
   Binding this model to extracted official Jasmin/C remains a separate task. *)
module CanonicalCheck = {
  proc run(a : W8.t Array1152.t) : int = {
    var i : int;
    var flags : W32.t;
    i <- 0;
    flags <- W32.zero;
    while (i < 384) {
      flags <- flags `|` canonical_sub (decoded_even a i);
      flags <- flags `|` canonical_sub (decoded_odd a i);
      i <- i + 1;
    }
    return W32.to_uint (flags `>>>` 31);
  }
}.

lemma canonical_check_functional a0 :
  hoare [CanonicalCheck.run : a = a0 ==> res = canonical_return a0].
proof.
  proc.
  while (a = a0 /\ 0 <= i <= 384 /\ flags = canonical_acc a0 i).
  + auto => /> &hr hi0 hi384 hguard.
    rewrite canonical_accS 1:hi0; smt().
  auto => />.
  rewrite canonical_acc0; split; first trivial.
  move=> i0 hdone hi0 hi384.
  have hi : i0 = 384 by smt().
  by rewrite hi /canonical_return.
qed.

lemma canonical_check_lossless : islossless CanonicalCheck.run.
proof.
  proc.
  while (0 <= i <= 384) (384 - i).
  + move=> z; auto => />; smt().
  auto => />; smt().
qed.

lemma canonical_check_success a0 :
  phoare [CanonicalCheck.run : a = a0 ==>
    (res = 0 <=> forall j, 0 <= j < 768 =>
      W16.to_uint (decoded_poly a0).[j] < 3457) /\
    (res = 0 \/ res = 1)] = 1%r.
proof.
  conseq canonical_check_lossless (canonical_check_functional a0) => />.
  split; last exact (canonical_return_binary a0).
  split.
  + move=> hz j hj0 hj768.
    have hall := iffLR _ _ (canonical_return_success_iff a0) hz.
    apply hall; by split.
  exact (iffRL _ _ (canonical_return_success_iff a0)).
qed.

lemma canonical_check_tobytes_success p :
  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p =>
  phoare [CanonicalCheck.run :
    a = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p ==> res = 0] = 1%r.
proof.
  move=> hp.
  have [_ hs] := canonical_tobytes_roundtrip p hp.
  conseq canonical_check_lossless
    (canonical_check_functional (NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p)) => />.
qed.
