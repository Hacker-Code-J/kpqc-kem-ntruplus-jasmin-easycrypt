require import AllCore Distr.
from Jasmin require import JWord JModel_x86.

require import Array32.
require import NTRUPlus768DecapFailProof.

(* A target-width shadow of the C expression [buf3[i] & ~(-fail)].
   [fail] is sign-extended from int8_t, the uint8_t source is zero-extended,
   the bitwise operations happen in W32, and the store truncates to W8.  The
   selection theorems use only the predecessor's proved fail values 0 and 1;
   this is not a general C integer-representation equivalence theorem. *)
op decap_mask_word32 (failv : W8.t) : W32.t =
  invw (- MOVSX_u32s8 failv).

op decap_mask_byte (failv : W8.t) : W8.t =
  truncateu8 (decap_mask_word32 failv).

op decap_masked_byte_word32
    (failv src : W8.t) : W32.t =
  zeroextu32 src `&` decap_mask_word32 failv.

op decap_masked_byte_spec
    (failv src : W8.t) : W8.t =
  truncateu8 (decap_masked_byte_word32 failv src).

op decap_mask_ss_spec
    (failv : W8.t) (buf3_prefix : W8.t Array32.t) : W8.t Array32.t =
  Array32.init (fun i => decap_masked_byte_spec failv buf3_prefix.[i]).

op decap_mask_zero_ss : W8.t Array32.t =
  Array32.init (fun _ => W8.zero).

lemma movsx_u32s8_fail_false :
  MOVSX_u32s8 (fail_byte false) = W32.zero.
proof.
  rewrite /MOVSX_u32s8 fail_byte_false.
  rewrite W8.to_sintK_small 1:/#.
  done.
qed.

lemma movsx_u32s8_fail_true :
  MOVSX_u32s8 (fail_byte true) = W32.of_int 1.
proof.
  rewrite /MOVSX_u32s8 fail_byte_true.
  rewrite W8.to_sintK_small 1:/#.
  done.
qed.

lemma invw_zero_is_onew :
  invw W32.zero = W32.onew.
proof.
  apply W32.wordP => i Hi.
  by rewrite W32.invwE W32.zerowE W32.onewE Hi.
qed.

lemma invw_onew_is_zero :
  invw W32.onew = W32.zero.
proof.
  apply W32.wordP => i Hi.
  by rewrite W32.invwE W32.onewE W32.zerowE Hi.
qed.

lemma decap_mask_word32_fail_false :
  decap_mask_word32 (fail_byte false) = W32.onew.
proof.
  rewrite /decap_mask_word32 movsx_u32s8_fail_false.
  rewrite oppr0.
  exact invw_zero_is_onew.
qed.

lemma decap_mask_word32_fail_true :
  decap_mask_word32 (fail_byte true) = W32.zero.
proof.
  rewrite /decap_mask_word32 movsx_u32s8_fail_true.
  rewrite W32.minus_one.
  exact invw_onew_is_zero.
qed.

lemma truncateu8_zeroextu32_id
    (x : W8.t) :
  truncateu8 (zeroextu32 x) = x.
proof.
  apply W8.to_uint_eq.
  rewrite /truncateu8 /zeroextu32 /= !of_uintK /=.
  by smt(W8.to_uint_cmp pow2_8).
qed.

lemma decap_mask_byte_fail_false :
  decap_mask_byte (fail_byte false) = W8.onew.
proof.
  rewrite /decap_mask_byte decap_mask_word32_fail_false.
  apply W8.to_uint_eq.
  rewrite to_uint_truncateu8 /=.
  have H32 : W32.to_uint W32.onew = 2 ^ 32 - 1 by exact W32.to_uint_onew.
  have H8 : W8.to_uint W8.onew = 2 ^ 8 - 1 by exact W8.to_uint_onew.
  rewrite H32 H8.
  by smt().
qed.

lemma decap_mask_byte_fail_true :
  decap_mask_byte (fail_byte true) = W8.zero.
proof.
  rewrite /decap_mask_byte decap_mask_word32_fail_true.
  apply W8.to_uint_eq.
  by rewrite to_uint_truncateu8 /=.
qed.

lemma decap_masked_byte_copy
    (src : W8.t) :
  decap_masked_byte_spec (fail_byte false) src = src.
proof.
  rewrite /decap_masked_byte_spec /decap_masked_byte_word32.
  rewrite decap_mask_word32_fail_false W32.andw1_s.
  exact (truncateu8_zeroextu32_id src).
qed.

lemma decap_masked_byte_zero
    (src : W8.t) :
  decap_masked_byte_spec (fail_byte true) src = W8.zero.
proof.
  rewrite /decap_masked_byte_spec /decap_masked_byte_word32.
  rewrite decap_mask_word32_fail_true W32.andw0.
  apply W8.to_uint_eq.
  by rewrite to_uint_truncateu8 /=.
qed.

lemma decap_mask_ss_copy
    (buf3_prefix : W8.t Array32.t) :
  decap_mask_ss_spec (fail_byte false) buf3_prefix = buf3_prefix.
proof.
  apply Array32.tP => i Hi.
  rewrite /decap_mask_ss_spec Array32.initiE 1:/#.
  exact (decap_masked_byte_copy buf3_prefix.[i]).
qed.

lemma decap_mask_ss_zero
    (buf3_prefix : W8.t Array32.t) :
  decap_mask_ss_spec (fail_byte true) buf3_prefix = decap_mask_zero_ss.
proof.
  apply Array32.tP => i Hi.
  rewrite /decap_mask_ss_spec /decap_mask_zero_ss !Array32.initiE 1,2:/#.
  exact (decap_masked_byte_zero buf3_prefix.[i]).
qed.

lemma decap_mask_ss_select
    (failed : bool) (buf3_prefix : W8.t Array32.t) :
  decap_mask_ss_spec (fail_byte failed) buf3_prefix =
  if failed then decap_mask_zero_ss else buf3_prefix.
proof.
  case failed; smt(decap_mask_ss_copy decap_mask_ss_zero).
qed.

module DecapMask = {
  (* Fixed-array value model of the 32 stores.  Prior destination contents,
     pointer aliasing, and the following C int return are outside this model. *)
  proc mask_ss(buf3_prefix : W8.t Array32.t,
               failv : W8.t) : W8.t Array32.t = {
    var ss : W8.t Array32.t;
    var i : int;

    ss <- Array32.init (fun _ => W8.zero);
    i <- 0;
    while (i < 32) {
      ss.[i] <- decap_masked_byte_spec failv buf3_prefix.[i];
      i <- i + 1;
    }
    return ss;
  }
}.

lemma decap_mask_functional
    (buf3_prefix0 : W8.t Array32.t)
    (failv0 : W8.t) :
  hoare [DecapMask.mask_ss :
    arg = (buf3_prefix0, failv0) ==>
      res = decap_mask_ss_spec failv0 buf3_prefix0].
proof.
  proc.
  wp.
  while (
      0 <= i{hr} <= 32 /\
      failv{hr} = failv0 /\
      buf3_prefix{hr} = buf3_prefix0 /\
      ss{hr} =
        Array32.init (fun k =>
          if 0 <= k < i{hr} then
            decap_masked_byte_spec failv0 buf3_prefix0.[k]
          else
            W8.zero)); last first.
  + auto => />; split; first by smt().
    move=> i Hi0 Hi32 Hexit.
    have Hi : i = 32 by smt().
    apply Array32.tP => k Hk.
    rewrite /decap_mask_ss_spec !Array32.initiE 1,2:/# Hi.
    by smt().
  + auto => /> &hr Hi0 Hi32 Hss.
    split; first by smt().
    apply Array32.tP => k Hk.
    rewrite Array32.initiE 1:/#.
    case (k = i{hr}).
    * move=> ->.
      rewrite get_setE 1:/#.
      have -> : 0 <= i{hr} < i{hr} + 1 by smt().
      by smt().
    * move=> Hneq.
      rewrite get_setE 1:/#.
      rewrite Array32.initiE 1:/#.
      case (0 <= k < i{hr}) => Hcase /=.
      + have -> : 0 <= k < i{hr} + 1 by smt().
        by smt().
      + have -> : ! (0 <= k < i{hr} + 1) by smt().
        by smt().
qed.

lemma decap_mask_selection_h
    (buf3_prefix0 : W8.t Array32.t)
    (failed : bool) :
  hoare [DecapMask.mask_ss :
    arg = (buf3_prefix0, fail_byte failed) ==>
      res = if failed then decap_mask_zero_ss else buf3_prefix0].
proof.
  conseq (decap_mask_functional buf3_prefix0 (fail_byte failed)) => />.
  exact (decap_mask_ss_select failed buf3_prefix0).
qed.

lemma decap_mask_ll :
  islossless DecapMask.mask_ss.
proof.
  proc.
  wp; while (0 <= i{hr} <= 32) (32 - i{hr}); last by auto => /> /#.
  by auto => /> /#.
qed.

lemma decap_mask_correct
    (buf3_prefix0 : W8.t Array32.t)
    (failv0 : W8.t) :
  phoare [DecapMask.mask_ss :
    arg = (buf3_prefix0, failv0) ==>
      res = decap_mask_ss_spec failv0 buf3_prefix0] = 1%r.
proof.
  by conseq decap_mask_ll (decap_mask_functional buf3_prefix0 failv0).
qed.
