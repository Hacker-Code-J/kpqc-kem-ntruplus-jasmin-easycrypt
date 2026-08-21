require import AllCore Distr.
from Jasmin require import JWord.

op fail_byte (b : bool) : W8.t =
  W8.of_int (b2i b).

op fail_word (b : bool) : W64.t =
  W64.of_int (b2i b).

op decap_fail_word_spec
    (decode_fail_byte : W8.t) (compare_result : W64.t) : W8.t =
  truncateu8 ((zeroextu64 decode_fail_byte) `|` compare_result).

op decap_fail_spec_bool
    (decode_failed compare_failed : bool) : W8.t =
  fail_byte (decode_failed \/ compare_failed).

lemma fail_byte_false :
  fail_byte false = W8.of_int 0.
proof. by rewrite /fail_byte. qed.

lemma fail_byte_true :
  fail_byte true = W8.of_int 1.
proof. by rewrite /fail_byte. qed.

lemma fail_word_false :
  fail_word false = W64.of_int 0.
proof. by rewrite /fail_word. qed.

lemma fail_word_true :
  fail_word true = W64.of_int 1.
proof. by rewrite /fail_word. qed.

lemma truncateu8_fail_word (b : bool) :
  truncateu8 (fail_word b) = fail_byte b.
proof.
  case b.
  + rewrite /fail_word /fail_byte /truncateu8 /= !of_uintK /=.
    done.
  + rewrite /fail_word /fail_byte /truncateu8 /= !of_uintK /=.
    done.
qed.

lemma zeroextu64_fail_byte (b : bool) :
  zeroextu64 (fail_byte b) = fail_word b.
proof.
  case b.
  + rewrite fail_byte_true fail_word_true W64.to_uint_eq.
    by rewrite to_uint_zeroextu64 !of_uintK /=.
  + rewrite fail_byte_false fail_word_false W64.to_uint_eq.
    by rewrite to_uint_zeroextu64 !of_uintK /=.
qed.

lemma fail_byte_or
    (decode_failed compare_failed : bool) :
  fail_byte decode_failed `|` fail_byte compare_failed =
  fail_byte (decode_failed \/ compare_failed).
proof.
  case decode_failed; case compare_failed => /=.
  + done.
  + rewrite fail_byte_false fail_byte_true /=.
    done.
  + rewrite fail_byte_true fail_byte_false /=.
    done.
  + done.
qed.

lemma fail_word_or
    (decode_failed compare_failed : bool) :
  fail_word decode_failed `|` fail_word compare_failed =
  fail_word (decode_failed \/ compare_failed).
proof.
  case decode_failed; case compare_failed => /=.
  + done.
  + rewrite fail_word_false fail_word_true /=.
    done.
  + rewrite fail_word_true fail_word_false /=.
    done.
  + done.
qed.

lemma decap_fail_word_spec_bool
    (decode_failed compare_failed : bool) :
  decap_fail_word_spec
    (fail_byte decode_failed)
    (fail_word compare_failed) =
  decap_fail_spec_bool decode_failed compare_failed.
proof.
  rewrite /decap_fail_word_spec /decap_fail_spec_bool.
  by rewrite zeroextu64_fail_byte fail_word_or truncateu8_fail_word.
qed.

lemma decap_fail_spec_range
    (decode_failed compare_failed : bool) :
  decap_fail_spec_bool decode_failed compare_failed = W8.of_int 0 \/
  decap_fail_spec_bool decode_failed compare_failed = W8.of_int 1.
proof.
  case decode_failed; case compare_failed => /=;
  by rewrite ?fail_byte_false ?fail_byte_true.
qed.

lemma decap_fail_spec_zero_iff
    (decode_failed compare_failed : bool) :
  decap_fail_spec_bool decode_failed compare_failed = W8.of_int 0 <=>
  ! decode_failed /\ ! compare_failed.
proof.
  case decode_failed; case compare_failed => /=; smt().
qed.

lemma decap_fail_spec_one_iff
    (decode_failed compare_failed : bool) :
  decap_fail_spec_bool decode_failed compare_failed = W8.of_int 1 <=>
  decode_failed \/ compare_failed.
proof.
  case decode_failed; case compare_failed => /=; smt().
qed.

lemma decap_fail_spec_to_uint
    (decode_failed compare_failed : bool) :
  W8.to_uint (decap_fail_spec_bool decode_failed compare_failed) =
  b2i (decode_failed \/ compare_failed).
proof.
  case decode_failed; case compare_failed => /=;
  by rewrite ?fail_byte_false ?fail_byte_true.
qed.

module DecapFail = {
  (* This models only the decapsulation failure-byte composition boundary:
     the stored int8_t failure byte from poly_sotp_decode, the promoted
     uint64 compare result from verify, and the truncating OR update.
     The proof relies on both operands already being 0/1 and does not claim
     full C integer-promotion, aliasing, or binary-equivalence correctness. *)
  proc combine(decode_fail_byte : W8.t,
               compare_result : W64.t) : W8.t = {
    var failv : W8.t;

    failv <- truncateu8 ((zeroextu64 decode_fail_byte) `|` compare_result);
    return failv;
  }
}.

lemma decap_fail_functional
    (decode_failed compare_failed : bool) :
  hoare [DecapFail.combine :
    arg = (fail_byte decode_failed, fail_word compare_failed) ==>
      res = decap_fail_spec_bool decode_failed compare_failed].
proof.
  proc.
  wp.
  skip => />.
  exact (decap_fail_word_spec_bool decode_failed compare_failed).
qed.

lemma decap_fail_correct_h
    (decode_failed compare_failed : bool) :
  hoare [DecapFail.combine :
    arg = (fail_byte decode_failed, fail_word compare_failed) ==>
      (res = W8.of_int 0 <=> ! decode_failed /\ ! compare_failed) /\
      (res = W8.of_int 1 <=> decode_failed \/ compare_failed)].
proof.
  conseq (decap_fail_functional decode_failed compare_failed) => />.
  by rewrite decap_fail_spec_zero_iff decap_fail_spec_one_iff.
qed.

lemma decap_fail_ll :
  islossless DecapFail.combine.
proof.
  proc.
  auto.
qed.

lemma decap_fail_correct
    (decode_failed compare_failed : bool) :
  phoare [DecapFail.combine :
    arg = (fail_byte decode_failed, fail_word compare_failed) ==>
      res = decap_fail_spec_bool decode_failed compare_failed] = 1%r.
proof.
  by conseq decap_fail_ll (decap_fail_functional decode_failed compare_failed).
qed.
