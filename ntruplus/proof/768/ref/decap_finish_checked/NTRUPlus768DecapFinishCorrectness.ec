require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array32 Array224 Array1152 NTRUPlus768DecapFinish.
require import NTRUPlus768VerifyProof NTRUPlus768DecapFailProof NTRUPlus768DecapMaskProof.

module Finish = NTRUPlus768DecapFinish.M.

op finish_key_prefix (h : W8.t Array224.t) : W8.t Array32.t =
  Array32.init (fun i => h.[i]).

op finish_ss_spec (h : W8.t Array224.t) (failed : bool) : W8.t Array32.t =
  if failed then decap_mask_zero_ss else finish_key_prefix h.

lemma finish_verify_equiv :
  equiv [Finish.verify_bytes ~ Verify.verify :
    recovered{1} = buf1{2} /\ regenerated{1} = buf2{2} ==> ={res}].
proof.
  proc.
  wp.
  while (recovered{1} = buf1{2} /\ regenerated{1} = buf2{2} /\
    ={acc} /\ W64.to_uint i{1} = i{2} /\ 0 <= i{2} <= 1152).
  + auto => /> &1 hlo hhi hguard hloop.
    rewrite !W64.ultE /=.
    have hn : W64.to_uint (i{1} + W64.one) = W64.to_uint i{1} + 1.
    + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
    rewrite hn; smt().
  auto => />; smt().
qed.

lemma finish_verify_functional r0 r1 :
  hoare [Finish.verify_bytes : arg = (r0,r1) ==> res = verify_spec r0 r1].
proof. conseq finish_verify_equiv (verify_functional r0 r1); smt(). qed.

lemma finish_verify_ll : islossless Finish.verify_bytes.
proof. conseq finish_verify_equiv verify_ll; smt(). qed.

lemma finish_combine df r0 r1 :
  (truncateu32 (verify_spec r0 r1) `|` W32.of_int (b2i df)) =
    W32.of_int (b2i (df \/ r0 <> r1)).
proof.
  rewrite /verify_spec.
  case df; case (r0 = r1) => /=; rewrite /truncateu32 /=; done.
qed.

lemma finish_mask_byte (b : W8.t) (failed : bool) :
  b `&` truncateu8 (invw (- W32.of_int (b2i failed))) =
    if failed then W8.zero else b.
proof.
  case failed => hf; rewrite /b2i /=.
  + have h : invw (- W32.one) = W32.zero.
    + by rewrite W32.minus_one invw_onew_is_zero.
    by rewrite h /truncateu8 /=.
  have h : invw (- W32.zero) = W32.onew.
  + by rewrite oppr0 invw_zero_is_onew.
  rewrite h.
  have ht : truncateu8 W32.onew = W8.onew.
  + apply W8.to_uint_eq.
    by rewrite to_uint_truncateu8 W32.to_uint_onew W8.to_uint_onew /=.
  by rewrite ht W8.andw1_s.
qed.

lemma finish_functional ss0 h0 r0 r1 (df : bool) :
  hoare [Finish.jade_ntruplus_ntruplus768_amd64_ref_decap_finish :
    arg = (ss0,h0,r0,r1,W32.of_int (b2i df)) ==>
    res = (finish_ss_spec h0 (df \/ r0 <> r1),
           W32.of_int (b2i (df \/ r0 <> r1)))].
proof.
  proc.
  seq 2 : (ss = ss0 /\ hashout = h0 /\ decode_fail = W32.of_int (b2i df) /\
           comparison = verify_spec r0 r1).
  + call (finish_verify_functional r0 r1); auto.
  while (hashout = h0 /\
    failed = W32.of_int (b2i (df \/ r0 <> r1)) /\
    mask = invw (- W32.of_int (b2i (df \/ r0 <> r1))) /\
    0 <= W64.to_uint i <= 32 /\
    forall j, 0 <= j < W64.to_uint i =>
      ss.[j] = if df \/ r0 <> r1 then W8.zero else h0.[j]); last first.
  + auto => />.
    rewrite finish_combine /=.
    split; first smt().
    move=> i1 ss1 hdone hlo hhi hprefix.
    rewrite W64.ultE /= in hdone.
    have hi : W64.to_uint i1 = 32 by smt().
    apply Array32.tP => j hj.
    rewrite /finish_ss_spec /finish_key_prefix /decap_mask_zero_ss.
    case (df \/ r0 <> r1) => hf; rewrite Array32.initiE //.
    + by rewrite (hprefix j _) 1:/# hf.
    by rewrite (hprefix j _) 1:/# hf.
  auto => /> &hr hlo hhi hprefix hloop.
  rewrite W64.ultE /= in hloop.
  have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  rewrite hn finish_mask_byte.
  split; first smt().
  move=> j hjlo hjhi.
  rewrite Array32.get_setE 1:/# /=; smt().
qed.

lemma finish_ll : islossless
  Finish.jade_ntruplus_ntruplus768_amd64_ref_decap_finish.
proof.
  proc.
  while (0 <= W64.to_uint i <= 32) (32 - W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  wp; call finish_verify_ll; auto => />.
  move=> i hlo hhi hd; rewrite W64.ultE /=; smt().
qed.

lemma finish_correct ss0 h0 r0 r1 (df : bool) :
  phoare [Finish.jade_ntruplus_ntruplus768_amd64_ref_decap_finish :
    arg = (ss0,h0,r0,r1,W32.of_int (b2i df)) ==>
    res = (finish_ss_spec h0 (df \/ r0 <> r1),
           W32.of_int (b2i (df \/ r0 <> r1)))] = 1%r.
proof. by conseq finish_ll (finish_functional ss0 h0 r0 r1 df). qed.

lemma finish_ss_existing_mask h failed :
  finish_ss_spec h failed =
    decap_mask_ss_spec (fail_byte failed) (finish_key_prefix h).
proof. by rewrite decap_mask_ss_select /finish_ss_spec. qed.

lemma finish_flag_binary (failed : bool) :
  W32.of_int (b2i failed) = W32.zero \/
  W32.of_int (b2i failed) = W32.one.
proof. by case failed => h; rewrite /b2i /=. qed.

lemma finish_flag_zero_iff (failed : bool) :
  W32.of_int (b2i failed) = W32.zero <=> !failed.
proof.
  by case failed => h; rewrite /b2i /= ?W32.to_uint_eq /=.
qed.

lemma finish_acceptance_h ss0 h0 r0 r1 (df : bool) :
  hoare [Finish.jade_ntruplus_ntruplus768_amd64_ref_decap_finish :
    arg = (ss0,h0,r0,r1,W32.of_int (b2i df)) ==>
    (res.`2 = W32.zero \/ res.`2 = W32.one) /\
    (res.`2 = W32.zero <=> !df /\ r0 = r1) /\
    (df \/ r0 <> r1 => res.`1 = decap_mask_zero_ss) /\
    (!df /\ r0 = r1 => res.`1 = finish_key_prefix h0)].
proof.
  conseq (finish_functional ss0 h0 r0 r1 df) => />.
  rewrite finish_flag_binary finish_flag_zero_iff /=.
  by case (df \/ r0 <> r1) => hf; smt().
qed.

(* Arbitrary [ss0] makes independence from incoming destination contents
   explicit. This value-level theorem does not model native pointer aliasing,
   external SHAKE, or later C temporary-buffer erasure. *)
lemma finish_acceptance_correct ss0 h0 r0 r1 (df : bool) :
  phoare [Finish.jade_ntruplus_ntruplus768_amd64_ref_decap_finish :
    arg = (ss0,h0,r0,r1,W32.of_int (b2i df)) ==>
    (res.`2 = W32.zero \/ res.`2 = W32.one) /\
    (res.`2 = W32.zero <=> !df /\ r0 = r1) /\
    (df \/ r0 <> r1 => res.`1 = decap_mask_zero_ss) /\
    (!df /\ r0 = r1 => res.`1 = finish_key_prefix h0)] = 1%r.
proof. by conseq finish_ll (finish_acceptance_h ss0 h0 r0 r1 df). qed.
