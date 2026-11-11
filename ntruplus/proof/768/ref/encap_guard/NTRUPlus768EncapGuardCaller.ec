require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array32 NTRUPlus768EncapGuard.
require import NTRUPlus768EncapGuardSpec NTRUPlus768EncapGuardProof NTRUPlus768CanonicalDecoder.

(* This is an EasyCrypt composition at the guard/continuation boundary.
   It is not the extracted full Encaps API. In particular, it makes no claim
   that the public C API has not consumed randomness before this boundary. *)
module type EncapBody = {
  proc run(hp : W16.t Array768.t, ct : W8.t Array1152.t,
    ss : W8.t Array32.t, pk : W8.t Array1152.t) : W8.t Array1152.t * W8.t Array32.t
}.

module EncapGuardedCaller(Body : EncapBody) = {
  proc run(hp : W16.t Array768.t, ct : W8.t Array1152.t,
      ss : W8.t Array32.t, pk : W8.t Array1152.t) :
      W16.t Array768.t * W8.t Array1152.t * W8.t Array32.t * W32.t = {
    var status : W32.t;
    (hp, ct, ss, status) <@ NTRUPlus768EncapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_encap_guard(hp,ct,ss,pk);
    if (status = W32.zero) {
      (ct, ss) <@ Body.run(hp,ct,ss,pk);
    }
    return (hp,ct,ss,status);
  }
}.

(* The comparison program dispatches exactly one abstract Body call. No
   termination assumption on that arbitrary continuation is used by equiv. *)
module EncapDirectCaller(Body : EncapBody) = {
  proc run(hp : W16.t Array768.t, ct : W8.t Array1152.t,
      ss : W8.t Array32.t, pk : W8.t Array1152.t) :
      W16.t Array768.t * W8.t Array1152.t * W8.t Array32.t * W32.t = {
    hp <- decoded_poly pk;
    (ct, ss) <@ Body.run(hp,ct,ss,pk);
    return (hp,ct,ss,W32.zero);
  }
}.

lemma encap_caller_rejection_preserves_body (Body <: EncapBody) hp0 ct0 ss0 pk0 &m :
  ! (encap_key_canonical pk0) =>
  phoare [EncapGuardedCaller(Body).run :
    hp = hp0 /\ ct = ct0 /\ ss = ss0 /\ pk = pk0 /\ (glob Body) = (glob Body){m} ==>
    res = (decoded_poly pk0, encap_zero_ct, encap_zero_ss, W32.one) /\
    (glob Body) = (glob Body){m}] = 1%r.
proof.
  move=> hbad; proc.
  rcondf 2.
  + call (encap_guard_reject_functional hp0 ct0 ss0 pk0 hbad).
    auto => />; smt(W32.to_uint0 W32.to_uint1).
  call (encap_guard_noncanonical_reject hp0 ct0 ss0 pk0 hbad).
  by auto.
qed.

lemma encap_caller_valid_dispatch (Body <: EncapBody) :
  equiv [EncapGuardedCaller(Body).run ~ EncapDirectCaller(Body).run :
    ={hp,ct,ss,pk,glob Body} /\ encap_key_canonical pk{1} ==>
    ={res,glob Body}].
proof.
  proc.
  rcondt{1} 2.
  + move=> &2; ecall (encap_guard_functional hp ct ss pk).
    auto => />; rewrite /encap_guard_spec /encap_status; smt().
  call (_ : true).
  wp.
  ecall{1} (encap_guard_correct hp{1} ct{1} ss{1} pk{1}).
  auto => />; rewrite /encap_guard_spec /encap_status; smt().
qed.
