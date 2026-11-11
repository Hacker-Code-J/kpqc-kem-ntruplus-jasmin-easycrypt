require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array1153 Array2304 Array32 Array192 Array96.
require import NTRUPlus768DecapMessagePrepareProof NTRUPlus768DecapMessageSpec NTRUPlus768DecapMessageProof.
require import NTRUPlus768DecapR2CompCaller NTRUPlus768DecapR2CompSpec NTRUPlus768DecapR2CompAlgebra.
require import NTRUPlus768DecapCandidateSpec NTRUPlus768DecapCandidateAlgebra.
require import NTRUPlus768DecapGuardSpec NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.
require import NTRUPlus768DecapR2Bridge NTRUPlus768PolyToBytesProof NTRUPlus768PolyToBytesAlgebra.
require import NTRUPlus768PolySOTPDecodeAlgebra.

require import NTRUPlus768DecapMessageAlgebra.

module GuardedMessage(H : MessageSHAKE) = {
  proc run(serialized : W8.t Array1152.t, input : W8.t Array1153.t,
      msg : W8.t Array96.t, rp mp cp fp hp : W16.t Array768.t,
      ss : W8.t Array32.t, ct : W8.t Array1152.t, skpoly : W8.t Array2304.t) :
      W8.t Array1152.t * W8.t Array96.t * W8.t Array32.t * W32.t = {
    var status : W32.t;
    (rp,mp,ss,status) <@ GuardedR2.run(rp,mp,cp,fp,hp,ss,ct,skpoly);
    if (status = W32.zero) {
      (serialized,msg,status) <@ DecapMessage(H).run(serialized,input,msg,rp,mp);
    }
    return (serialized,msg,ss,status);
  }
}.

lemma guarded_message_accept_functional (H <: MessageSHAKE)
    bs0 input0 msg0 rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0 :
  (forall input0, hoare [H.shake : input = input0 ==> res = message_shake_spec input0]) =>
  decap_guard_accepts ct0 (decap_fbytes sk0) (decap_hbytes sk0) =>
  hoare [GuardedMessage(H).run :
    serialized = bs0 /\ input = input0 /\ msg = msg0 /\
    rp = rp0 /\ mp = mp0 /\ cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 ==>
    (res.`1,res.`2,res.`4) = decap_message_spec (message_r2 ct0 sk0) (message_candidate ct0 sk0) /\
    res.`3 = ss0].
proof.
  move=> hh ha.
  have [hr hm] := message_caller_input_closure ct0 sk0 ha.
  proc; rcondt 2.
  + call (guarded_r2_functional rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0).
    auto => />; by rewrite /guarded_r2_spec ha.
  call (decap_message_functional H bs0 input0 msg0 (message_r2 ct0 sk0) (message_candidate ct0 sk0) hh hr hm).
  call (guarded_r2_functional rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0).
  auto => />; by rewrite /guarded_r2_spec ha /message_r2 /message_candidate.
qed.

lemma guarded_message_lossless (H <: MessageSHAKE) :
  islossless H.shake => islossless GuardedMessage(H).run.
proof.
  move=> hl; proc.
  seq 1 : true.
  + ecall (guarded_r2_functional rp mp cp fp hp ss ct skpoly); auto.
  + call guarded_r2_lossless; auto.
  + if; [call (decap_message_lossless H hl) | ]; auto.
  + hoare; ecall (guarded_r2_functional rp mp cp fp hp ss ct skpoly); auto.
  auto.
qed.

lemma guarded_message_accept (H <: MessageSHAKE)
    bs0 input0 msg0 rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0 :
  (forall input0, hoare [H.shake : input = input0 ==> res = message_shake_spec input0]) =>
  islossless H.shake =>
  decap_guard_accepts ct0 (decap_fbytes sk0) (decap_hbytes sk0) =>
  phoare [GuardedMessage(H).run :
    serialized = bs0 /\ input = input0 /\ msg = msg0 /\
    rp = rp0 /\ mp = mp0 /\ cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 ==>
    (res.`1,res.`2,res.`4) = decap_message_spec (message_r2 ct0 sk0) (message_candidate ct0 sk0) /\
    res.`3 = ss0] = 1%r.
proof.
  move=> hh hl ha; by conseq (guarded_message_lossless H hl)
    (guarded_message_accept_functional H bs0 input0 msg0 rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0 hh ha).
qed.

(* Entry rejection skips SHAKE without requiring it to terminate. The
   preserved message buffer is distinct from SOTP rejection's zero message. *)
lemma guarded_message_reject (H <: MessageSHAKE)
    bs0 input0 msg0 rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0 &m :
  ! decap_guard_accepts ct0 (decap_fbytes sk0) (decap_hbytes sk0) =>
  phoare [GuardedMessage(H).run :
    serialized = bs0 /\ input = input0 /\ msg = msg0 /\
    rp = rp0 /\ mp = mp0 /\ cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 /\
    (glob H) = (glob H){m} ==>
    res = (bs0,msg0,encap_zero_ss,W32.one) /\ (glob H) = (glob H){m}] = 1%r.
proof.
  move=> hb; proc; rcondf 2.
  + call (guarded_r2_functional rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0).
    auto => />; rewrite /guarded_r2_spec hb; smt(W32.to_uint0 W32.to_uint1).
  call (guarded_r2_reject rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0 hb); by auto.
qed.
