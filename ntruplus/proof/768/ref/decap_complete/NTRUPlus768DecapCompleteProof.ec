require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array2336 Array2304 Array1152 Array32 Array96 Array192 Array224 Array768 Array13506.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768DecapCompleteHash NTRUPlus768DecapCompleteTailProof.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapMessageProof NTRUPlus768DecapMessageAlgebra.
require import NTRUPlus768DecapR2CompCaller NTRUPlus768DecapGuardSpec NTRUPlus768EncapGuardSpec.
require import NTRUPlus768DecapClear NTRUPlus768DecapClearProof NTRUPlus768DecapHashHBridge.

lemma complete_guarded_prefix ct sk :
  guarded_r2_spec witness witness encap_zero_ss ct (complete_sk_poly sk) =
  if complete_entry_accepts ct sk then
    (message_r2 ct (complete_sk_poly sk),message_candidate ct (complete_sk_poly sk),encap_zero_ss,W32.zero)
  else (witness,witness,encap_zero_ss,W32.one).
proof.
  by rewrite /guarded_r2_spec /complete_entry_accepts /message_r2 /message_candidate.
qed.

lemma complete_prefix_message ct sk :
  decap_message_spec (message_r2 ct (complete_sk_poly sk)) (message_candidate ct (complete_sk_poly sk)) =
  complete_message_result ct sk.
proof. by rewrite /complete_message_result. qed.

(* The guard status alone controls the early exit. A later SOTP failure is
   always passed through HashH/regeneration to the final shared-key mask. *)
module CompleteCore(G : MessageSHAKE, H : CompleteSHAKEH) = {
  proc run(ct : W8.t Array1152.t, sk : W8.t Array2336.t) : W8.t Array32.t * W32.t = {
    var rp,mp : W16.t Array768.t;
    var ss : W8.t Array32.t;
    var status : W32.t;
    var bs : W8.t Array1152.t;
    var msg : W8.t Array96.t;
    (rp,mp,ss,status) <@ GuardedR2.run(witness,witness,witness,witness,witness,encap_zero_ss,ct,complete_sk_poly sk);
    if (status=W32.zero) {
      (bs,msg,status) <@ DecapMessage(G).run(witness,witness,witness,rp,mp);
      (ss,status) <@ CompleteTail(H).run(bs,msg,status,complete_sk_suffix sk);
    }
    return (ss,status);
  }
}.

lemma complete_core_functional (G <: MessageSHAKE) (H <: CompleteSHAKEH) ct0 sk0 :
  (forall input0, hoare [G.shake : input=input0 ==> res=message_shake_spec input0]) =>
  (forall input0, hoare [H.shake : input=input0 ==> res=complete_shake_h_spec input0]) =>
  hoare [CompleteCore(G,H).run : ct=ct0 /\ sk=sk0 ==> res=complete_spec ct0 sk0].
proof.
  move=> hg hh; case (complete_entry_accepts ct0 sk0) => ha.
  + have [hr hm] := message_caller_input_closure ct0 (complete_sk_poly sk0) ha.
    proc; rcondt 2.
    - call (guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly sk0)).
      auto => />; by rewrite complete_guarded_prefix ha.
    call (complete_tail_functional H (complete_message_result ct0 sk0).`1
      (complete_message_result ct0 sk0).`2 (complete_sotp_failed ct0 sk0) (complete_sk_suffix sk0) hh).
    call (decap_message_functional G witness witness witness
      (message_r2 ct0 (complete_sk_poly sk0)) (message_candidate ct0 (complete_sk_poly sk0)) hg hr hm).
    call (guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly sk0)).
    auto => />.
    rewrite complete_guarded_prefix ha /= complete_prefix_message complete_message_status /complete_spec ha.
    by rewrite -pairS.
  proc; rcondf 2.
  + call (guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly sk0)).
    auto => />; rewrite complete_guarded_prefix ha; smt(W32.to_uint0 W32.to_uint1).
  call (guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly sk0)).
  auto => />; by rewrite complete_guarded_prefix ha /complete_spec ha.
qed.

lemma complete_core_lossless (G <: MessageSHAKE) (H <: CompleteSHAKEH) :
  islossless G.shake => islossless H.shake => islossless CompleteCore(G,H).run.
proof.
  move=> gl hl; proc; seq 1 : true.
  + ecall (guarded_r2_functional witness witness witness witness witness encap_zero_ss ct (complete_sk_poly sk)); auto.
  + call guarded_r2_lossless; auto.
  + if; [call (complete_tail_lossless H hl); call (decap_message_lossless G gl) | ]; auto.
  + hoare; ecall (guarded_r2_functional witness witness witness witness witness encap_zero_ss ct (complete_sk_poly sk)); auto.
  auto.
qed.

(* The cleanup call always executes. The returned array represents the
   designated caller workspace after clearing; it does not encode a proof of
   C pointer aliasing, spills, registers, or all compiler-generated storage. *)
module CompleteDecaps(G : MessageSHAKE, H : CompleteSHAKEH) = {
  proc run(ct : W8.t Array1152.t, sk : W8.t Array2336.t,
      workspace : W8.t Array13506.t) : W8.t Array32.t * W32.t * W8.t Array13506.t = {
    var ss : W8.t Array32.t;
    var status : W32.t;
    (ss,status) <@ CompleteCore(G,H).run(ct,sk);
    workspace <@ NTRUPlus768DecapClear.M.jade_ntruplus_ntruplus768_amd64_ref_decap_clear(workspace);
    return (ss,status,workspace);
  }
}.

lemma complete_functional (G <: MessageSHAKE) (H <: CompleteSHAKEH) ct0 sk0 workspace0 :
  (forall input0, hoare [G.shake : input=input0 ==> res=message_shake_spec input0]) =>
  (forall input0, hoare [H.shake : input=input0 ==> res=complete_shake_h_spec input0]) =>
  hoare [CompleteDecaps(G,H).run : ct=ct0 /\ sk=sk0 /\ workspace=workspace0 ==>
    (res.`1,res.`2)=complete_spec ct0 sk0 /\ res.`3=clear_zero_spec].
proof.
  move=> hg hh; proc; call (decap_clear_functional workspace0);
    call (complete_core_functional G H ct0 sk0 hg hh); auto => />.
  by rewrite -pairS.
qed.

lemma complete_lossless (G <: MessageSHAKE) (H <: CompleteSHAKEH) :
  islossless G.shake => islossless H.shake => islossless CompleteDecaps(G,H).run.
proof.
  move=> gl hl; proc; call decap_clear_lossless; call (complete_core_lossless G H gl hl); by auto.
qed.

lemma complete_correct (G <: MessageSHAKE) (H <: CompleteSHAKEH) ct0 sk0 workspace0 :
  (forall input0, hoare [G.shake : input=input0 ==> res=message_shake_spec input0]) =>
  (forall input0, hoare [H.shake : input=input0 ==> res=complete_shake_h_spec input0]) =>
  islossless G.shake => islossless H.shake =>
  phoare [CompleteDecaps(G,H).run : ct=ct0 /\ sk=sk0 /\ workspace=workspace0 ==>
    (res.`1,res.`2)=complete_spec ct0 sk0 /\ res.`3=clear_zero_spec]=1%r.
proof.
  move=> hg hh gl hl; by conseq (complete_lossless G H gl hl)
    (complete_functional G H ct0 sk0 workspace0 hg hh).
qed.

lemma complete_math_correct ct0 sk0 workspace0 :
  phoare [CompleteDecaps(MathematicalSHAKE,MathematicalSHAKEH).run :
    ct=ct0 /\ sk=sk0 /\ workspace=workspace0 ==>
    (res.`1,res.`2)=complete_spec ct0 sk0 /\ res.`3=clear_zero_spec]=1%r.
proof.
  exact (complete_correct MathematicalSHAKE MathematicalSHAKEH ct0 sk0 workspace0
    mathematical_shake_functional complete_mathematical_h_functional
    mathematical_shake_lossless complete_mathematical_h_lossless).
qed.

lemma complete_success (G <: MessageSHAKE) (H <: CompleteSHAKEH) ct0 sk0 workspace0 :
  (forall input0, hoare [G.shake : input=input0 ==> res=message_shake_spec input0]) =>
  (forall input0, hoare [H.shake : input=input0 ==> res=complete_shake_h_spec input0]) =>
  islossless G.shake => islossless H.shake => complete_accepts ct0 sk0 =>
  phoare [CompleteDecaps(G,H).run : ct=ct0 /\ sk=sk0 /\ workspace=workspace0 ==>
    res.`1=Array32.init (fun i => (hash_h_spec (complete_message_result ct0 sk0).`2 (complete_sk_suffix sk0)).[i]) /\
    res.`2=W32.zero /\ res.`3=clear_zero_spec]=1%r.
proof.
  move=> hg hh gl hl ha.
  conseq (complete_lossless G H gl hl) (complete_functional G H ct0 sk0 workspace0 hg hh) => />.
  move=> &hr -> -> result hs hc.
  move: hs; rewrite (complete_accept_result ct0 sk0 ha); smt().
qed.

lemma complete_failure (G <: MessageSHAKE) (H <: CompleteSHAKEH) ct0 sk0 workspace0 :
  (forall input0, hoare [G.shake : input=input0 ==> res=message_shake_spec input0]) =>
  (forall input0, hoare [H.shake : input=input0 ==> res=complete_shake_h_spec input0]) =>
  islossless G.shake => islossless H.shake => !complete_accepts ct0 sk0 =>
  phoare [CompleteDecaps(G,H).run : ct=ct0 /\ sk=sk0 /\ workspace=workspace0 ==>
    res=(encap_zero_ss,W32.one,clear_zero_spec)]=1%r.
proof.
  move=> hg hh gl hl ha.
  conseq (complete_lossless G H gl hl) (complete_functional G H ct0 sk0 workspace0 hg hh) => />.
  move=> &hr -> -> result hs hc.
  move: hs; rewrite (complete_reject_result ct0 sk0 ha); smt().
qed.

lemma complete_status_correct (G <: MessageSHAKE) (H <: CompleteSHAKEH) ct0 sk0 workspace0 :
  (forall input0, hoare [G.shake : input=input0 ==> res=message_shake_spec input0]) =>
  (forall input0, hoare [H.shake : input=input0 ==> res=complete_shake_h_spec input0]) =>
  islossless G.shake => islossless H.shake =>
  phoare [CompleteDecaps(G,H).run : ct=ct0 /\ sk=sk0 /\ workspace=workspace0 ==>
    (res.`2=W32.zero <=> complete_accepts ct0 sk0) /\
    (res.`2=W32.one => res.`1=encap_zero_ss) /\ res.`3=clear_zero_spec]=1%r.
proof.
  move=> hg hh gl hl.
  conseq (complete_lossless G H gl hl) (complete_functional G H ct0 sk0 workspace0 hg hh) => />.
  move=> &hr result hs hc.
  have hz := complete_status_zero ct{hr} sk{hr}.
  have hf := complete_failure_zero ct{hr} sk{hr}.
  rewrite /complete_accepts /complete_entry_accepts /decap_guard_accepts /decap_key_encoding_valid in hz.
  smt().
qed.

lemma complete_core_entry_reject (G <: MessageSHAKE) (H <: CompleteSHAKEH) ct0 sk0 &m :
  !complete_entry_accepts ct0 sk0 =>
  phoare [CompleteCore(G,H).run : ct=ct0 /\ sk=sk0 /\
    (glob G)=(glob G){m} /\ (glob H)=(glob H){m} ==>
    res=(encap_zero_ss,W32.one) /\ (glob G)=(glob G){m} /\ (glob H)=(glob H){m}]=1%r.
proof.
  move=> hb; proc; rcondf 2.
  + call (guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly sk0)).
    auto => />; rewrite complete_guarded_prefix hb; smt(W32.to_uint0 W32.to_uint1).
  call (guarded_r2_reject witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly sk0) hb).
  by auto.
qed.

(* No functional or termination assumption about either hash is required:
   invalid entry bytes bypass both hashes, and clearing still executes. *)
lemma complete_entry_reject (G <: MessageSHAKE) (H <: CompleteSHAKEH) ct0 sk0 workspace0 &m :
  !complete_entry_accepts ct0 sk0 =>
  phoare [CompleteDecaps(G,H).run : ct=ct0 /\ sk=sk0 /\ workspace=workspace0 /\
    (glob G)=(glob G){m} /\ (glob H)=(glob H){m} ==>
    res=(encap_zero_ss,W32.one,clear_zero_spec) /\ (glob G)=(glob G){m} /\ (glob H)=(glob H){m}]=1%r.
proof.
  move=> hb; proc; inline CompleteCore(G,H).run.
  rcondf 4.
  + call (guarded_r2_functional witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly sk0)).
    auto => />; rewrite complete_guarded_prefix hb; smt(W32.to_uint0 W32.to_uint1).
  call (decap_clear_correct workspace0); wp.
  call (guarded_r2_reject witness witness witness witness witness encap_zero_ss ct0 (complete_sk_poly sk0) hb).
  by auto.
qed.
