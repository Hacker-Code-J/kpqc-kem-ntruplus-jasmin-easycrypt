require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array2304 Array32.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec.
require import NTRUPlus768DecapGuard NTRUPlus768DecapGuardSpec NTRUPlus768DecapGuardProof.
require import NTRUPlus768DecapCandidate NTRUPlus768DecapCandidateSpec NTRUPlus768DecapCandidateProof.
require import NTRUPlus768DecapR2Comp NTRUPlus768DecapR2CompSpec.
require import NTRUPlus768DecapR2CompProof NTRUPlus768DecapR2CompAlgebra.
require import NTRUPlus768PolySubAlgebra NTRUPlus768PolyBasemulAlgebra NTRUPlus768DecapCandidateAlgebra.

(* A model caller of three actual extracted exports. The three native entry
   points are separate: this is not whole-Decaps extraction, a shared-memory
   alias theorem, an erasure theorem, or a randomness-recovery theorem. *)
module GuardedR2 = {
  proc run(rp mp cp fp hp : W16.t Array768.t, ss : W8.t Array32.t,
      ct : W8.t Array1152.t, skpoly : W8.t Array2304.t) :
      W16.t Array768.t * W16.t Array768.t * W8.t Array32.t * W32.t = {
    var status : W32.t;
    (cp, fp, hp, ss, status) <@ NTRUPlus768DecapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_decap_guard(cp,fp,hp,ss,ct,skpoly);
    if (status = W32.zero) {
      mp <@ NTRUPlus768DecapCandidate.M.jade_ntruplus_ntruplus768_amd64_ref_decap_candidate(mp,cp,fp);
      rp <@ NTRUPlus768DecapR2Comp.M.jade_ntruplus_ntruplus768_amd64_ref_decap_r2(rp,cp,mp,hp);
    }
    return (rp,mp,ss,status);
  }
}.

op guarded_r2_spec (rp mp : W16.t Array768.t) (ss : W8.t Array32.t)
    (ct : W8.t Array1152.t) (sk : W8.t Array2304.t) :
    W16.t Array768.t * W16.t Array768.t * W8.t Array32.t * W32.t =
  let candidate = decap_candidate_spec (decoded_poly ct) (decoded_poly (decap_fbytes sk)) in
  if decap_guard_accepts ct (decap_fbytes sk) (decap_hbytes sk)
  then (decap_r2_spec (decoded_poly ct) candidate (decoded_poly (decap_hbytes sk)),
        candidate, ss, W32.zero)
  else (rp,mp,encap_zero_ss,W32.one).

lemma guarded_r2_functional rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0 :
  hoare [GuardedR2.run :
    rp = rp0 /\ mp = mp0 /\ cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 ==>
    res = guarded_r2_spec rp0 mp0 ss0 ct0 sk0].
proof.
  proc.
  seq 1 : (rp = rp0 /\ mp = mp0 /\ ct = ct0 /\ skpoly = sk0 /\
    (cp,fp,hp,ss,status) = decap_guard_spec fp0 hp0 ss0 ct0 (decap_fbytes sk0) (decap_hbytes sk0)).
  + call (decap_guard_functional cp0 fp0 hp0 ss0 ct0 sk0); auto.
  if.
  + ecall (decap_r2_functional rp0 cp (decap_candidate_spec cp fp) hp).
    ecall (decap_candidate_functional mp0 cp fp).
    auto => />.
    rewrite /guarded_r2_spec /decap_guard_status /decap_guard_accepts /decap_key_encoding_valid.
    have hn : W32.one <> W32.zero by smt(W32.to_uint0 W32.to_uint1).
    case (encap_key_canonical ct0 /\ encap_key_canonical (decap_fbytes sk0) /\
      encap_key_canonical (decap_hbytes sk0)) => hg /=.
    - move: hg => [hc [hf hh]]; by rewrite hc hf.
    by rewrite hn.
  auto => />; rewrite /guarded_r2_spec /decap_guard_status;
    smt(W32.to_uint0 W32.to_uint1).
qed.

lemma guarded_r2_lossless : islossless GuardedR2.run.
proof.
  proc; seq 1 : true.
  + ecall (decap_guard_functional cp fp hp ss ct skpoly); auto.
  + call decap_guard_lossless; auto.
  + if; [call decap_r2_lossless; call decap_candidate_lossless | ]; auto.
  + hoare; ecall (decap_guard_functional cp fp hp ss ct skpoly); auto.
  auto.
qed.

lemma guarded_r2_reject rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0 :
  ! decap_guard_accepts ct0 (decap_fbytes sk0) (decap_hbytes sk0) =>
  phoare [GuardedR2.run :
    rp = rp0 /\ mp = mp0 /\ cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 ==>
    res = (rp0,mp0,encap_zero_ss,W32.one)] = 1%r.
proof.
  move=> hb.
  conseq guarded_r2_lossless
    (guarded_r2_functional rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0) => />.
  move=> &hr -> ->.
  by rewrite /guarded_r2_spec hb.
qed.

lemma guarded_r2_accept rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0 :
  decap_guard_accepts ct0 (decap_fbytes sk0) (decap_hbytes sk0) =>
  phoare [GuardedR2.run :
    rp = rp0 /\ mp = mp0 /\ cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 ==>
    res = (decap_r2_spec (decoded_poly ct0)
      (decap_candidate_spec (decoded_poly ct0) (decoded_poly (decap_fbytes sk0)))
      (decoded_poly (decap_hbytes sk0)),
      decap_candidate_spec (decoded_poly ct0) (decoded_poly (decap_fbytes sk0)), ss0, W32.zero)] = 1%r.
proof.
  move=> ha.
  conseq guarded_r2_lossless
    (guarded_r2_functional rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0) => />.
  move=> &hr -> ->.
  by rewrite /guarded_r2_spec ha /=.
qed.

lemma guarded_r2_accept_inputs rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0 :
  decap_guard_accepts ct0 (decap_fbytes sk0) (decap_hbytes sk0) =>
  phoare [GuardedR2.run :
    rp = rp0 /\ mp = mp0 /\ cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 ==>
    decoder_range (decoded_poly ct0) /\ candidate_ternary res.`2 /\
    in_canonical_range768 (decoded_poly (decap_hbytes sk0))] = 1%r.
proof.
  move=> ha.
  conseq guarded_r2_lossless
    (guarded_r2_functional rp0 mp0 cp0 fp0 hp0 ss0 ct0 sk0) => />.
  move=> &hr -> ->.
  rewrite /guarded_r2_spec ha /=.
  exact (r2_guard_candidate_inputs ct0 sk0 ha).
qed.
