require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array2304 Array32.
require import NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec.
require import NTRUPlus768DecapGuard NTRUPlus768DecapGuardSpec NTRUPlus768DecapGuardProof.
require import NTRUPlus768DecapCandidate NTRUPlus768DecapCandidateSpec.
require import NTRUPlus768DecapCandidateProof NTRUPlus768DecapCandidateAlgebra.

(* An EasyCrypt caller of the two actual extracted procedures. The native
   guard and candidate APIs remain separate; this is not a whole Decaps
   extraction, nor a statement about native pointer aliases or erasure. *)
module GuardedCandidate = {
  proc run(rp cp fp hp : W16.t Array768.t, ss : W8.t Array32.t,
      ct : W8.t Array1152.t, skpoly : W8.t Array2304.t) :
      W16.t Array768.t * W8.t Array32.t * W32.t = {
    var status : W32.t;
    (cp, fp, hp, ss, status) <@ NTRUPlus768DecapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_decap_guard(cp,fp,hp,ss,ct,skpoly);
    if (status = W32.zero) {
      rp <@ NTRUPlus768DecapCandidate.M.jade_ntruplus_ntruplus768_amd64_ref_decap_candidate(rp,cp,fp);
    }
    return (rp,ss,status);
  }
}.

op guarded_candidate_spec (rp : W16.t Array768.t) (ss : W8.t Array32.t)
    (ct : W8.t Array1152.t) (sk : W8.t Array2304.t) :
    W16.t Array768.t * W8.t Array32.t * W32.t =
  if decap_guard_accepts ct (decap_fbytes sk) (decap_hbytes sk)
  then (decap_candidate_spec (decoded_poly ct) (decoded_poly (decap_fbytes sk)), ss, W32.zero)
  else (rp,encap_zero_ss,W32.one).

lemma guarded_candidate_functional rp0 cp0 fp0 hp0 ss0 ct0 sk0 :
  hoare [GuardedCandidate.run :
    rp = rp0 /\ cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 ==>
    res = guarded_candidate_spec rp0 ss0 ct0 sk0].
proof.
  proc.
  seq 1 : (rp = rp0 /\ ct = ct0 /\ skpoly = sk0 /\
    (cp,fp,hp,ss,status) = decap_guard_spec fp0 hp0 ss0 ct0 (decap_fbytes sk0) (decap_hbytes sk0)).
  + call (decap_guard_functional cp0 fp0 hp0 ss0 ct0 sk0); auto.
  if.
  + ecall (decap_candidate_functional rp0 cp fp).
    auto => />.
    rewrite /guarded_candidate_spec /decap_guard_status /decap_guard_accepts /decap_key_encoding_valid.
    have hn : W32.one <> W32.zero by smt(W32.to_uint0 W32.to_uint1).
    case (encap_key_canonical ct0 /\ encap_key_canonical (decap_fbytes sk0) /\
      encap_key_canonical (decap_hbytes sk0)) => hg /=.
    - move: hg => [hc _]; by rewrite hc.
    by rewrite hn.
  auto => />; rewrite /guarded_candidate_spec /decap_guard_status;
    smt(W32.to_uint0 W32.to_uint1).
qed.

lemma guarded_candidate_lossless : islossless GuardedCandidate.run.
proof.
  proc; seq 1 : true.
  + ecall (decap_guard_functional cp fp hp ss ct skpoly); auto.
  + call decap_guard_lossless; auto.
  + if; [call decap_candidate_lossless | ]; auto.
  + hoare; ecall (decap_guard_functional cp fp hp ss ct skpoly); auto.
  auto.
qed.

lemma guarded_candidate_reject rp0 cp0 fp0 hp0 ss0 ct0 sk0 :
  ! decap_guard_accepts ct0 (decap_fbytes sk0) (decap_hbytes sk0) =>
  phoare [GuardedCandidate.run :
    rp = rp0 /\ cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 ==>
    res = (rp0, encap_zero_ss, W32.one)] = 1%r.
proof.
  move=> hb.
  conseq guarded_candidate_lossless
    (guarded_candidate_functional rp0 cp0 fp0 hp0 ss0 ct0 sk0) => />.
  move=> &hr -> ->.
  by rewrite /guarded_candidate_spec hb.
qed.

lemma guarded_candidate_accept rp0 cp0 fp0 hp0 ss0 ct0 sk0 :
  decap_guard_accepts ct0 (decap_fbytes sk0) (decap_hbytes sk0) =>
  phoare [GuardedCandidate.run :
    rp = rp0 /\ cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 ==>
    res = (decap_candidate_spec (decoded_poly ct0) (decoded_poly (decap_fbytes sk0)), ss0, W32.zero)] = 1%r.
proof.
  move=> ha.
  conseq guarded_candidate_lossless
    (guarded_candidate_functional rp0 cp0 fp0 hp0 ss0 ct0 sk0) => />.
  move=> &hr -> ->.
  by rewrite /guarded_candidate_spec ha /=.
qed.
