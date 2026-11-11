require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array2304 Array32 NTRUPlus768DecapGuard.
require import NTRUPlus768DecapGuardSpec NTRUPlus768DecapGuardProof NTRUPlus768EncapGuardSpec NTRUPlus768CanonicalDecoder.

(* Composition at the extracted guard/abstract continuation boundary.
   This does not identify Body with the extracted complete Decaps API.
   Guard acceptance only permits continuation: the continuation returns its
   own status, including later SOTP/reencryption rejection. *)
module type DecapBody = {
  proc run(cp fp hp : W16.t Array768.t, ss : W8.t Array32.t,
    ct : W8.t Array1152.t, skpoly : W8.t Array2304.t) : W8.t Array32.t * W32.t
}.

module DecapGuardedCaller(Body : DecapBody) = {
  proc run(cp fp hp : W16.t Array768.t, ss : W8.t Array32.t,
      ct : W8.t Array1152.t, skpoly : W8.t Array2304.t) :
      W16.t Array768.t * W16.t Array768.t * W16.t Array768.t * W8.t Array32.t * W32.t = {
    var status : W32.t;
    (cp, fp, hp, ss, status) <@ NTRUPlus768DecapGuard.M.jade_ntruplus_ntruplus768_amd64_ref_decap_guard(cp,fp,hp,ss,ct,skpoly);
    if (status = W32.zero) {
      (ss, status) <@ Body.run(cp,fp,hp,ss,ct,skpoly);
    }
    return (cp,fp,hp,ss,status);
  }
}.

(* The valid-input comparison program makes exactly one continuation call.
   No termination assumption on that arbitrary Body is used by equiv. *)
module DecapDirectCaller(Body : DecapBody) = {
  proc run(cp fp hp : W16.t Array768.t, ss : W8.t Array32.t,
      ct : W8.t Array1152.t, skpoly : W8.t Array2304.t) :
      W16.t Array768.t * W16.t Array768.t * W16.t Array768.t * W8.t Array32.t * W32.t = {
    var status : W32.t;
    cp <- decoded_poly ct;
    fp <- decoded_poly (decap_fbytes skpoly);
    hp <- decoded_poly (decap_hbytes skpoly);
    (ss, status) <@ Body.run(cp,fp,hp,ss,ct,skpoly);
    return (cp,fp,hp,ss,status);
  }
}.

lemma decap_caller_rejection_preserves_body (Body <: DecapBody) cp0 fp0 hp0 ss0 ct0 sk0 &m :
  ! (decap_guard_accepts ct0 (decap_fbytes sk0) (decap_hbytes sk0)) =>
  phoare [DecapGuardedCaller(Body).run :
    cp = cp0 /\ fp = fp0 /\ hp = hp0 /\ ss = ss0 /\ ct = ct0 /\ skpoly = sk0 /\
    (glob Body) = (glob Body){m} ==>
    res = decap_guard_spec fp0 hp0 ss0 ct0 (decap_fbytes sk0) (decap_hbytes sk0) /\
    (glob Body) = (glob Body){m}] = 1%r.
proof.
  move=> hbad; proc.
  rcondf 2.
  + call (decap_guard_functional cp0 fp0 hp0 ss0 ct0 sk0).
    auto => />; rewrite /decap_guard_spec /decap_guard_status hbad /=;
    smt(W32.to_uint0 W32.to_uint1).
  call (decap_guard_correct cp0 fp0 hp0 ss0 ct0 sk0).
  by auto.
qed.

lemma decap_caller_valid_dispatch (Body <: DecapBody) :
  equiv [DecapGuardedCaller(Body).run ~ DecapDirectCaller(Body).run :
    ={cp,fp,hp,ss,ct,skpoly,glob Body} /\
    decap_guard_accepts ct{1} (decap_fbytes skpoly{1}) (decap_hbytes skpoly{1}) ==>
    ={res,glob Body}].
proof.
  proc.
  rcondt{1} 2.
  + move=> &2; ecall (decap_guard_functional cp fp hp ss ct skpoly).
    auto => />; rewrite /decap_guard_spec /decap_guard_status; smt().
  call (_ : true).
  wp.
  ecall{1} (decap_guard_correct cp{1} fp{1} hp{1} ss{1} ct{1} skpoly{1}).
  auto => />; rewrite /decap_guard_spec /decap_guard_status /decap_guard_accepts /decap_key_encoding_valid; smt().
qed.
