require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array192 Array768.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteAttempt.

(* The returned accepted buffers and inverses are private proof witnesses.
   The public keypair procedure projects only the serialized public/secret keys. *)
module KeygenRetry(R : KeygenSeedRNG,E : KeygenExpand) = {
 proc f() : W8.t Array192.t * W16.t Array768.t * W16.t Array768.t = {
  var seed:W8.t Array32.t; var buf:W8.t Array192.t;
  var ntt,inverse:W16.t Array768.t; var status:W64.t;
  buf <- witness; ntt <- witness; inverse <- witness; status <- W64.one;
  while (status <> W64.zero) {
   seed <@ R.sample();
   (buf,ntt,inverse,status) <@ KeygenAttempt(E).f(seed);
  }
  return (buf,ntt,inverse);
 }
 proc g() : W8.t Array192.t * W16.t Array768.t * W16.t Array768.t = {
  var seed:W8.t Array32.t; var buf:W8.t Array192.t;
  var ntt,inverse:W16.t Array768.t; var status:W64.t;
  buf <- witness; ntt <- witness; inverse <- witness; status <- W64.one;
  while (status <> W64.zero) {
   seed <@ R.sample();
   (buf,ntt,inverse,status) <@ KeygenAttempt(E).g(seed);
  }
  return (buf,ntt,inverse);
 }
}.
lemma keygen_retry_f_accepted (R <: KeygenSeedRNG) (E <: KeygenExpand) :
 hoare [KeygenRetry(R,E).f : true ==> keygen_f_accepted res.`1 res.`2 res.`3].
proof.
 proc; while(status=W64.zero => keygen_f_accepted buf ntt inverse).
 + call(keygen_attempt_f_accepted E); call (_:true ==> true); auto.
 auto => />; smt(W64.to_uint0 W64.to_uint1).
qed.
lemma keygen_retry_g_accepted (R <: KeygenSeedRNG) (E <: KeygenExpand) :
 hoare [KeygenRetry(R,E).g : true ==> keygen_g_accepted res.`1 res.`2 res.`3].
proof.
 proc; while(status=W64.zero => keygen_g_accepted buf ntt inverse).
 + call(keygen_attempt_g_accepted E); call (_:true ==> true); auto.
 auto => />; smt(W64.to_uint0 W64.to_uint1).
qed.
