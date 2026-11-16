require import AllCore Distr Dexcepted.
from Jasmin require import JWord.
require import Array192.

(* Rejection law for actual expanded buffers; the predicate retains all
   dependencies between the coefficients after acceptance. *)
clone import Dexcepted.WhileSampling as BufferSampling with
  type input <- W8.t Array192.t distr,
  type t <- W8.t Array192.t,
  op dt <- (fun d => d).

op buffer_reject (accept:W8.t Array192.t -> bool)
    (_:W8.t Array192.t distr) (buffer:W8.t Array192.t) = !accept buffer.

module BufferRejection = {
  proc sample(d:W8.t Array192.t distr,accept:W8.t Array192.t -> bool) : W8.t Array192.t = {
    var buffer:W8.t Array192.t;
    buffer <$ d;
    while (!accept buffer) { buffer <$ d; }
    return buffer;
  }
  proc direct(d:W8.t Array192.t distr,accept:W8.t Array192.t -> bool) : W8.t Array192.t = {
    var buffer:W8.t Array192.t;
    buffer <$ dcond d accept;
    return buffer;
  }
  proc flagged(d:W8.t Array192.t distr,accept:W8.t Array192.t -> bool) : W8.t Array192.t = {
    var buffer:W8.t Array192.t; var success:bool;
    buffer <- witness; success <- false;
    while (!success) { buffer <$ d; success <- accept buffer; }
    return buffer;
  }
  proc expanded(d:W8.t Array192.t distr,accept:W8.t Array192.t -> bool,
      expand:W8.t Array192.t -> W8.t Array192.t) : W8.t Array192.t = {
    var buffer:W8.t Array192.t;
    buffer <@ sample(d,accept);
    return expand buffer;
  }
}.

lemma buffer_excepted_conditional d accept :
  d \ buffer_reject accept d = dcond d accept.
proof.
  rewrite /buffer_reject /(\) /dcond; congr; congr.
  by apply fun_ext => buffer; rewrite /predC.
qed.

lemma buffer_rejection_flagged :
  equiv [BufferRejection.flagged ~ BufferRejection.sample : ={d,accept} ==> ={res}].
proof.
  proc; unroll{1} 3; rcondt{1} 3; first by auto.
  while (={d,accept,buffer} /\ success{1}=accept{2} buffer{2}); auto => />.
qed.

lemma buffer_rejection_library :
  equiv [BufferRejection.sample ~ BufferSampling.SampleW.sample :
    d{1}=i{2} /\ test{2}=buffer_reject accept{1} ==> ={res}].
proof.
  proc; inline BufferSampling.SampleWi.sample.
  wp; while (buffer{1}=r0{2} /\ d{1}=i0{2} /\ test0{2}=buffer_reject accept{1});
    auto => />; rewrite /buffer_reject; smt().
qed.

lemma buffer_rejection_probability &m d accept (event:W8.t Array192.t -> bool) :
  is_lossless d =>
  Pr[BufferRejection.sample(d,accept) @ &m:event res] = mu (dcond d accept) event.
proof.
  move=> dll; rewrite -buffer_excepted_conditional.
  rewrite -(@BufferSampling.pr_sampleW &m d (buffer_reject accept) event dll).
  by byequiv buffer_rejection_library.
qed.

lemma buffer_rejection_phoare d0 accept0 (event:W8.t Array192.t -> bool) :
  is_lossless d0 =>
  phoare [BufferRejection.sample : d=d0 /\ accept=accept0 ==> event res] =
    (mu (dcond d0 accept0) event).
proof.
  move=> dll; by bypr => &m [-> ->]; apply (buffer_rejection_probability &m d0 accept0 event dll).
qed.

lemma buffer_rejection_lossless d0 accept0 :
  is_lossless d0 => 0%r < mu d0 accept0 =>
  phoare [BufferRejection.sample : d=d0 /\ accept=accept0 ==> true] = 1%r.
proof.
  move=> dll positive.
  have condll:=dcond_ll d0 accept0 positive.
  conseq (buffer_rejection_phoare d0 accept0 predT dll); smt().
qed.

lemma buffer_rejection_exact_conditional &m d accept (event:W8.t Array192.t -> bool) :
  is_lossless d =>
  Pr[BufferRejection.sample(d,accept) @ &m:event res] =
    mu d (fun buffer => accept buffer /\ event buffer) / mu d accept.
proof.
  move=> dll; rewrite (buffer_rejection_probability &m d accept event dll) dcondE.
  by rewrite /predI.
qed.

lemma buffer_rejection_flagged_probability d0 accept0 (event:W8.t Array192.t -> bool) :
  is_lossless d0 =>
  phoare [BufferRejection.flagged : d=d0 /\ accept=accept0 ==> event res] =
    (mu (dcond d0 accept0) event).
proof.
  move=> dll; conseq buffer_rejection_flagged (buffer_rejection_phoare d0 accept0 event dll); smt().
qed.
