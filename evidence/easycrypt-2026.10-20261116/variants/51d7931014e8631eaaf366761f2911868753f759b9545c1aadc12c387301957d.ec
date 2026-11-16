require import AllCore Distr List DList.
from Jasmin require import JWord.
require import Array192.

(* The loop draws actual expansion buffers independently from d.  Nonpositive
   budgets perform no draw.  None records exhaustion without acceptance. *)
module BoundedBufferRejection = {
  proc run(d:W8.t Array192.t distr, accept:W8.t Array192.t -> bool,
      q:int) : W8.t Array192.t option = {
    var buffer:W8.t Array192.t; var count:int; var success:bool;
    buffer <- witness; count <- 0; success <- false;
    while (count < q /\ !success) {
      buffer <$ d;
      success <- accept buffer;
      count <- count + 1;
    }
    return if success then Some buffer else None;
  }
}.

clone import DList.ParametricProgram as BufferListSampling with
  type t <- W8.t Array192.t.

lemma bounded_buffer_rejection_lossless d0 :
  is_lossless d0 =>
  phoare[BoundedBufferRejection.run : d=d0 ==> true] = 1%r.
proof.
  move=> dll; proc.
  while (d=d0) (q-count).
  + move=> z; auto=> />; smt().
  auto=> />; smt().
qed.

lemma bounded_buffer_rejection_nonpositive q0 :
  q0<=0 =>
  phoare[BoundedBufferRejection.run : q=q0 ==> res=None] = 1%r.
proof.
  move=> hq; proc; rcondf 4; auto; smt().
qed.

lemma bounded_buffer_rejection_list accept0 :
  equiv[BoundedBufferRejection.run ~ BufferListSampling.Loop.sample :
    d{1}=d{2} /\ q{1}=n{2} /\ accept{1}=accept0 /\ is_lossless d{1} ==>
    (res{1}=None) = all (fun b=> !accept0 b) res{2}].
proof.
  proc; splitwhile{2} 3 : (all (fun b=> !accept0 b) l).
  seq 4 3 : (d{1}=d{2} /\ q{1}=n{2} /\ accept{1}=accept0 /\
    is_lossless d{1} /\ count{1}=i{2} /\
    (!success{1})=all (fun b=> !accept0 b) l{2} /\
    (!success{1} => n{2}<=i{2})).
  + while (d{1}=d{2} /\ q{1}=n{2} /\ accept{1}=accept0 /\
      is_lossless d{1} /\ count{1}=i{2} /\
      (!success{1})=all (fun b=> !accept0 b) l{2});
      auto=> />; smt().
  while{2} (is_lossless d{2} /\
    (!success{1})=all (fun b=> !accept0 b) l{2} /\
    (!success{1} => n{2}<=i{2})) (n{2}-i{2}); auto=> />; smt().
qed.

lemma bounded_buffer_dlist_all (d:W8.t Array192.t distr)
    (p:W8.t Array192.t -> bool) q :
  0<=q => mu (dlist d q) (all p) = (mu d p)^q.
proof.
  elim: q => [|q hq ih].
  + by rewrite dlist0 // dunitE /= RField.expr0.
  rewrite dlistS //= dmapE /(\o) /=.
  by rewrite (Distr.dprodE p (List.all p) d (dlist d q)) ih RField.exprS.
qed.

lemma bounded_buffer_rejection_tail &m d0 accept0 q0 :
  is_lossless d0 => 0<=q0 =>
  Pr[BoundedBufferRejection.run(d0,accept0,q0) @ &m:res=None] =
    (1%r-mu d0 accept0)^q0.
proof.
  move=> dll hq.
  have ->: Pr[BoundedBufferRejection.run(d0,accept0,q0) @ &m:res=None] =
      Pr[BufferListSampling.Loop.sample(d0,q0) @ &m:
        all (fun b=> !accept0 b) res].
  + byequiv (bounded_buffer_rejection_list accept0); auto.
    smt().
  have <-: Pr[BufferListSampling.Sample.sample(d0,q0) @ &m:
        all (fun b=> !accept0 b) res] =
      Pr[BufferListSampling.Loop.sample(d0,q0) @ &m:
        all (fun b=> !accept0 b) res].
  + by byequiv BufferListSampling.Sample_Loop_eq; auto; smt().
  have ->: Pr[BufferListSampling.Sample.sample(d0,q0) @ &m:
        all (fun b=> !accept0 b) res] =
      mu (dlist d0 q0) (all (fun b=> !accept0 b)).
  + by byphoare (_:d=d0 /\ n=q0 ==> all (fun b=> !accept0 b) res) => //;
      proc; rnd; auto.
  rewrite bounded_buffer_dlist_all //.
  have ->: (fun b=> !accept0 b) = predC accept0 by done.
  by rewrite mu_not dll.
qed.

lemma bounded_buffer_rejection_tail_phoare d0 accept0 q0 :
  is_lossless d0 => 0<=q0 =>
  phoare[BoundedBufferRejection.run :
    d=d0 /\ accept=accept0 /\ q=q0 ==> res=None] =
    ((1%r-mu d0 accept0)^q0).
proof.
  move=> dll hq; by bypr=> &m [-> [-> ->]];
    exact (bounded_buffer_rejection_tail &m d0 accept0 q0 dll hq).
qed.
