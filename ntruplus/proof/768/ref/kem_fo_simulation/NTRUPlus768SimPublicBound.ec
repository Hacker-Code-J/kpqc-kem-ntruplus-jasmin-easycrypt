require import AllCore List Distr FMap StdOrder StdBigop.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768ACWC2Oracle.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOF NTRUPlus768CCAGame NTRUPlus768CCAStatusAdapter NTRUPlus768CCADecapOracle.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOQueryBudget NTRUPlus768FOBadBound.
require import NTRUPlus768SimModel NTRUPlus768SimOracles NTRUPlus768SimPublicError.
import RealOrder StdBigop.Bigreal.BRA.

type sim_public_snapshot = keygen_witness * acwc2_g_function * fo_h_input option *
 (fo_h_input,W8.t Array224.t)fmap * (fo_h_input,W8.t Array224.t)fmap.
op sim_public_inv w g ex (s:sim_public_snapshot) =
 s.`1=w /\ s.`2=g /\ s.`3=ex /\ sim_log_included s.`4 s.`5 /\ sim_h_cover s.`4 s.`5 ex.
op sim_public_charge n lim=min n lim.

module SimPublicBudget = {
 var nh,limit:int
 var overflow:bool
 proc init(q:int) = {nh<-0;limit<-max 0 q;overflow<-false;}
 proc request() : bool = {
  var allowed;allowed<-nh<limit;nh<-nh+1;overflow<-overflow \/ !allowed;return allowed;
 }
}.
module SimPublicCountH(O:CCAExtendedOraclePort) : CCAExtendedOraclePort = {
 proc e=O.e
 proc f=O.f
 proc g=O.g
 proc h(input:fo_h_input) : W8.t Array224.t = {
  var y,allowed;allowed <@ SimPublicBudget.request();y <@ O.h(input);return y;
 }
 proc raw(input:W8.t list,outlen:int) : W8.t list option = {
  var y,allowed;if(fo_raw_h input outlen){allowed <@ SimPublicBudget.request();}
  y <@ O.raw(input,outlen);return y;
 }
}.
(* The identity writes identify all public callback boundaries to FEL.
   They preserve values. Only typed H and valid raw H consume budget. *)
module SimPublicCapH(O:CCAExtendedOraclePort) : CCAExtendedOraclePort = {
 proc e(input:W8.t Array32.t) : W8.t Array192.t = {
  var y;y <@ O.e(input);SimPublicBudget.nh<-SimPublicBudget.nh;return y;
 }
 proc f(input:W8.t Array1152.t) : W8.t Array32.t = {
  var y;y <@ O.f(input);SimPublicBudget.nh<-SimPublicBudget.nh;return y;
 }
 proc g(input:W8.t Array1152.t) : W8.t Array192.t = {
  var y;y <@ O.g(input);SimPublicBudget.nh<-SimPublicBudget.nh;return y;
 }
 proc h(input:fo_h_input) : W8.t Array224.t = {
  var y,allowed;allowed <@ SimPublicBudget.request();y<-witness;
  if(allowed){y <@ O.h(input);}SimPublicBudget.nh<-SimPublicBudget.nh;return y;
 }
 proc raw(input:W8.t list,outlen:int) : W8.t list option = {
  var y,allowed;allowed<-true;
  if(fo_raw_h input outlen){allowed <@ SimPublicBudget.request();}
  y<-None;if(allowed){y <@ O.raw(input,outlen);}
  SimPublicBudget.nh<-SimPublicBudget.nh;return y;
 }
}.
module SimPublicD(D:CCADecapPort) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var y;y <@ D.decap(ct);SimPublicBudget.nh<-SimPublicBudget.nh;return y;
 }
}.
module SimPublicCountedA(A:CCAExtendedAdversary,O:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc guess=A(SimPublicCountH(O),SimPublicD(D)).guess
}.
module SimPublicCappedA(A:CCAExtendedAdversary,O:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc guess=A(SimPublicCapH(O),SimPublicD(D)).guess
}.
module SimPublicBoundedPhase(A:CCAExtendedAdversary,B:FOBackend) = {
 proc run(q:int,pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t) : bool = {
  var answer;var fixed_context;
  fixed_context<-(FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m);
  SimBad.corr<-false;SimPublicBudget.init(q);
  answer <@ SimPublicCappedA(A,FOHashView(B),FODecapView(B)).guess(pk,ct,key);
  return answer;
 }
}.

lemma sim_public_budget_init_ll : islossless SimPublicBudget.init.
proof. proc;auto. qed.
lemma sim_public_request_ll : islossless SimPublicBudget.request.
proof. proc;auto. qed.
lemma sim_public_request_state n lim over : hoare[SimPublicBudget.request:
 SimPublicBudget.nh=n /\ SimPublicBudget.limit=lim /\ SimPublicBudget.overflow=over ==>
 SimPublicBudget.nh=n+1 /\ SimPublicBudget.limit=lim /\
 SimPublicBudget.overflow=(over \/ !(n<lim)) /\ res=(n<lim)].
proof. proc;auto. qed.
lemma sim_public_count_h_projection (O<:CCAExtendedOraclePort {-SimPublicBudget}) :
 equiv[SimPublicCountH(O).h ~ O.h : ={arg,glob O} ==> ={res,glob O}].
proof. proc*;inline{1} SimPublicCountH(O).h SimPublicBudget.request;sim. qed.
lemma sim_public_count_raw_projection (O<:CCAExtendedOraclePort {-SimPublicBudget}) :
 equiv[SimPublicCountH(O).raw ~ O.raw : ={arg,glob O} ==> ={res,glob O}].
proof.
 proc*;inline{1} SimPublicCountH(O).raw;wp.
 call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto.
 inline SimPublicBudget.request;auto.
qed.
lemma sim_public_d_projection (D<:CCADecapPort {-SimPublicBudget}) :
 equiv[SimPublicD(D).decap ~ D.decap : ={arg,glob D,glob SimPublicBudget} ==> ={res,glob D,glob SimPublicBudget}].
proof.
 proc*;inline{1} SimPublicD(D).decap;wp.
 call(_: ={arg,glob D} ==> ={res,glob D});first by proc true;auto. auto.
qed.

(* This is an explicitly capped public-H phase. D is forwarded without a cap.
   The returned corr-mass bound does not require adversary losslessness. *)
lemma sim_public_bounded_corr
 (A<:CCAExtendedAdversary {-FOContext,-SimHistory,-ROH,-SimBad,-SimPublicBudget})
 (B<:FOBackend {-A,-SimPublicBudget}) w0 g0 ex0 q0 pk0 ct0 key0 &m :
 0<=q0 =>sim_public_inv w0 g0 ex0 (FOContext.w{m},FOContext.g{m},FOContext.challenge_h{m},SimHistory.h{m},ROH.m{m}) =>
 (forall b,hoare[B.e:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b]) =>
 (forall b,hoare[B.f:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b]) =>
 (forall b,hoare[B.g:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b]) =>
 (forall b,hoare[B.h:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ (b=>SimBad.corr)]) =>
 (forall b,hoare[B.raw:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ (b=>SimBad.corr)]) =>
 (forall b,hoare[B.raw:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b /\ !fo_raw_h input outlen ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b]) =>
 (forall b,hoare[B.decap:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b]) =>
 (phoare[B.h:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ !SimBad.corr ==>SimBad.corr]<=(fo_error w0 g0)) =>
 (phoare[B.raw:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ !SimBad.corr /\ fo_raw_h input outlen ==>SimBad.corr]<=(fo_error w0 g0)) =>
 Pr[SimPublicBoundedPhase(A,B).run(q0,pk0,ct0,key0) @ &m:SimBad.corr]<=q0%r*fo_error w0 g0.
proof.
 move=>hq hi he hf hg hh hr hr0 hd ph pr.
 have hhctx:forall b,hoare[B.h:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m)].
 + move=>b;conseq [-frame](hh b);smt().
 have hrctx:forall b,hoare[B.raw:sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m)].
 + move=>b;conseq [-frame](hr b);smt().
 fel 3 (sim_public_charge SimPublicBudget.nh SimPublicBudget.limit) (fun _,fo_error w0 g0) q0 SimBad.corr
 [SimPublicCapH(FOHashView(B)).e:false;SimPublicCapH(FOHashView(B)).f:false;
  SimPublicCapH(FOHashView(B)).g:false;
  SimPublicCapH(FOHashView(B)).h:(SimPublicBudget.nh<SimPublicBudget.limit);
  SimPublicCapH(FOHashView(B)).raw:(fo_raw_h input outlen /\ SimPublicBudget.nh<SimPublicBudget.limit);
  SimPublicD(FODecapView(B)).decap:false]
 (sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimPublicBudget.limit=q0 /\ 0<=SimPublicBudget.nh)=> //.
 + by rewrite(fo_fel_cost_sum q0 (fo_error w0 g0) hq).
 + rewrite /sim_public_charge;smt().
 + inline SimPublicBudget.init;auto=> />;rewrite /sim_public_charge;smt().
 + move=>b c.
   conseq [-frame](_: _ ==> c<=sim_public_charge SimPublicBudget.nh SimPublicBudget.limit /\ SimPublicBudget.limit=q0 /\ 0<=SimPublicBudget.nh)
    (_: _ ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b);1,2:smt().
   + proc;wp;call(he b);auto;smt().
   proc;wp;call(_:true ==>true);first by trivial. auto;smt().
 + move=>b c.
   conseq [-frame](_: _ ==> c<=sim_public_charge SimPublicBudget.nh SimPublicBudget.limit /\ SimPublicBudget.limit=q0 /\ 0<=SimPublicBudget.nh)
    (_: _ ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b);1,2:smt().
   + proc;wp;call(hf b);auto;smt().
   proc;wp;call(_:true ==>true);first by trivial. auto;smt().
 + move=>b c.
   conseq [-frame](_: _ ==> c<=sim_public_charge SimPublicBudget.nh SimPublicBudget.limit /\ SimPublicBudget.limit=q0 /\ 0<=SimPublicBudget.nh)
    (_: _ ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b);1,2:smt().
   + proc;wp;call(hg b);auto;smt().
   proc;wp;call(_:true ==>true);first by trivial. auto;smt().
 + proc;wp;rcondt 3;first by inline SimPublicBudget.request;auto;smt().
   call ph;inline SimPublicBudget.request;auto;smt().
 + move=>c.
   conseq [-frame](_: _ ==> c<sim_public_charge SimPublicBudget.nh SimPublicBudget.limit /\ SimPublicBudget.limit=q0 /\ 0<=SimPublicBudget.nh)
    (_: _ ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m));1,2:smt().
   + proc;exists* SimBad.corr;elim*=>b0;wp;rcondt 3;first by inline SimPublicBudget.request;auto;smt().
     call(hhctx b0);inline SimPublicBudget.request;auto;smt().
   proc;wp;rcondt 3;first by inline SimPublicBudget.request;auto;smt().
   call(_:true ==>true);first by trivial.
   inline SimPublicBudget.request;auto=> />;rewrite /sim_public_charge;smt().
 + move=>b c;proc;wp;rcondf 3;first by inline SimPublicBudget.request;auto;smt().
   inline SimPublicBudget.request;auto=> />;rewrite /sim_public_charge;smt().
 + proc;wp;rcondt 2;first by auto;smt().
   rcondt 4;first by inline SimPublicBudget.request;auto;smt().
   call pr;inline SimPublicBudget.request;auto;smt().
 + move=>c.
   conseq [-frame](_: _ ==> c<sim_public_charge SimPublicBudget.nh SimPublicBudget.limit /\ SimPublicBudget.limit=q0 /\ 0<=SimPublicBudget.nh)
    (_: _ ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m));1,2:smt().
   + proc;exists* SimBad.corr;elim*=>b0;wp;rcondt 2;first by auto;smt().
     rcondt 4;first by inline SimPublicBudget.request;auto;smt().
     call(hrctx b0);inline SimPublicBudget.request;auto;smt().
   proc;wp;rcondt 2;first by auto;smt().
   rcondt 4;first by inline SimPublicBudget.request;auto;smt().
   call(_:true ==>true);first by trivial.
   inline SimPublicBudget.request;auto=> />;rewrite /sim_public_charge;smt().
 + move=>b c.
 conseq [-frame](_: _ ==> c<=sim_public_charge SimPublicBudget.nh SimPublicBudget.limit /\ SimPublicBudget.limit=q0 /\ 0<=SimPublicBudget.nh)
  (_: _ ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b);1,2:smt().
 + proc;wp;sp 1;if.
   + rcondf 3;first by inline SimPublicBudget.request;auto;smt().
     inline SimPublicBudget.request;auto;smt().
   rcondt 2;first by auto. call(hr0 b);auto;smt().
 proc;wp;sp 1;if.
 + rcondf 3;first by inline SimPublicBudget.request;auto;smt().
   inline SimPublicBudget.request;auto=> />;rewrite /sim_public_charge;smt().
 rcondt 2;first by auto. call(_:true ==>true);first by trivial. auto;smt().
 move=>b c.
   conseq [-frame](_: _ ==> c<=sim_public_charge SimPublicBudget.nh SimPublicBudget.limit /\ SimPublicBudget.limit=q0 /\ 0<=SimPublicBudget.nh)
    (_: _ ==> sim_public_inv w0 g0 ex0 (FOContext.w,FOContext.g,FOContext.challenge_h,SimHistory.h,ROH.m) /\ SimBad.corr=b);1,2:smt().
   + proc;wp;call(hd b);auto;smt().
   proc;wp;call(_:true ==>true);first by trivial. auto;smt().

qed.

lemma sim_public_cap_e_ll (O<:CCAExtendedOraclePort) : islossless O.e=>islossless SimPublicCapH(O).e.
proof. move=>h;proc;wp;call h;auto. qed.
lemma sim_public_cap_f_ll (O<:CCAExtendedOraclePort) : islossless O.f=>islossless SimPublicCapH(O).f.
proof. move=>h;proc;wp;call h;auto. qed.
lemma sim_public_cap_g_ll (O<:CCAExtendedOraclePort) : islossless O.g=>islossless SimPublicCapH(O).g.
proof. move=>h;proc;wp;call h;auto. qed.
lemma sim_public_cap_h_ll (O<:CCAExtendedOraclePort) : islossless O.h=>islossless SimPublicCapH(O).h.
proof.
 move=>h;proc;seq 2:true;1,4,5:by auto.
 + wp;call sim_public_request_ll;auto.
 if;auto;call h;auto.
qed.
lemma sim_public_cap_raw_ll (O<:CCAExtendedOraclePort) : islossless O.raw=>islossless SimPublicCapH(O).raw.
proof.
 move=>h;proc;seq 3:true;1,4,5:by auto.
 + wp;sp 1;if;auto;call sim_public_request_ll;auto.
 if;auto;call h;auto.
qed.
lemma sim_public_d_ll (D<:CCADecapPort) : islossless D.decap=>islossless SimPublicD(D).decap.
proof. move=>h;proc;wp;call h;auto. qed.
lemma sim_public_count_h_ll (O<:CCAExtendedOraclePort) : islossless O.h=>islossless SimPublicCountH(O).h.
proof. move=>h;proc;call h;call sim_public_request_ll;auto. qed.
lemma sim_public_count_raw_ll (O<:CCAExtendedOraclePort) : islossless O.raw=>islossless SimPublicCountH(O).raw.
proof. move=>h;proc;call h;if;auto;call sim_public_request_ll;auto. qed.

lemma sim_public_cap_e_projection (O<:CCAExtendedOraclePort {-SimPublicBudget}) :
 equiv[SimPublicCapH(O).e ~ O.e: ={arg,glob O,glob SimPublicBudget} ==> ={res,glob O,glob SimPublicBudget}].
proof.
 proc*;inline{1} SimPublicCapH(O).e;wp.
 call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto. auto.
qed.
lemma sim_public_cap_f_projection (O<:CCAExtendedOraclePort {-SimPublicBudget}) :
 equiv[SimPublicCapH(O).f ~ O.f: ={arg,glob O,glob SimPublicBudget} ==> ={res,glob O,glob SimPublicBudget}].
proof.
 proc*;inline{1} SimPublicCapH(O).f;wp.
 call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto. auto.
qed.
lemma sim_public_cap_g_projection (O<:CCAExtendedOraclePort {-SimPublicBudget}) :
 equiv[SimPublicCapH(O).g ~ O.g: ={arg,glob O,glob SimPublicBudget} ==> ={res,glob O,glob SimPublicBudget}].
proof.
 proc*;inline{1} SimPublicCapH(O).g;wp.
 call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto. auto.
qed.

lemma sim_public_capped_phase_ll
 (A<:CCAExtendedAdversary {-SimPublicBudget}) (B<:FOBackend {-A,-SimPublicBudget}) :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 islossless SimPublicCappedA(A,FOHashView(B),FODecapView(B)).guess.
proof.
 move=>he hf hg hh hr hd all.
 apply(all (SimPublicCapH(FOHashView(B))) (SimPublicD(FODecapView(B)))).
 + exact(sim_public_cap_e_ll (FOHashView(B)) he).
 + exact(sim_public_cap_f_ll (FOHashView(B)) hf).
 + exact(sim_public_cap_g_ll (FOHashView(B)) hg).
 + exact(sim_public_cap_h_ll (FOHashView(B)) hh).
 + exact(sim_public_cap_raw_ll (FOHashView(B)) hr).
 exact(sim_public_d_ll (FODecapView(B)) hd).
qed.
lemma sim_public_bounded_phase_ll
 (A<:CCAExtendedAdversary {-SimPublicBudget}) (B<:FOBackend {-A,-SimPublicBudget}) :
 islossless B.e=>islossless B.f=>islossless B.g=>islossless B.h=>islossless B.raw=>islossless B.decap=>
 (forall (H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 islossless SimPublicBoundedPhase(A,B).run.
proof.
 move=>he hf hg hh hr hd all;proc.
 call(sim_public_capped_phase_ll A B he hf hg hh hr hd all).
 call sim_public_budget_init_ll;auto.
qed.
