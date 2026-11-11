require import AllCore List Distr DBool FMap SDist StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768AHState NTRUPlus768AHAdapter NTRUPlus768AHCPAGames.
require import NTRUPlus768AHFreshBound.
require import NTRUPlus768CPAModel NTRUPlus768CPAReduction.
require import NTRUPlus768SecModel NTRUPlus768SecChallengeBridge.
require import NTRUPlus768SimModel NTRUPlus768SimLookup NTRUPlus768SimSampling.
require import NTRUPlus768SimOracles NTRUPlus768SimAverage.
require import NTRUPlus768FOModel NTRUPlus768FOError NTRUPlus768FOEagerG.
require import NTRUPlus768FOSetupDistribution NTRUPlus768FOSetupExpectation NTRUPlus768FOJointGames.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768ROMKeygen.
require import NTRUPlus768RawXOFStreams NTRUPlus768RawXOF NTRUPlus768CCAGame.
require import NTRUPlus768CCADecapOracle NTRUPlus768CCAOraclePorts.
require import NTRUPlus768ACWC2Oracle NTRUPlus768PKEModel NTRUPlus768DecapCompleteSpec.
import RealOrder.

lemma ah_cpa_setup_facts (s:fo_setup_observation) : fo_setup_valid s=>
 pke_key_relation s.`1.`1 /\
 acwc2_cache_matches(acwc2_gfun s.`3)(acwc2_g_cache s.`3) /\
 s.`2.[s.`1.`1.`kg_pk]=Some(complete_sk_suffix s.`1.`1.`kg_sk).
proof.
 move=>hv;have [hr [_ [hk [_ hg]]]]:=hv.
 move:hr;rewrite /rom_key_relation=>hr.
 by smt().
qed.

lemma ah_cpa_encrypt_prepared pk0 msg0 hout0 g gm0 :
 acwc2_cache_matches g gm0=>
 phoare[SimEncrypt(FOGActual).run:
 pk=pk0 /\ msg=msg0 /\ hout=hout0 /\ ROG.m=gm0 ==>
 res=sim_candidate pk0 g (msg0,witness) hout0 /\ ROG.m=gm0]=1%r.
proof.
 move=>hg;conseq(sim_encrypt_lossless FOGActual rog_get_ll)
  (sim_encrypt_prepared pk0 (msg0,witness) hout0 g gm0 hg);smt().
qed.

lemma ah_cpa_encrypt_coupling g gm0 : acwc2_cache_matches g gm0=>
 equiv[SimEncrypt(FOGActual).run ~ SimEncrypt(FOGActual).run:
 ={arg} /\ ROG.m{1}=gm0 /\ ROG.m{2}=gm0 ==>
 ={res} /\ ROG.m{1}=gm0 /\ ROG.m{2}=gm0].
proof.
 move=>hg;exists* pk{1},msg{1},hout{1};elim*=>pk0 msg0 hout0.
 proc*;ecall{1}(ah_cpa_encrypt_prepared pk0 msg0 hout0 g gm0 hg).
 ecall{2}(ah_cpa_encrypt_prepared pk0 msg0 hout0 g gm0 hg).
 auto=> />;smt().
qed.

(* The monitor is confined to a proof kernel. The challenge still uses
   the actual encryption calls, followed by the full adaptive phase. *)
module AHCPAMonitoredKernel(A:CCAExtendedAdversary) = {
 proc guess(s:fo_setup_observation):bool = {
  var target,other:W8.t Array96.t;var bit,ignored:bool;
  var hout:W8.t Array224.t;var enc:W8.t Array1152.t option;
  var key:W8.t Array32.t;
  ROE.init();ROG.init();ROH.init();RawXOFStreams.init();
  ROF.m<-s.`2;ROG.m<-acwc2_g_cache s.`3;
  target<$uniform96;other<$uniform96;bit<$dbool;hout<$uniform224;
  enc<@SimEncrypt(FOGActual).run(s.`1.`1.`kg_pk,if bit then other else target,hout);
  key<$uniform32;
  ignored<@AHFreshPhase(A).run(s.`1.`1,acwc2_gfun s.`3,s.`1.`1.`kg_pk,oget enc,key);
  return (!((target,SimPublic.suffix) \in SimHistory.h))=bit;
 }
}.

lemma ah_cpa_monitored_projection
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO,-FOContext,-SimBad}) :
 equiv[AHCPAMonitoredKernel(A).guess ~ AHCPAKernel(A).guess:
 ={s,glob A,glob SimPublic,SimHistory.h} ==> ={res,glob A}].
proof.
 proc;inline{1} AHFreshPhase(A).run;
 inline{2} AHCPAContext(A,FOGActual).run SecRun(A,FOGActual).run SecPhase(A,FOGActual).run.
 wp;call(ah_fresh_adversary_projection A).
 inline SimPublic.init SimHistory.init;wp.
 call(_: ={arg,ROF.m} ==> ={res,ROF.m});first by sim.
 wp;rnd;wp;call(_: ={arg,ROG.m} ==> ={res,ROG.m});first by sim.
 rnd;rnd;rnd;rnd.
 inline ROE.init ROG.init ROH.init RawXOFStreams.init;auto.
qed.

lemma ah_cpa_monitored_probability
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO,-FOContext,-SimBad})
 s &m (event:bool->bool) :
 Pr[AHCPAMonitoredKernel(A).guess(s)@&m:event res]=
 Pr[AHCPAKernel(A).guess(s)@&m:event res].
proof. by byequiv(ah_cpa_monitored_projection A)=> //. qed.

lemma ah_cpa_monitored_bad
 (A<:CCAExtendedAdversary {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO,-FOContext,-SimBad})
 s0 qC &m :
 0<=qC=>hoare[CPAPhase(A).run:true ==>fsize SimHistory.h<=qC]=>
 Pr[AHCPAMonitoredKernel(A).guess(s0)@&m:SimBad.corr]<=qC%r*fo_setup_error s0.
proof.
 move=>hq hc;rewrite /fo_setup_error.
 byphoare(_:s=s0 ==>SimBad.corr)=> //.
 proc;wp;call(ah_fresh_phase_ph A s0.`1.`1 (acwc2_gfun s0.`3) qC hq hc).
 rnd;call(_:true ==>true);first by trivial.
 rnd;rnd;rnd;rnd.
 inline ROE.init ROG.init ROH.init RawXOFStreams.init;auto=> />;
 smt(uniform32_ll uniform96_ll uniform224_ll dbool_ll fo_error_range).
qed.

require import NTRUPlus768AHCoupling NTRUPlus768FOSecurity NTRUPlus768HistBound.

lemma ah_cpa_monitored_coupling
 (S<:AHStore {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO,-FOContext,-SimBad})
 (A<:CCAExtendedAdversary {-S,-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO,-FOContext,-SimBad})
 (view:(glob S)->ah_state) (s0:fo_setup_observation) :
 fo_setup_valid s0=>
 islossless S.init=>islossless S.snapshot=>islossless S.record=>
 (forall pk suffix star,hoare[S.init:arg=(pk,suffix,star) ==>
  view(glob S)=ah_initial pk suffix star])=>
 (forall st,hoare[S.snapshot:view(glob S)=st ==>
  res=st /\ view(glob S)=st])=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
  view(glob S)=ah_record_state st x y])=>
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 equiv[AHCPAMonitoredKernel(A).guess ~ AHCPAMonitoredKernel(AHWrapper(S,A)).guess:
 ={s,glob A} /\ s{1}=s0 ==>
 ={SimBad.corr} /\ (!SimBad.corr{1}=> ={res})].
proof.
 move=>hv hi hs hr hinit hsnap hrecord all.
 have [hk [hg hf]]:=ah_cpa_setup_facts s0 hv.
 proc;wp.
 call(ah_phase_coupling S A view s0.`1.`1 (acwc2_gfun s0.`3)
  hk hi hs hr hinit hsnap hrecord all).
 rnd;call(ah_cpa_encrypt_coupling (acwc2_gfun s0.`3) (acwc2_g_cache s0.`3) hg).
 rnd;rnd;rnd;rnd.
 inline ROE.init ROG.init ROH.init RawXOFStreams.init;auto=> />;smt().
qed.

(* The only resource premise is the original CPA phase's distinct public
   H-record bound. The actual adversary's query order is fully adaptive. *)
lemma ah_cpa_distance
 (S<:AHStore {-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO,-FOContext,-SimBad})
 (A<:CCAExtendedAdversary {-S,-CPAReduction,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,
  -CCADecapOracle,-SimPublic,-SimHistory,-FOGRO.RO,-FOGRO.FRO,-FOContext,-SimBad})
 (view:(glob S)->ah_state) qC &m :
 islossless S.init=>islossless S.snapshot=>islossless S.record=>
 (forall pk suffix star,hoare[S.init:arg=(pk,suffix,star) ==>
  view(glob S)=ah_initial pk suffix star])=>
 (forall st,hoare[S.snapshot:view(glob S)=st ==>
  res=st /\ view(glob S)=st])=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
  view(glob S)=ah_record_state st x y])=>
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
  islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
  islossless D.decap=>islossless A(H,D).guess)=>
 0<=qC=>hoare[CPAPhase(A).run:true ==>fsize SimHistory.h<=qC]=>
 `|Pr[CPAGame(CPAReduction(A)).run()@&m:res]-
   Pr[CPAGame(CPAReduction(AHWrapper(S,A))).run()@&m:res]|
 <=qC%r/(2%r^353).
proof.
 move=>hi hs hr hinit hsnap hrecord all hq hc.
 rewrite(ah_cpa_actual_mu A &m)(ah_cpa_actual_mu (AHWrapper(S,A)) &m).
 pose K0:=fun s=>mk(fun b=>Pr[AHCPAKernel(A).guess(s)@&m:res=b]).
 pose K1:=fun s=>mk(fun b=>Pr[AHCPAKernel(AHWrapper(S,A)).guess(s)@&m:res=b]).
 have hQ:0%r<=qC%r by smt().
 have hp:forall s,s \in mk(fun z=>Pr[FOSetupSource.guess(witness)@&m:res=z])=>
  `|mu1(K0 s)true-mu1(K1 s)true|<=0%r+qC%r*fo_setup_error s.
 + move=>s hsupport.
   have hv:=fo_setup_law_support &m witness s hsupport.
   rewrite /K0 /K1 (fo_kernel_win_mu (AHCPAKernel(A)) &m s)
    (fo_kernel_win_mu (AHCPAKernel(AHWrapper(S,A))) &m s)
    -(ah_cpa_monitored_probability A s &m (fun b=>b))
    -(ah_cpa_monitored_probability (AHWrapper(S,A)) s &m (fun b=>b)) /=.
   have eqv:=ah_cpa_monitored_coupling S A view s hv hi hs hr hinit hsnap hrecord all.
   have hgood:
    Pr[AHCPAMonitoredKernel(A).guess(s)@&m:res /\ !SimBad.corr]=
    Pr[AHCPAMonitoredKernel(AHWrapper(S,A)).guess(s)@&m:res /\ !SimBad.corr].
   - byequiv eqv=> //;
     clear hi hs hr hinit hsnap hrecord all hc hv hq hQ hsupport K0 K1 eqv;
     smt().
   have hbad:
    Pr[AHCPAMonitoredKernel(A).guess(s)@&m:SimBad.corr]=
    Pr[AHCPAMonitoredKernel(AHWrapper(S,A)).guess(s)@&m:SimBad.corr].
   - byequiv eqv=> //;
     clear hi hs hr hinit hsnap hrecord all hc hv hq hQ hsupport K0 K1 eqv hgood;
     smt().
   have hl:
    Pr[AHCPAMonitoredKernel(A).guess(s)@&m:res /\ SimBad.corr]<=
    Pr[AHCPAMonitoredKernel(A).guess(s)@&m:SimBad.corr]
    by rewrite Pr[mu_sub].
   have hrp:
    Pr[AHCPAMonitoredKernel(AHWrapper(S,A)).guess(s)@&m:res /\ SimBad.corr]<=
    Pr[AHCPAMonitoredKernel(AHWrapper(S,A)).guess(s)@&m:SimBad.corr]
    by rewrite Pr[mu_sub].
   have hb:=ah_cpa_monitored_bad A s qC &m hq hc.
   rewrite Pr[mu_split SimBad.corr].
   have ->:Pr[AHCPAMonitoredKernel(AHWrapper(S,A)).guess(s)@&m:res]=
    Pr[AHCPAMonitoredKernel(AHWrapper(S,A)).guess(s)@&m:res /\ SimBad.corr]+
    Pr[AHCPAMonitoredKernel(AHWrapper(S,A)).guess(s)@&m:res /\ !SimBad.corr]
    by rewrite Pr[mu_split SimBad.corr].
   have hp0:0%r<=Pr[AHCPAMonitoredKernel(A).guess(s)@&m:res /\ SimBad.corr]
    by rewrite Pr[mu_ge0].
   have hp1:0%r<=Pr[AHCPAMonitoredKernel(AHWrapper(S,A)).guess(s)@&m:res /\ SimBad.corr]
    by rewrite Pr[mu_ge0].
   have hr2:
    Pr[AHCPAMonitoredKernel(AHWrapper(S,A)).guess(s)@&m:res /\ SimBad.corr]<=
    Pr[AHCPAMonitoredKernel(A).guess(s)@&m:SimBad.corr]
    by rewrite hbad;exact hrp.
   exact(hist_probability_split_distance _ _ _ _ _ _ hgood hp0 hp1 hl hr2 hb).
 have hzero:0%r<=0%r by done.
 have ha:=sim_setup_distance_average &m K0 K1 (pred1 true) 0%r qC%r hzero hQ hp.
 by move:ha;rewrite /K0 /K1 /=.
qed.
