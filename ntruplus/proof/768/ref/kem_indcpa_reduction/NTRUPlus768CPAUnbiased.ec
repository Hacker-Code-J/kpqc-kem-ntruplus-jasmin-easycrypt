require import AllCore Distr DProd DBool FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152 Array2336.
require import NTRUPlus768PKEProcedures NTRUPlus768PKEModel NTRUPlus768SOTPContracts NTRUPlus768FOProcedures NTRUPlus768PolyCBD1Checked.
require import NTRUPlus768CPAModel NTRUPlus768CPAReduction NTRUPlus768CPAChallenge.
require import NTRUPlus768RawXOF NTRUPlus768AcceptanceProbability.
require import NTRUPlus768HashPayloadSampling NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768CCAGame NTRUPlus768CCAOraclePorts NTRUPlus768CCADecapOracle.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions NTRUPlus768RawXOFStreams NTRUPlus768FreshRetryLaw NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768SimLookup NTRUPlus768SimModel NTRUPlus768FOGAdapters NTRUPlus768FOEagerG NTRUPlus768KEMPayloadSpec.

(* The actual fresh challenge is retained, but its H entry is not programmed.
   The second return component records only the final public H-history hit. *)
module CPAErased(A:CCAExtendedAdversary) = {
 proc run() : bool * bool = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var msg:W8.t Array96.t;var hout:W8.t Array224.t;
  var suffix,random:W8.t Array32.t;var ct:W8.t Array1152.t option;
  var bit,guess:bool;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  msg<$uniform96;hout<$uniform224;suffix<@ROF.get(pk);
  ct<@SimEncrypt(FOGActual).run(pk,msg,hout);
  random<$uniform32;bit<$dbool;
  guess<@CPAPhase(A).run(pk,oget ct,if bit then random else payload_shared_key hout);
  return (guess=bit,(msg,SimPublic.suffix) \in SimHistory.h);
 }
}.
(* Joint law, rather than separate marginal laws: encryption sees only the
   192-byte tail, while either selected 32-byte key is fresh and independent. *)
module CPACoins = {
 proc sample(bit:bool): W8.t Array192.t * W8.t Array32.t = {
  var hout:W8.t Array224.t;var random:W8.t Array32.t;var result: W8.t Array192.t * W8.t Array32.t;
  hout<$uniform224;random<$uniform32;
  result<-(complete_hash_tail hout,if bit then random else payload_shared_key hout);return result;
 }
 proc independent(bit:bool): W8.t Array192.t * W8.t Array32.t = {
  var tail:W8.t Array192.t;var key:W8.t Array32.t;var result: W8.t Array192.t * W8.t Array32.t;
  tail<$uniform192;key<$uniform32;result<-(tail,key);return result;
 }
}.
module type CPACoinPort = {proc sample(bit:bool):W8.t Array192.t * W8.t Array32.t}.
module CPAIndependentCoins = {proc sample=CPACoins.independent}.
module CPAUsingCoins(A:CCAExtendedAdversary,C:CPACoinPort) = {
 proc run() : bool * bool = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var msg:W8.t Array96.t;var coins:W8.t Array192.t * W8.t Array32.t;
  var suffix:W8.t Array32.t;var ct:W8.t Array1152.t option;var bit,guess:bool;
  ROMInit.init();RawXOFStreams.init();
  (pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();
  msg<$uniform96;bit<$dbool;coins<@C.sample(bit);suffix<@ROF.get(pk);
  ct<@SimEncrypt(FOGActual).run(pk,msg,hash_join(witness,coins.`1));
  guess<@CPAPhase(A).run(pk,oget ct,coins.`2);
  return(guess=bit,(msg,SimPublic.suffix) \in SimHistory.h);
 }
}.
module type CPAPKEPort = {proc run(pk:W8.t Array1152.t,m r:pke_poly):W8.t Array1152.t option}.
module type CPASOTPPort = {proc run(msg:W8.t Array96.t,pad:W8.t Array192.t):pke_poly}.
module type CPAGHashPort = {proc run(r:pke_poly):W8.t Array192.t}.
module type CPACBDPort = {proc jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(rp:pke_poly,buf:W8.t Array192.t):pke_poly}.
lemma cpa_pke_same (M<:CPAPKEPort):equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma cpa_sotp_same (M<:CPASOTPPort):equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma cpa_ghash_same (M<:CPAGHashPort):equiv[M.run ~ M.run: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma cpa_cbd_same (M<:CPACBDPort):
 equiv[M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1 ~ M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma cpa_encrypt_tail :
 equiv[SimEncrypt(FOGActual).run ~ SimEncrypt(FOGActual).run:
 ={pk,msg,ROG.m} /\ complete_hash_tail hout{1}=complete_hash_tail hout{2} ==>
 ={res,ROG.m}].
proof.
 proc;call(cpa_pke_same PKEEnc);call(cpa_sotp_same SOTPEncode);
 call(cpa_ghash_same (FOHashG(FOGHash(FOGActual))));
 call(cpa_cbd_same NTRUPlus768PolyCBD1Checked.M);auto.
qed.
lemma cpa_tail_head_law :
 dmap uniform224 (fun h=>(complete_hash_tail h,payload_shared_key h)) =
 uniform192 `*` uniform32.
proof.
 rewrite -uniform224_join_law dmap_comp.
 have he : ((fun h:W8.t Array224.t=>(complete_hash_tail h,payload_shared_key h)) \o hash_join) =
  (fun p:W8.t Array32.t * W8.t Array192.t=>(p.`2,p.`1)).
 + by apply fun_ext=>p;rewrite /(\o) /= hash_join_tail -cpa_hash_headE hash_join_head.
 by rewrite he -dprodC.
qed.
lemma cpa_pair_law :
 dlet uniform192 (fun tail=>dmap uniform32 (fun key=>(tail,key)))=uniform192 `*` uniform32.
proof. by rewrite /dmap -dprod_dlet. qed.
lemma cpa_coins_true_law :
 dlet uniform224 (fun h=>dmap uniform32 (fun r=>(complete_hash_tail h,r)))=uniform192 `*` uniform32.
proof.
 have h:=dmap_dprodL uniform224 uniform32 complete_hash_tail.
 move:h;rewrite uniform224_tail_law dmap_dprodE /= =>h;apply/eq_sym;exact h.
qed.
lemma cpa_coins_false_law :
 dlet uniform224 (fun h=>dmap uniform32 (fun (_:W8.t Array32.t)=>(complete_hash_tail h,payload_shared_key h)))=uniform192 `*` uniform32.
proof.
 rewrite -cpa_tail_head_law /dmap;apply eq_dlet=> // h.
 by rewrite dlet_cst 1:uniform32_ll.
qed.
lemma cpa_coins_uniform : equiv[CPACoins.sample ~ CPACoins.independent:
 true ==> ={res}].
proof.
 proc;case(bit{1}).
 + rndsem*{1} 0; rndsem*{2} 0; rnd;auto=> /> &1 hb.
   by rewrite cpa_pair_law cpa_coins_true_law.
 rndsem*{1} 0; rndsem*{2} 0; rnd;auto=> /> &1 hb.
 by rewrite cpa_pair_law cpa_coins_false_law.
qed.

module type CPAFPort = {proc get(input:W8.t Array1152.t):W8.t Array32.t}.
lemma cpa_f_same (M<:CPAFPort) : equiv[M.get ~ M.get: ={arg,glob M} ==> ={res,glob M}].
proof. proc true;auto. qed.
lemma cpa_erased_coins (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) :
 equiv[CPAErased(A).run ~ CPAUsingCoins(A,CPACoins).run:
 ={glob CPAErased(A)} ==> ={res,glob CPAErased(A)}].
proof.
 proc;inline{2} CPACoins.sample.
 swap{1} 9 -4;swap{1} 9 -2.
 wp;call(cpa_phase_same (CPAPhase(A)));
 call cpa_encrypt_tail;call(cpa_f_same ROF);wp;
 rnd;rnd;wp;rnd;rnd;
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM)));
 call(cpa_init_same RawXOFStreams);call(cpa_init_same ROMInit);
 auto=> />;smt(hash_join_tail).
qed.
lemma cpa_using_coins_independent (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) :
 equiv[CPAUsingCoins(A,CPACoins).run ~ CPAUsingCoins(A,CPAIndependentCoins).run:
 ={glob CPAErased(A)} ==> ={res,glob CPAErased(A)}].
proof.
 proc;wp;call(cpa_phase_same (CPAPhase(A)));call cpa_encrypt_tail;
 call(cpa_f_same ROF);call cpa_coins_uniform;rnd;rnd;
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM)));
 call(cpa_init_same RawXOFStreams);call(cpa_init_same ROMInit);auto.
qed.

(* The final fair bit is sampled after the lossless adversarial phase.
   Robust adversary losslessness is needed for probability exactly one half. *)
lemma cpa_independent_unbiased
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) :
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 phoare[CPAUsingCoins(A,CPAIndependentCoins).run:true ==>res.`1]= (1%r/2%r).
proof.
 move=>all;proc;inline CPAIndependentCoins.sample;
 kill 6 ! 1;first by auto.
 swap 5 7.
 seq 11 : true 1%r (1%r/2%r) 0%r 0%r true => //.
 + call(cpa_phase_ll A all);call(sim_encrypt_lossless FOGActual rog_get_ll);
   call rof_get_ll;wp;rnd;rnd;rnd;
   call fresh_keygen_lossless_unconditional;call raw_stream_init_ll;call rom_init_ll;
   auto;smt(uniform96_ll uniform192_ll uniform32_ll).
 rnd;auto=> /> &hr;rewrite dboolE /=;case(guess{hr});smt().
qed.
lemma cpa_erased_unbiased
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) &m :
 (forall(H<:CCAExtendedOraclePort {-A})(D<:CCADecapPort {-A}),
 islossless H.e=>islossless H.f=>islossless H.g=>islossless H.h=>islossless H.raw=>
 islossless D.decap=>islossless A(H,D).guess)=>
 Pr[CPAErased(A).run()@&m:res.`1]= (1%r/2%r).
proof.
 move=>all.
 have h1:Pr[CPAErased(A).run()@&m:res.`1]=Pr[CPAUsingCoins(A,CPACoins).run()@&m:res.`1]
  by byequiv(cpa_erased_coins A)=> //.
 have h2:Pr[CPAUsingCoins(A,CPACoins).run()@&m:res.`1]=Pr[CPAUsingCoins(A,CPAIndependentCoins).run()@&m:res.`1]
  by byequiv(cpa_using_coins_independent A)=> //.
 rewrite h1 h2;byphoare(cpa_independent_unbiased A all)=> //.
qed.

module CPATrueCoins = {
 proc sample(bit:bool):W8.t Array192.t * W8.t Array32.t = {
  var result;result<@CPACoins.sample(true);return result;
 }
}.
lemma cpa_true_independent : equiv[CPATrueCoins.sample ~ CPAIndependentCoins.sample:
 true ==> ={res}].
proof. proc*;inline{1} CPATrueCoins.sample;wp;call cpa_coins_uniform;auto. qed.
lemma cpa_true_using_independent (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) :
 equiv[CPAUsingCoins(A,CPATrueCoins).run ~ CPAUsingCoins(A,CPAIndependentCoins).run:
 ={glob CPAErased(A)} ==> ={res,glob CPAErased(A)}].
proof.
 proc;wp;call(cpa_phase_same (CPAPhase(A)));call cpa_encrypt_tail;
 call(cpa_f_same ROF);call cpa_true_independent;rnd;rnd;
 call(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM)));
 call(cpa_init_same RawXOFStreams);call(cpa_init_same ROMInit);auto.
qed.
require import NTRUPlus768ROMKeygen NTRUPlus768SimLookupGameBridge.
(* The extra F(pk) read is already cached by the actual public KeyGen.
   This property is proved from its existing contract, not assumed. *)
lemma cpa_keygen_f_present :
 hoare[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run:true ==> res.`1 \in ROF.m].
proof.
 conseq(rom_keygen_public UniformSeedRNG FreshExpand)=> />.
 rewrite /rom_key_relation; smt(domE).
qed.
lemma cpa_keygen_f_same :
 equiv[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run ~ Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run:
 ={glob Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM)} ==>
 ={res,glob Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM)} /\ res{1}.`1 \in ROF.m{1}].
proof.
 conseq(cpa_gen_same (Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM))) cpa_keygen_f_present _;auto.
qed.
lemma cpa_true_unprogrammed (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) :
 equiv[CPAUsingCoins(A,CPATrueCoins).run ~ CPAUnprogrammed(A).run:
 ={glob CPAErased(A)} ==> res{1}.`2=res{2}].
proof.
 proc;inline{1} CPATrueCoins.sample CPACoins.sample;inline{2} CPACipher.run.
 swap{2} 10 -2.
 wp;call(cpa_phase_same (CPAPhase(A)));wp;call cpa_encrypt_tail;
 ecall{1}(sim_lookup_f_cached ROF.m{1} pk{1} (oget ROF.m{1}.[pk{1}]));wp;
 rnd;rnd;wp;rnd{1};rnd;call cpa_keygen_f_same;
 call(cpa_init_same RawXOFStreams);call(cpa_init_same ROMInit);
 auto=> />.
 move=> result fm hdom msg hm bit hb hout hh random hr.
 rewrite hash_join_tail /=.
 apply(some_oget fm.[result.`1]);by move:hdom;rewrite domE.
qed.
(* Equality of returning hit probabilities does not require adversary LL. *)
lemma cpa_erased_hit
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory}) &m :
 Pr[CPAErased(A).run()@&m:res.`2]=Pr[CPAUnprogrammed(A).run()@&m:res].
proof.
 have h1:Pr[CPAErased(A).run()@&m:res.`2]=Pr[CPAUsingCoins(A,CPACoins).run()@&m:res.`2]
  by byequiv(cpa_erased_coins A)=> //.
 have h2:Pr[CPAUsingCoins(A,CPACoins).run()@&m:res.`2]=Pr[CPAUsingCoins(A,CPAIndependentCoins).run()@&m:res.`2]
  by byequiv(cpa_using_coins_independent A)=> //.
 have h3:Pr[CPAUsingCoins(A,CPATrueCoins).run()@&m:res.`2]=Pr[CPAUsingCoins(A,CPAIndependentCoins).run()@&m:res.`2]
  by byequiv(cpa_true_using_independent A)=> //.
 rewrite h1 h2 -h3;byequiv(cpa_true_unprogrammed A)=> //.
qed.
