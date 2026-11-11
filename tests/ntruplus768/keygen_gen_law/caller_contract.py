"""The endpoint observes actual returned key bytes; the ROM result remains approximate."""
BASE='ntruplus/proof/768/ref/keygen_gen_law/'
DIST=BASE+'NTRUPlus768GenDistribution.ec'
PROCEDURES=BASE+'NTRUPlus768GenProcedures.ec'
ROM=BASE+'NTRUPlus768GenROMBridge.ec'
RULES=(
 (PROCEDURES,'polynomial rejection sampling repeats independent proposals until the whole predicate accepts',r'module GenPolynomialRejection = { proc sample(d:NTRUPoly.poly distr,accept:NTRUPoly.poly->bool) : NTRUPoly.poly = { var p:NTRUPoly.poly; p <$ d; while(!accept p){p <$ d;} return p; } proc direct(d:NTRUPoly.poly distr,accept:NTRUPoly.poly->bool) : NTRUPoly.poly = { var p:NTRUPoly.poly; p <$ dcond d accept; return p; } }.'),
 (PROCEDURES,'Figure18 executes separate shaped-f and unscaled-g rejection stages',r'module Figure18Gen = { proc sample_fg() : NTRUPoly.poly*NTRUPoly.poly = { var f0,f,g:NTRUPoly.poly; f0 <@ GenPolynomialRejection.sample(pke_field_psi1,gen_f0_accept); f <- gen_shape_f f0; g <@ GenPolynomialRejection.sample(pke_field_psi1,pke_rq_unit); return(f,g); } proc run() : NTRUPoly.poly*NTRUPoly.poly = { var fg,key:NTRUPoly.poly*NTRUPoly.poly; fg <@ sample_fg(); key <- gen_key_from_fg fg; return key; } }.'),
 (DIST,'fresh exact law names the exported byte-key API and decoded returned pair',r'lemma gen_fresh_public_key_law &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) : Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m: event(gen_serialized_core res.`1 res.`2)]=mu gen_key_law event.'),
 (DIST,'programmed exact law names the actual recording port and decoded returned pair',r'lemma gen_programmed_public_key_law &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) : Pr[Keygen(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run() @ &m: event(gen_serialized_core res.`1 res.`2)]=mu gen_key_law event.'),
 (DIST,'programmed-to-fresh output projection retains the actual F cache',r'lemma gen_programmed_public_projection : equiv[Keygen(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run ~ Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run : ={glob ROF} ==> ={res,glob ROF}].'),
 (PROCEDURES,'literal public programmed API is equated to the Figure18 procedure only through its decoded core',r'lemma figure18_programmed_public_probability &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) : Pr[Keygen(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run() @ &m: event(gen_serialized_core res.`1 res.`2)]=Pr[Figure18Gen.run() @ &m:event res].'),
 (PROCEDURES,'literal public fresh API is equated to the actual Figure18 repeat procedure',r'lemma figure18_fresh_public_probability &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) : Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m: event(gen_serialized_core res.`1 res.`2)]=Pr[Figure18Gen.run() @ &m:event res].'),
 (ROM,'actual ROM marginal keeps the empty-E premise and certified nonzero approximation',r'lemma gen_rom_public_key_law_239 &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) : ROE.m{m}=empty => `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m: event(gen_serialized_core res.`1 res.`2)]-mu gen_key_law event| < 1%r/(2%r^239).'),
)
MUTATIONS=(
 ('polynomial-rejection-loop-is-reversed',PROCEDURES,'while(!accept p){p <$ d;}','while(accept p){p <$ d;}'),
 ('polynomial-rejection-stops-after-only-one-retry',PROCEDURES,'while(!accept p){p <$ d;}','if(!accept p){p <$ d;}'),
 ('Figure18-f-stage-tests-unit-of-unshaped-f0',PROCEDURES,'f0 <@ GenPolynomialRejection.sample(pke_field_psi1,gen_f0_accept);','f0 <@ GenPolynomialRejection.sample(pke_field_psi1,pke_rq_unit);'),
 ('Figure18-g-stage-omits-unit-conditioning',PROCEDURES,'g <@ GenPolynomialRejection.sample(pke_field_psi1,pke_rq_unit);','g <$ pke_field_psi1;'),
 ('public-fresh-endpoint-is-only-an-instrumented-witness-law',DIST,'lemma gen_fresh_public_key_law &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) : Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m: event(gen_serialized_core res.`1 res.`2)]','lemma gen_fresh_public_key_law &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) : Pr[KeygenInstrumented(UniformSeedRNG,FreshExpand,SHAKEFROM).run(witness) @ &m: event(gen_actual_core res.`1)]'),
 ('programmed-public-law-assumes-empty-E-despite-overwrite-semantics',DIST,'lemma gen_programmed_public_key_law &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) :','lemma gen_programmed_public_key_law &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) : ROE.m{m}=empty =>'),
 ('programmed-output-projection-forgets-F-cache-state',DIST,'={glob ROF} ==> ={res,glob ROF}].','={glob ROF} ==> ={res}].'),
 ('programmed-marginal-projection-is-expanded-to-false-E-table-equality',DIST,'={glob ROF} ==> ={res,glob ROF}].','={glob ROE,glob ROF} ==> ={res,glob ROE,glob ROF}].'),
 ('literal-Gen-endpoint-substitutes-bare-fresh-for-recording-expand',PROCEDURES,'lemma figure18_programmed_public_probability &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) : Pr[Keygen(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run()','lemma figure18_programmed_public_probability &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) : Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run()'),
 ('literal-Gen-endpoint-substitutes-the-marginal-law-for-the-repeat-procedure',PROCEDURES,'event(gen_serialized_core res.`1 res.`2)]=Pr[Figure18Gen.run() @ &m:event res].','event(gen_serialized_core res.`1 res.`2)]=mu gen_key_law event.'),
 ('ROM-approximation-omits-the-initial-E-table-condition',ROM,'lemma gen_rom_public_key_law_239 &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) : ROE.m{m}=empty =>','lemma gen_rom_public_key_law_239 &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) :'),
 ('ROM-approximation-is-replaced-by-exact-equality',ROM,'< 1%r/(2%r^239).','=0%r.'),
 ('ROM-law-assumes-unlimited-KeyGen-losslessness',ROM,'lemma gen_rom_public_key_law_239 &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) :','lemma gen_rom_public_key_law_239 &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) : islossless Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run =>'),
)
