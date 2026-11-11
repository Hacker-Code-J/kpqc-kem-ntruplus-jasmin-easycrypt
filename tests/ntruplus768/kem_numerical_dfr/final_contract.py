"""Link actual initialized KEM calls to the final failure-plus-missing bound."""
PREFIX='ntruplus/proof/768/ref/kem_numerical_dfr/'
OBSERVATION=PREFIX+'NTRUPlus768ROMDFRObservation.ec'
FINAL=PREFIX+'NTRUPlus768NumericalDFR.ec'


def check_final(read,ordered,require):
    def has(code,token,label):
        wanted=''.join(token.split()).replace('op[opaque]','op')
        require(wanted in code.replace('op[opaque]','op'),label)
    observation=read(OBSERVATION)
    actual=observation.split('moduleROMKeygenEncapObservation=',1)[1].split('moduleInitializedKeygenThenUniform',1)[0]
    ordered(actual,('ROE.init(); ROF.init(); ROG.init(); ROH.init();',
        'out <@ KeygenInstrumented(UniformSeedRNG,ExpandROM,SHAKEFROM).run(witness);',
        'rm <@ EncapBufferObservation.run(out.`1);','return(out,rm.`1,rm.`2);'))
    require(actual.count('.init()')==4,'actual observer must retain one initial reset and no post-keygen cache reset')
    has(observation,'call{1}(complete_lossless SHAKEGROM SHAKEHROM ro_g_shake_ll ro_h_shake_ll).','actual Decaps is removed from bad observation only through its proved losslessness')
    private=observation.split('lemmarom_private_uniform_observation',1)[1].split('proof.',1)[0]
    has(private,'equiv[KEMROMPrivate(UniformKEMRNG).run ~ InitializedKeygenThenUniform(ExpandROM).run : true ==> res.`2{1}= !honest_no_wrap res{2}].','bridge must project the private no-wrap flag of the original KEM experiment')
    mass=observation.split('lemmainitialized_rom_return_mass',1)[1].split('proof.',1)[0]
    has(mass,'Pr[KEMROMPrivate(UniformKEMRNG).run() @ &m : true] = Pr[InitializedKeygenThenUniform(ExpandROM).run() @ &m : true].','actual private return mass must be preserved without assuming it equals one')
    final=read(FINAL)
    total=final.split('lemmanumerical_rom_dfr_total',1)[1].split('proof.',1)[0]
    expected='&m : Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : res] + (1%r-Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : true]) < 1%r/(2%r^238).'
    require(total==''.join(expected.split()),'final theorem must bound original public KEM failure plus nonreturning mass unconditionally')
    conditioned=final.split('lemmaconditioned_no_wrap_numerical',1)[1].split('proof.',1)[0]
    require(conditioned==':muaccepted_four_lawfour_buffers_bad<1%r/(2%r^354).','ideal no-wrap bound must target whole-key conditioned buffers without extra hypotheses')
    has(final,'mu accepted_four_law four_buffers_bad+keygen_observer_error < 1%r/(2%r^238).','final error must include actual KeyGen approximation cost')
    has(final,'inline ROE.init ROF.init ROG.init ROH.init; auto.','empty-cache premise must be discharged by the actual initialization')
    success=final.split('lemmanumerical_rom_success_mass',1)[1].split('proof.',1)[0]
    has(success,'1%r-1%r/(2%r^238) < Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : !res].','success mass must refer to the same original public KEM experiment')
    require('islosslessKEMROMCorrectness(UniformKEMRNG).run' not in final and
            'islosslessKEMROMPrivate(UniformKEMRNG).run' not in final,
            'final numerical bound must not assume actual unlimited-ROM termination')
