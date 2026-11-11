#!/usr/bin/env python3
"""Semantic mutations and preserved strict EOF/negative diagnostic regressions."""
import json
import sys
sys.dont_write_bytecode=True
import check_kem_numerical_dfr as policy
import eof_sentinels as eof
from model_contract import MODEL,DECOMPOSITION,CBD,MGF,CONTEXT,CONVOLUTION,RECOVERY,FAILURE,ORACLES,ROM_GAME
from probability_contract import CONDITIONAL,NOWRAP,TAIL,PAYLOAD,IDEAL,TRANSFER
from calls_contract import ENCAP,TENSOR,BLOCKS
from final_contract import OBSERVATION,FINAL
from verify_kem_numerical_dfr import check_negative_diagnostic,check_sentinel

MUTATIONS=(
 (r'actual-observer-resets-F-after-KeyGen',OBSERVATION,r'rm <@ EncapBufferObservation.run(out.`1);',r'ROF.init(); rm <@ EncapBufferObservation.run(out.`1);'),
 (r'actual-Decaps-losslessness-discharge-omitted',OBSERVATION,r'call{1}(complete_lossless SHAKEGROM SHAKEHROM ro_g_shake_ll ro_h_shake_ll).',r''),
 (r'actual-private-bad-flag-replaced-with-failure',OBSERVATION,r'lemma rom_private_uniform_observation : equiv[KEMROMPrivate(UniformKEMRNG).run ~ InitializedKeygenThenUniform(ExpandROM).run : true ==> res.`2{1}= !honest_no_wrap res{2}]',r'lemma rom_private_uniform_observation : equiv[KEMROMPrivate(UniformKEMRNG).run ~ InitializedKeygenThenUniform(ExpandROM).run : true ==> res.`1{1}= !honest_no_wrap res{2}]'),
 (r'final-bound-assumes-positive-acceptance',FINAL,r'lemma numerical_rom_dfr_total &m :',r'lemma numerical_rom_dfr_total &m : 0%r<fresh_f_accept_mass =>'),
 (r'final-bound-assumes-empty-E-initially',FINAL,r'lemma numerical_rom_dfr_total &m :',r'lemma numerical_rom_dfr_total &m : ROE.m{m}=empty =>'),
 (r'final-bound-assumes-real-return-mass-one',FINAL,r'lemma numerical_rom_dfr_total &m :',r'lemma numerical_rom_dfr_total &m : Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : true]=1%r =>'),
 (r'final-total-omits-real-nonreturn',FINAL,r'lemma numerical_rom_dfr_total &m : Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : res] + (1%r-Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : true])',r'lemma numerical_rom_dfr_total &m : Pr[KEMROMCorrectness(UniformKEMRNG).run() @ &m : res]'),
 (r'final-total-substitutes-reference-KEM',FINAL,r'lemma numerical_rom_dfr_total &m : Pr[KEMROMCorrectness(UniformKEMRNG).run()',r'lemma numerical_rom_dfr_total &m : Pr[ReferenceKEM.run()'),
 (r'final-ideal-bound-substitutes-raw-buffers',FINAL,r'lemma conditioned_no_wrap_numerical : mu accepted_four_law four_buffers_bad',r'lemma conditioned_no_wrap_numerical : mu raw_four_law four_buffers_bad'),

 (r'four-buffer-tensor-duplicates-key-f',CBD,r'cbd_pair_blocks perm (bs.`1.`2,bs.`2.`1) ++ cbd_pair_blocks perm (bs.`2.`2,bs.`1.`1)',r'cbd_pair_blocks perm (bs.`1.`1,bs.`2.`1) ++ cbd_pair_blocks perm (bs.`2.`2,bs.`1.`1)'),
 (r'block-permutation-injectivity-premise-omitted',CBD,r'lemma cbd_four_blocks_uniform perm : (forall i j,0<=i<384=>0<=j<384=>perm i=perm j=>i=j) =>',r'lemma cbd_four_blocks_uniform perm :'),
 (r'four-buffer-block-count-halved',CBD,r'(cbd_four_blocks perm)=dlist dcbd_quad 768',r'(cbd_four_blocks perm)=dlist dcbd_quad 384'),

 (r'actual-Encaps-observation-skipped',ENCAP,r'(er,coins) <@ EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,UniformCoins).run(w.`kg_pk,witness);',r'(er,coins) <@ ReferenceEncap.run(w.`kg_pk,witness);'),
 (r'actual-Encaps-H-query-uses-cleared-coins',ENCAP,r'h <- oget ROH.m.[(coins,complete_sk_suffix w.`kg_sk)];',r'h <- oget ROH.m.[(witness,complete_sk_suffix w.`kg_sk)];'),
 (r'actual-Encaps-G-query-substituted',ENCAP,r'p <- oget ROG.m.[payload_serialized h];',r'p <- oget ROG.m.[witness];'),
 (r'actual-fresh-H-premise-removed',ENCAP,r'ROF.m{1}=fm0 /\ ROH.m{1}=empty ==>',r'ROF.m{1}=fm0 ==>'),
 (r'actual-fresh-G-premise-removed',ENCAP,r'hashout{1}=h0 /\ ROG.m{1}=empty ==>',r'hashout{1}=h0 ==>'),
 (r'actual-Encaps-workspace-clear-discharge-skipped',ENCAP,r'call{1} encap_clear_lossless.',r''),
 (r'actual-Encaps-coins-clear-discharge-skipped',ENCAP,r'call{1} encap_clear_coins_lossless.',r''),
 (r'tensor-half-pairing-loses-coordinates',TENSOR,r'dmap (dlist d (2*n)) (cbd_tensor_halves x0 n)',r'dmap (dlist d n) (cbd_tensor_halves x0 n)'),
 (r'tensor-left-coordinate-reused',TENSOR,r'(nth x0 ab.`1 i,nth x0 ab.`1 (i+n))',r'(nth x0 ab.`1 i,nth x0 ab.`1 i)'),
 (r'tensor-right-coordinate-reused',TENSOR,r'(nth x0 ab.`2 (perm i),nth x0 ab.`2 (perm i+n))',r'(nth x0 ab.`2 (perm i),nth x0 ab.`2 (perm i))'),

 (r'conditioning-f-acceptance-omitted',CONDITIONAL,r'keygen_f_accept bs.`1.`1 /\ keygen_g_accept bs.`1.`2',r'keygen_g_accept bs.`1.`2'),
 (r'conditioning-denominator-loses-g',CONDITIONAL,r'/ (fresh_f_accept_mass*fresh_g_accept_mass)',r'/ fresh_f_accept_mass'),
 (r'conditioning-factor-omitted',CONDITIONAL,r'mu accepted_four_law event <= (64%r/25%r)*mu raw_four_law event',r'mu accepted_four_law event <= mu raw_four_law event'),
 (r'no-wrap-tail-excludes-576-boundary',NOWRAP,r'576<=`|(sampled_m1_noise fbuf gbuf r m).[k]|',r'576<`|(sampled_m1_noise fbuf gbuf r m).[k]|'),
 (r'tail-loses-negative-sign',TAIL,r'op noise_coefficient_bound = 2%r*noise_mgf_base^768/(2%r^576)',r'op noise_coefficient_bound = noise_mgf_base^768/(2%r^576)'),
 (r'tail-counts-one-convolution-only',TAIL,r'op noise_coefficient_bound = 2%r*noise_mgf_base^768/(2%r^576)',r'op noise_coefficient_bound = 2%r*noise_mgf_base^384/(2%r^576)'),
 (r'tail-union-count-halved',TAIL,r'op noise_unconditional_bound = 1536%r*noise_mgf_base^768/(2%r^576)',r'op noise_unconditional_bound = 768%r*noise_mgf_base^768/(2%r^576)'),
 (r'tail-independent-join-shortened',TAIL,r'size ds=768 =>',r'size ds=384 =>'),
 (r'H-tail-offset-shifted',PAYLOAD,r'else p.`2.[i-32]',r'else p.`2.[i-31]'),
 (r'H-tail-law-truncated',PAYLOAD,r'dmap uniform224 complete_hash_tail=uniform192',r'dmap uniform224 complete_hash_tail=uniform96'),
 (r'payload-fixes-SOTP-coins',PAYLOAD,r'poly_sotp_encode_input coins hp.`2',r'poly_sotp_encode_input witness hp.`2'),
 (r'ideal-keygen-clear-seam-omitted',IDEAL,r'call{1} keygen_clear_lossless.',r''),
 (r'ideal-keygen-finish-seam-omitted',IDEAL,r'call{1}(keygen_finish_lossless SHAKEFROM ro_f_shake_ll).',r''),
 (r'ideal-keygen-f-retry-seam-omitted',IDEAL,r'call fresh_retry_g_accepted_buffer; call fresh_retry_f_accepted_buffer;',r'call fresh_retry_g_accepted_buffer;'),
 (r'ideal-keygen-g-retry-seam-omitted',IDEAL,r'call fresh_retry_g_accepted_buffer; call fresh_retry_f_accepted_buffer;',r'call fresh_retry_f_accepted_buffer;'),
 (r'postprocessing-real-nonreturn-omitted',TRANSFER,r'!honest_no_wrap res] + (1%r-Pr[KeygenThenUniform(ExpandROM).run() @ &m : true])',r'!honest_no_wrap res] + 0%r'),

 (r'monomial-middle-sign-flipped',CONVOLUTION,r'integer_scale (-1) (integer_unit (s - 768))',r'integer_scale 1 (integer_unit (s - 768))'),
 (r'monomial-high-sign-flipped',CONVOLUTION,r'else integer_scale (-1) (integer_unit (s - 1152))',r'else integer_unit (s - 1152)'),
 (r'noise-lift-rescaling-omitted',RECOVERY,r'integer_scale 3 (sampled_m1_noise fbuf gbuf r m)',r'integer_scale 1 (sampled_m1_noise fbuf gbuf r m)'),
 (r'no-wrap-message-constant-omitted',RECOVERY,r'integer_add (integer_coefficients m) (integer_scale 3 (sampled_m1_noise fbuf gbuf r m))',r'integer_scale 3 (sampled_m1_noise fbuf gbuf r m)'),
 (r'no-wrap-threshold-off-by-one',RECOVERY,r'<= 1728.',r'< 1728.'),
 (r'block-partner-wrong-modulus',DECOMPOSITION,r'(k-i) %%384',r'(k-i) %%768'),
 (r'block-reduction-high-sign-flipped',DECOMPOSITION,r'else -b2i(k=s-1152)',r'else b2i(k=s-1152)'),
 (r'block-carry-boundary-off-by-one',DECOMPOSITION,r'if i<=k then a*b-c*d',r'if i<k then a*b-c*d'),
 (r'block-diagonal-sign-flipped',DECOMPOSITION,r'a*b-c*d else -(a*d+c*b+c*d)',r'a*b+c*d else -(a*d+c*b+c*d)'),
 (r'block-negative-path-sign-flipped',DECOMPOSITION,r'else -(a*d+c*b+c*d)',r'else (a*d+c*b+c*d)'),
 (r'block-fourth-case-term-omitted',DECOMPOSITION,r'else a*b+a*d+c*b',r'else a*b+c*b'),
 (r'block-coordinate-overlap',DECOMPOSITION,r'a.[i] a.[i+384]',r'a.[i] a.[i]'),
 (r'block-384-sum-truncated',DECOMPOSITION,r'b.[noise_partner k i+384]) 0 384',r'b.[noise_partner k i+384]) 0 383'),
 (r'CBD-zero-weight-wrong',CBD,r'if u=0 then -1 else if u=3 then 1 else 0',r'if u=0 then -1 else if u<3 then 1 else 0'),
 (r'CBD-head-tail-pair-alias',CBD,r'if i %% 2=0 then i %/ 2 else 768+i %/ 2',r'if i %% 2=0 then i %/ 2 else i %/ 2'),
 (r'CBD-conditioned-coefficients-asserted-iid',CBD,r'lemma cbd_coeff_list_uniform : dmap uniform192 cbd_coeff_list=dlist dcbd 768',r'lemma cbd_coeff_list_uniform : dmap (dcond uniform192 keygen_f_accept) cbd_coeff_list=dlist dcbd 768'),
 (r'MGF-three-products-assumed-independent',MGF,r'op noise_mgf_base = 1237%r/1024%r',r'op noise_mgf_base = (17%r/16%r)^3'),
 (r'MGF-sign-ignored',MGF,r'E d (fun x=>2%r^(s*x))',r'E d (fun x=>2%r^x)'),
 (r'observer-forgets-actual-f-buffer',CONTEXT,r'x.`1.`1.`kg_fbuf x.`1.`1.`kg_gbuf',r'witness x.`1.`1.`kg_gbuf'),
 (r'whole-key-f-conditioning-omitted',MODEL,r'((dcond uniform192 keygen_f_accept) `*` (dcond uniform192 keygen_g_accept))',r'(uniform192 `*` (dcond uniform192 keygen_g_accept))'),
 (r'whole-key-g-conditioning-omitted',MODEL,r'((dcond uniform192 keygen_f_accept) `*` (dcond uniform192 keygen_g_accept))',r'((dcond uniform192 keygen_f_accept) `*` uniform192)'),
 (r'bad-event-negation-omitted',MODEL,r'!sampled_m1_no_wrap f g',r'sampled_m1_no_wrap f g'),
 (r'honest-coins-frozen',MODEL,r'x <$ uniform96;',r'x <- witness;'),
 (r'honest-seed-law-truncated',MODEL,r'x <$ uniform32;',r'x <$ uniform96;'),
 (r'postprocessor-reads-ROM-state',CONTEXT,r'return honest_no_wrap(x,rbuf,mbuf);',r'return honest_no_wrap(x,rbuf,mbuf) /\ ROG.m=empty;'),
 (r'postprocessor-skips-r-sample',CONTEXT,r'rbuf <$ uniform192; mbuf <$ uniform192; return honest_no_wrap',r'rbuf <- witness; mbuf <$ uniform192; return honest_no_wrap'),
 (r'keygen-approximation-tail-omitted',CONTEXT,r'op keygen_observer_error = 130818%r/(2%r^256)',r'op keygen_observer_error = 130816%r/(2%r^256)'),
 (r'post-keygen-hash-frame-allows-G-changes',CONTEXT,r'(E<:KeygenExpand {-ROG,-ROH})',r'(E<:KeygenExpand {-ROH})'),
 (r'post-keygen-hash-frame-allows-H-changes',CONTEXT,r'(E<:KeygenExpand {-ROG,-ROH})',r'(E<:KeygenExpand {-ROG})'),
 (r'actual-Encaps-RNG-skipped',FAILURE,r'coins <@ Q.sample();',r'coins <- witness;'),
 (r'actual-Encaps-coin-clear-skipped',FAILURE,r'coins <@ NTRUPlus768EncapClearCoins.M.jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins(coins);',r'coins <- witness;'),
 (r'actual-Encaps-caller-substituted',FAILURE,r'er <@ EncapRandom(F,G,H,Q).run(pk,witness);',r'er <@ ReferenceEncap.run(pk,witness);'),
 (r'actual-Decaps-caller-substituted',FAILURE,r'dr <@ CompleteDecaps(G,H).run(er.`1,sk,witness);',r'dr <@ ReferenceDecaps.run(er.`1,sk,witness);'),
 (r'actual-failure-Encaps-status-omitted',FAILURE,r'er.`3 <> W32.zero \/ dr.`2 <> W32.zero',r'dr.`2 <> W32.zero'),
 (r'actual-failure-Decaps-status-omitted',FAILURE,r'er.`3 <> W32.zero \/ dr.`2 <> W32.zero',r'er.`3 <> W32.zero'),
 (r'actual-failure-shared-key-mismatch-omitted',FAILURE,r'\/ er.`2 <> dr.`1',r''),
 (r'fresh-G-key-absence-forgotten',ORACLES,r'ROG.m=m0 /\ input=x0 /\ x0 \notin m0 ==> res=y0',r'ROG.m=m0 /\ input=x0 ==> res=y0'),
 (r'fresh-H-key-absence-forgotten',ORACLES,r'ROH.m=m0 /\ input=x0 /\ x0 \notin m0 ==> res=y0',r'ROH.m=m0 /\ input=x0 ==> res=y0'),
 (r'actual-ROM-game-skips-H-initialization',ROM_GAME,r'ROE.init(); ROF.init(); ROG.init(); ROH.init();',r'ROE.init(); ROF.init(); ROG.init();'),
)


def main():
    controls=[]
    policy.check_structure()
    for inventory in (eof.SENTINELS,eof.SEMANTIC_TARGETS,eof.MODULE_BINDERS,eof.NEGATIVE_PROOFS):
        policy.require(set(inventory)==set(policy.MAINS),'semantic EOF inventory drift')
    for name,sentinel in eof.SENTINELS.items():
        check_sentinel(name,sentinel,eof.SEMANTIC_TARGETS[name],eof.MODULE_BINDERS[name])
    def rejects(label,action):
        try:action()
        except (ValueError,AssertionError,IndexError):
            controls.append({'label':label,'result':'EXPECTED_REJECTION'});return
        raise AssertionError('accepted negative control: '+label)
    for label,relative,old,new in MUTATIONS:
        text=policy.compact((policy.ROOT/relative).read_text()).replace('op[opaque]','op')
        old,new=(policy.compact(value).replace('op[opaque]','op') for value in (old,new))
        policy.require(old in text,'absent mutation target: '+label)
        altered=text.replace(old,new,1)
        policy.require(altered!=text,'ineffective mutation: '+label)
        rejects(label,lambda relative=relative,altered=altered:policy.check_structure({relative:altered}))
    for label,text in (
        ('admitted-proof','lemma forged : false. proof. admit. qed.'),
        ('assumed-acceptance-positivity','axiom fresh_f_positive : 0%r<fresh_f_accept_mass.'),
        ('disabled-checker','pragma -check.'),
        ('abstract-local-law','op arbitrary_acceptance : real.'),
        ('unclosed-comment','(* mask the final proof'),
    ):
        rejects(label,lambda text=text:policy.check_proof_text(text))
    own='/isolated/0/Main.ec'
    valid='[critical] ['+own+': line 80] cannot process [axiom] inside a proof script'
    check_negative_diagnostic(valid,own)
    rejects('eof-wrong-main',lambda:check_negative_diagnostic(valid,'/isolated/1/Other.ec'))
    rejects('eof-import-contamination',lambda:check_negative_diagnostic(
        '[critical] ['+own+': line 4] In external theory Broken: cannot process [axiom] inside a proof script',own))
    rejects('eof-unrelated-error',lambda:check_negative_diagnostic(
        '[critical] ['+own+': line 80] unknown type',own))
    rejects('eof-wrong-command-inside-proof',lambda:check_negative_diagnostic(
        '[critical] ['+own+': line 80] cannot process [module] inside a proof script',own))
    sentinel='lemma __test (P <: ProposalPort) : islossless P.draw => islossless PairPorts(P).sample. proof. exact (pair_ports_sample_lossless P). qed.'
    def validates(s):check_sentinel('fixture',s,'pair_ports_sample_lossless',('P',))
    validates(sentinel)
    rejects('eof-implicit-module-binder',lambda:validates(sentinel.replace('P <: ProposalPort','P : ProposalPort')))
    rejects('eof-wrong-semantic-target',lambda:validates(sentinel.replace('exact (pair_ports_sample_lossless','exact (irrelevant')))
    rejects('eof-target-suffix-forgery',lambda:validates(sentinel.replace('exact (pair_ports_sample_lossless','exact (pair_ports_sample_lossless_unreviewed')))
    rejects('eof-open-sentinel',lambda:validates(sentinel.replace('qed.','')))
    rejects('eof-constant-proposition',lambda:validates('lemma __test (P <: ProposalPort) : true. proof. exact pair_ports_sample_lossless. qed.'))
    source='lemma pair_value (P <: ProposalPort) : hoare[PairPorts(P).shake : true ==> res=PairPorts.pending]. proof. proc; auto. qed.'
    valid_sentinel='lemma __test (P <: ProposalPort) : hoare[PairPorts(P).shake : true ==> res=PairPorts.pending]. proof. exact (pair_value P). qed.'
    check_sentinel('fixture',valid_sentinel,'pair_value',('P',),source_text=source)
    rejects('eof-functor-global-instantiation',lambda:check_sentinel('fixture',
        valid_sentinel.replace('PairPorts.pending','PairPorts(P).pending'),'pair_value',('P',),source_text=source))
    policy.require(len(controls)==len(MUTATIONS)+15,'control inventory drift')
    print(json.dumps({'status':'PASS','declared':len(MUTATIONS)+15,'count':len(controls),'controls':controls,
                      'main_inventory':'FROZEN' if (policy.TEST/'source-pins.json').is_file() else 'DECLARED_NOT_PINNED' if policy.MAINS else 'PENDING_FREEZE',
                      'semantic_eof_count':len(eof.SENTINELS)}))


if __name__=='__main__':main()
