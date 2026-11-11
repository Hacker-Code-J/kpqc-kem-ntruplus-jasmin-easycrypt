#!/usr/bin/env python3
"""Semantic mutation controls and preserved diagnostic/EOF regressions."""
import json
import sys
sys.dont_write_bytecode=True
import check_keygen_acceptance as policy
import eof_sentinels as eof
from model_contract import ROOTS, ORBIT, ALGEBRA, BUDGET, SHAPING, ACCEPT, COLLISION, INPUT, PROBABILITY, SLICES, MASKS, ROMBOUND, COVER, HEAD
from verify_keygen_acceptance import check_negative_diagnostic, check_sentinel

MUTATIONS=(
    ('input-f-shape-substituted-g',INPUT,'if is_f then keygen_f_pre_ntt_spec buf else keygen_g_pre_ntt_spec buf','if is_f then keygen_g_pre_ntt_spec buf else keygen_g_pre_ntt_spec buf'),
    ('input-head-rescaling-omitted',INPUT,'lift_int(3*acceptance_head_bit buf k)','lift_int(acceptance_head_bit buf k)'),
    ('input-fails-to-fix-head-remainder',INPUT,'forall i, 2<=i<192 => b.[i]=c.[i]','forall i, 96<=i<192 => b.[i]=c.[i]'),
    ('input-omits-negative-bits-context',INPUT,'forall i, 2<=i<192 => b.[i]=c.[i]','forall i, 2<=i<96 => b.[i]=c.[i]'),
    ('probability-bad-event-uses-witness',PROBABILITY,'(acceptance_input is_f buf)','(acceptance_input is_f witness)'),
    ('probability-f-bound-assumes-positive',PROBABILITY,'lemma fresh_f_accept_lower :','lemma fresh_f_accept_lower : 0%r<fresh_f_accept_mass =>'),
    ('probability-g-bound-assumes-positive',PROBABILITY,'lemma fresh_g_accept_lower :','lemma fresh_g_accept_lower : 0%r<fresh_g_accept_mass =>'),
    ('probability-f-rejection-cover-substituted',PROBABILITY,'!keygen_f_accept buf => indexed_event_union 384 (acceptance_bad true) buf','!keygen_g_accept buf => indexed_event_union 384 (acceptance_bad true) buf'),
    ('probability-g-root-signs-halved',PROBABILITY,'!keygen_g_accept buf => indexed_event_union 384 (acceptance_bad false) buf','!keygen_g_accept buf => indexed_event_union 192 (acceptance_bad false) buf'),
    ('probability-real-ROM-LL-injected',PROBABILITY,'require import AllCore','lemma unproved : islossless Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run. proof. auto. qed. require import AllCore'),
    ('slice-exception-omitted',SLICES,'[252;974;2483;3205]','[974;2483;3205]'),
    ('slice-exception-fifth-power-wrong',SLICES,'then 5 else 4','then 4 else 4'),
    ('slice-certificate-only-checks-half-assignments',SLICES,'iota_ 0 32','iota_ 0 16'),
    ('mask-even-odd-digit-aliased',MASKS,'if p=0 then m %% 32 else m %/ 32','if p=0 then m %% 32 else m %% 32'),
    ('mask-fifth-odd-bit-copies-even',MASKS,'slice_bit (acceptance_digit m 1) 4','slice_bit (acceptance_digit m 0) 4'),
    ('mask-touches-negative-bits',MASKS,'if 0<=i<2','if 0<=i<192'),
    ('mask-even-odd-position-aliased',MASKS,'2*nth 0 (slice_exponents rho) t+p','2*nth 0 (slice_exponents rho) t'),
    ('numerical-bound-hidden-positivity',ROMBOUND,'lemma certified_keygen_public_distance_256 &m a m0 (event:W8.t Array1152.t * W8.t Array2336.t -> bool) :','lemma certified_keygen_public_distance_256 &m a m0 (event:W8.t Array1152.t * W8.t Array2336.t -> bool) : 0%r<fresh_f_accept_mass =>'),
    ('empty-cache-premise-omitted',ROMBOUND,'ROE.m{m}=empty =>',''),
    ('empty-cache-reference-API-substitution',ROMBOUND,'lemma certified_keygen_empty_cache_distance &m (event:W8.t Array1152.t * W8.t Array2336.t -> bool) : ROE.m{m}=empty => `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run()','lemma certified_keygen_empty_cache_distance &m (event:W8.t Array1152.t * W8.t Array2336.t -> bool) : ROE.m{m}=empty => `|Pr[ReferenceKeygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run()'),
    ('numeric-late-return-omits-nonreturn',ROMBOUND,'!counted_within 256 256 res] + (1%r-Pr[CountedKeygen(UniformSeedRNG,ExpandROM).run(witness) @ &m : true])','!counted_within 256 256 res] + 0%r'),
    ('actual-failed-word-status-reversed',ALGEBRA,'lemma failed_block_determinant (a:W16.t Array768.t) k : in_qrange768 a => 0<=k<192 => poly_block_status a k=W64.of_int 1 =>','lemma failed_block_determinant (a:W16.t Array768.t) k : in_qrange768 a => 0<=k<192 => poly_block_status a k=W64.of_int 0 =>'),
    ('actual-Montgomery-decoding-omitted',ALGEBRA,'zeta_decode(poly_block_zeta k)=terminal_value k','coeff(poly_block_zeta k)=terminal_value k'),
    ('determinant-second-signed-factor-omitted',ALGEBRA,'lift_int(inverse_determinant a z)=block_norm a r*block_norm a (-r)','lift_int(inverse_determinant a z)=block_norm a r'),
    ('actual-rejected-f-polynomial-substituted',ALGEBRA,'!keygen_f_accept buf => exists j,0<=j<384 /\\ quadratic_divides(roots j)(input_poly(keygen_f_pre_ntt_spec buf))','!keygen_f_accept buf => exists j,0<=j<384 /\\ quadratic_divides(roots j)(input_poly(keygen_g_pre_ntt_spec buf))'),
    ('concrete-f-cover-assumes-nonsquare',COVER,'lemma keygen_f_rejected_quadratic (buf:W8.t Array192.t) :','lemma keygen_f_rejected_quadratic (buf:W8.t Array192.t) : field_nonsquare(lift_int(acceptance_root 0)) =>'),
    ('concrete-g-cover-skips-half-roots',COVER,'!keygen_g_accept buf => exists j,0<=j<384','!keygen_g_accept buf => exists j,0<=j<192'),
    ('head-remainder-loses-odd-coordinate',HEAD,'NTRUPoly.polyC(lift_int 3*acceptance_weight8 r buf 1)*NTRUPoly.X','NTRUPoly.polyC(lift_int 3*acceptance_weight8 r buf 0)*NTRUPoly.X'),
    ('head-selected-equality-forgets-context',HEAD,'lemma acceptance_head_divisors_equal is_f rho b c : acceptance_same_tail b c =>','lemma acceptance_head_divisors_equal is_f rho b c :'),
    ('head-selected-equality-only-even',HEAD,'forall p,0<=p<2 => acceptance_selected_weight rho b p=acceptance_selected_weight rho c p','forall p,0<=p<1 => acceptance_selected_weight rho b p=acceptance_selected_weight rho c p'),
    ('root-certificate-wrong-value',ROOTS,'1003; 2454;','1004; 2454;'),
    ('root-certificate-sign-lost',ROOTS,'1003; 2454;','1003; 1003;'),
    ('root-certificate-one-root-omitted',ROOTS,'1003; 2454;','1003;'),
    ('Euler-exponent-wrong',ROOTS,'acceptance_euler_mod x = x^1728 %%3457','acceptance_euler_mod x = x^864 %%3457'),
    ('Euler-square-used-as-nonsquare',ROOTS,'all (fun r=>acceptance_euler_mod r=3456)','all (fun r=>acceptance_euler_mod r=1)'),
    ('root-square-unrelated-to-actual-z',ROOTS,'(acceptance_root(2*k+b2i b)^2) %%3457=terminal_value k','(acceptance_root(2*k+b2i b)^2) %%3457=22'),
    ('root-square-forgets-sign-selector',ROOTS,'(acceptance_root(2*k+b2i b)^2) %%3457=terminal_value k','(acceptance_root(2*k)^2) %%3457=terminal_value k'),
    ('orbit-addition-instead-of-XOR',ORBIT,'buf.[i] +^ mask.[i]','buf.[i] + mask.[i]'),
    ('orbit-distribution-not-preserved',ORBIT,'dmap uniform192 (uniform192_xor mask)=uniform192','dmap uniform192 (uniform192_xor mask)=uniform96'),
    ('orbit-invariance-premise-lost',ORBIT,'(forall i, 0<=i<n => dmap uniform192 (transforms i)=uniform192) =>',''),
    ('orbit-disjointness-premise-lost',ORBIT,'bad(transforms i buf) => bad(transforms j buf) => i=j','bad(transforms i buf) => bad(transforms j buf) => true'),
    ('union-misses-half-the-roots',ORBIT,'(forall i, 0<=i<384 => mu uniform192 (bad i)<=1%r/1024%r)','(forall i, 0<=i<192 => mu uniform192 (bad i)<=1%r/1024%r)'),
    ('slice-bound-uses-five-bits-only',ORBIT,'(forall i, 0<=i<384 => mu uniform192 (bad i)<=1%r/1024%r)','(forall i, 0<=i<384 => mu uniform192 (bad i)<=1%r/32%r)'),
    ('rejection-cover-direction-reversed',ORBIT,'!accept buf => indexed_event_union 384 bad buf','indexed_event_union 384 bad buf => !accept buf'),
    ('acceptance-bound-weakened',ORBIT,'5%r/8%r<=mu uniform192 accept','0%r<mu uniform192 accept'),
    ('nonsquare-definition-vacuous',ALGEBRA,'forall (x:CycloFq.cyclocoeff), x*x<>r','forall (x:CycloFq.cyclocoeff), true'),
    ('quadratic-wrong-factor',ALGEBRA,'NTRUPoly.PolyComRing.exp NTRUPoly.X 2-NTRUPoly.polyC r','NTRUPoly.PolyComRing.exp NTRUPoly.X 4-NTRUPoly.polyC r'),
    ('norm-zero-nonsquare-premise-omitted',ALGEBRA,'field_nonsquare r => a*a-r*(b*b)=CycloFq.zero','a*a-r*(b*b)=CycloFq.zero'),
    ('budget-f-positivity-only',BUDGET,'5%r/8%r <= pf <= 1%r =>','0%r<pf =>'),
    ('budget-g-positivity-only',BUDGET,'5%r/8%r <= pg <= 1%r =>','0%r<pg =>'),
    ('budget-only-counts-f-attempts',BUDGET,'proposal_delta a 512 =','proposal_delta a 256 ='),
    ('budget-forgets-prior-cache',BUDGET,'(512%r*a%r+130816%r)','(130816%r)'),
    ('budget-resets-between-phases',BUDGET,'(512%r*a%r+130816%r)','(512%r*a%r+65280%r)'),
    ('budget-omits-retry-numerator',BUDGET,'(512%r*a%r+130818%r)','(512%r*a%r+130816%r)'),
    ('budget-empty-cache-exponent-drift',BUDGET,'130818%r/(2%r^256) < 1%r/(2%r^239)','130818%r/(2%r^256) < 1%r/(2%r^240)'),
    ('actual-f-rescaling-wrong',SHAPING,'3 * NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int buf k','NTRUPlus768PolyCBD1Algebra.poly_cbd1_coeff_int buf k'),
    ('actual-f-constant-omitted',SHAPING,'+ keygen_delta0 k','+ 0'),
    ('actual-g-rescaling-wrong',SHAPING,'W16.of_int (3 * coeff p.[k])','W16.of_int (coeff p.[k])'),
    ('actual-f-inverse-predicate-substituted',ACCEPT,'poly_blocks_succeed (keygen_f_ntt_spec buf) 192','true'),
    ('actual-g-inverse-blocks-halved',ACCEPT,'poly_blocks_succeed (keygen_g_ntt_spec buf) 192','poly_blocks_succeed (keygen_g_ntt_spec buf) 96'),
    ('imported-collision-cross-phase-term-lost',COLLISION,'(qb*(qb-1))%r','(qb*(qb-2))%r'),
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
        text=policy.compact((policy.ROOT/relative).read_text())
        old,new=policy.compact(old),policy.compact(new)
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
