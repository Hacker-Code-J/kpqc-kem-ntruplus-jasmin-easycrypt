"""Check the intended event, matrix orientation, premises and final contracts.

These textual regression checks supplement proof replay; they do not establish
any mathematical statement by themselves.
"""
import re
import policy

SOURCES = {name: policy.PROOF / ('NTRUPlus768' + name + '.ec') for name in (
    'SRMultiplication', 'SRMultiplicationProof', 'SRMultiplicationField',
    'SRProbability', 'SRUnionModel', 'SRUnion', 'SRNumerical',
    'SRMatrixCounting', 'SRMultiplicationKernel', 'SRBound', 'SRFinal')}
CONTRACTS = {
    'SRMultiplication': [
        'type sr_matrix = int -> int -> int.',
        'lemma sr_mul_matrix_product a v : sr_matvec(sr_mul_matrix v)a=integer_product a v.',
        'lemma sr_mul_matrix_row_bound v k : inj_short v=>sr_row_sqnorm(sr_mul_matrix v)k<=12288.'],
    'SRMultiplicationProof': [
        'lemma sr_relation_zero_left h w : inj_short w=>inj_relation h inj_zero w=>w=inj_zero.',
        'lemma sr_success_nonzero_left h v w : inj_short_win h(v,w)=>v<>inj_zero.'],
    'SRMultiplicationField': [
        'lemma sr_field_vector_poly h : ow_rq_domain h=>int_poly(sr_field_vector h)=h.',
        'lemma sr_field_relation_matrix_iff h v w : ow_rq_domain h=>',
        '(inj_relation h v w <=> (forall k,0<=k<768=>((sr_matvec(sr_mul_matrix v)(sr_field_vector h)).[k]+w.[k])%%q=0)).'],
    'SRProbability': [
        'op sr_residue_lists : int list list = alltuples 768 (range 0 3457).',
        '(Bigint.BIA.bigi predT(fun j=>m k j*nth 0 xs j)0 768+w.[k])%%3457=0.',
        'lemma sr_uniform_fixed_pair_count v w : mu ow_uniform_rq (fun h=>inj_relation h v w)<=',
        '(size(sr_equation_lists(sr_mul_matrix v)w))%r*(1%r/3457%r)^768.'],
    'SRUnionModel': [
        'op [opaque] sr_alphabet:int list = range (-2) 3.',
        'lemma sr_short_pairs_mem z : z \\in sr_short_pairs <=> inj_short z.`1 /\\ inj_short z.`2.',
        'lemma sr_short_pairs_size : size sr_short_pairs=25^768.'],
    'SRUnion': [
        'lemma sr_uniform_from_nonzero_bound epsilon : 0%r<=epsilon=>',
        '(forall v w,inj_short v=>inj_short w=>v<>inj_zero=>',
        'mu ow_uniform_rq(fun a=>inj_relation a v w)<=epsilon)=>',
        'inj_uniform_bad_mass<=25%r^768*epsilon.'],
    'SRNumerical': [
        'lemma sr_union_numeric_integer_bound :',
        '25%r^768*((12288^384)%r/(3457^768)%r)<1%r/(2%r^244).'],
    'SRMatrixCounting': [
        'op sr_integer_kernel_trivial (m:int->int->int) =',
        'lemma sr_matrix_fiber_bound (m:int->int->int) (b:int->int) (xss:int list list) :',
        'sr_integer_kernel_trivial m=>sr_matrix_rows_bounded m=>',
        'uniq xss=>',
        'size(filter(sr_matrix_list_equation m b)xss)<=12288^384.'],
    'SRMultiplicationKernel': [
        'lemma sr_mul_kernel_trivial v : v<>inj_zero=>sr_integer_kernel_trivial(sr_mul_matrix v).'],
    'SRBound': [
        'lemma sr_fixed_pair_bound v w : inj_short v=>v<>inj_zero=>',
        'mu ow_uniform_rq(fun h=>inj_relation h v w)<=(12288^384)%r/(3457^768)%r.',
        'lemma sr_uniform_bad_mass_244 : inj_uniform_bad_mass<1%r/(2%r^244).',
        'sr_uniform_from_nonzero_bound', 'sr_fixed_pair_bound', 'sr_union_numeric_integer_bound'],
    'SRFinal': ['lemma sr_original_numerical', 'inj_original_statistical A &m',
                'have bound:inj_uniform_bad_mass<=1%r/(2%r^244).', 'sr_uniform_bad_mass_244'],
}
MUTATIONS = [
    ('SRMultiplication', 'wrong-row-height', '<=12288.', '<=12289.'),
    ('SRProbability', 'unit-only-enumeration', 'range 0 3457', 'range 1 3457'),
    ('SRProbability', 'wrong-linear-sign', '+w.[k])%%3457', '-w.[k])%%3457'),
    ('SRProbability', 'wrong-modulus', ')%%3457=0.', ')%%3458=0.'),
    ('SRUnionModel', 'lost-short-coefficients', 'range (-2) 3', 'range (-1) 2'),
    ('SRUnionModel', 'wrong-union-count', '25^768.', '5^768.'),
    ('SRUnion', 'lost-nonzero-premise', 'v<>inj_zero=>', 'true=>'),
    ('SRNumerical', 'unsupported-bit-bound',
     '25%r^768*((12288^384)%r/(3457^768)%r)<1%r/(2%r^244).',
     '25%r^768*((12288^384)%r/(3457^768)%r)<1%r/(2%r^245).'),
    ('SRBound', 'conditional-final-mass', 'lemma sr_uniform_bad_mass_244 :',
     'lemma sr_uniform_bad_mass_244 : false=>'),
]


def declaration(text, name):
    match = re.search(r'\blemma\s+' + re.escape(name) + r'\b(.*?)\bproof\.',
                      policy.without_comments(text), re.S)
    policy.require(match is not None, 'missing theorem ' + name)
    return policy.compact(match.group(1))


def check(sources=None):
    sources = sources or {name: path.read_text() for name, path in SOURCES.items()}
    policy.require(set(sources) == set(SOURCES), 'unexpected semantic source inventory')
    for name, fragments in CONTRACTS.items():
        policy.check_proof_text(sources[name])
        code = policy.compact(sources[name])
        policy.shared.ordered(code, [policy.compact(x) for x in fragments])
    previous = (policy.BASE / 'kem_inj_hardness/NTRUPlus768INJFinal.ec').read_text()
    expected = declaration(previous, 'inj_original_statistical').replace(
        'inj_uniform_bad_mass)/ow_alpha_g', '(1%r/(2%r^244)))/ow_alpha_g')
    policy.require(declaration(sources['SRFinal'], 'sr_original_numerical') == expected,
                   'original game, advantage or adversary/query/termination contract changed')
    policy.require('coq check' in sources['SRMatrixCounting'], 'missing native goal replay')
    policy.require('coq check' in sources['SRMultiplicationKernel'], 'missing actual multiplication goal replay')
    return True
