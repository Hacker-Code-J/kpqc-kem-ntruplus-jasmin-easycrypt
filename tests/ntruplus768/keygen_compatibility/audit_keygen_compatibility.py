#!/usr/bin/env python3
"""Source-bound integer certificates for the official KeyGen arithmetic seam.

This is not a C-AST or binary equivalence theorem.  Existing extracted-Jasmin
proofs are separate evidence.  Signed casts and shifts use target x86-64
two's-complement semantics; intentional Montgomery low-word casts are explicit.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
Q, N, RADIX, QINV, HALF = 3457, 768, 65536, 12929, 1728


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Bounds:
    """Outward integer intervals; dependencies deliberately overapproximated."""
    def __init__(self):
        self.stats = {'int16_checks': 0, 'int32_checks': 0,
                      'max_abs_int16': 0, 'max_abs_int32': 0,
                      'montgomery_calls': 0, 'max_abs_montgomery_input': 0}

    def check(self, a, bits):
        lo, hi = a
        assert lo <= hi and -(1 << (bits-1)) <= lo <= hi < 1 << (bits-1), (bits, a)
        self.stats[f'int{bits}_checks'] += 1
        key = f'max_abs_int{bits}'
        self.stats[key] = max(self.stats[key], abs(lo), abs(hi))
        return a

    def add(self, a, b):
        return self.check((a[0]+b[0], a[1]+b[1]), 32)

    def sub(self, a, b):
        return self.check((a[0]-b[1], a[1]-b[0]), 32)

    def mul(self, a, b):
        values = [x*y for x in a for y in b]
        return self.check((min(values), max(values)), 32)

    def square(self, a):
        lo, hi = a
        return self.check((0 if lo <= 0 <= hi else min(lo*lo, hi*hi),
                           max(lo*lo, hi*hi)), 32)

    def montgomery(self, a):
        self.check(a, 32)
        assert -Q*32768 <= a[0] <= a[1] < Q*32768, a
        # First int16 cast and assignment intentionally retain low words.
        self.check((-32768*QINV, 32767*QINV), 32)
        correction = self.check((-32768*Q, 32767*Q), 32)
        numerator = self.sub(a, correction)
        # Exact numerator is divisible by RADIX: Q*QINV == 1 mod RADIX.
        assert Q*QINV % RADIX == 1
        out = self.check((-((-numerator[0])//RADIX), numerator[1]//RADIX), 16)
        self.stats['montgomery_calls'] += 1
        self.stats['max_abs_montgomery_input'] = max(
            self.stats['max_abs_montgomery_input'], abs(a[0]), abs(a[1]))
        return out

    def fqmul(self, z, a):
        self.check(a, 16)
        self.check((z, z), 16)
        return self.montgomery(self.mul((z, z), a))


def barrett_certificate():
    v = ((1 << 26) + Q//2)//Q
    bad = []
    b = Bounds()
    for x in range(-32768, 32768):
        num = v*x + (1 << 25)
        b.check((num, num), 32)
        quotient = num//(1 << 26)
        b.check((quotient, quotient), 16)
        correction = quotient*Q
        b.check((correction, correction), 16)
        result = x-correction
        b.check((result, result), 16)
        assert (result-x) % Q == 0
        if not -HALF <= result <= HALF:
            bad.append(x)
    limit = min(abs(x) for x in bad)-1
    return {'checked_int16_inputs': 65536, 'v': v,
            'noncanonical_inputs': bad, 'centred_interval': [-limit, limit]}


def ntt_certificate(zetas, kind, centre_limit):
    assert kind in ('f', 'g')
    certificates = {}
    for schedule in ('per_layer', 'final_sweep'):
        b = Bounds()
        r = [(-3, 3)]*N
        if kind == 'f':
            r[0] = (-2, 4)
        layers = []

        def record(label):
            layers.append({'stage': label, 'lower': min(a[0] for a in r),
                           'upper': max(a[1] for a in r)})

        def barrett(a):
            b.check(a, 16)
            assert -centre_limit <= a[0] <= a[1] <= centre_limit
            return (-HALF, HALF)

        record('3CBD_plus_one' if kind == 'f' else '3CBD')
        k = 1
        z = zetas[k]
        k += 1
        for i in range(N//2):
            a, c = r[i], r[i+N//2]
            t = b.fqmul(z, c)
            r[i+N//2] = b.check(b.sub(b.add(a, c), t), 16)
            r[i] = b.check(b.add(a, t), 16)
        record('radix2_initial')
        for start in range(0, N, 384):
            z1, z2 = zetas[k], zetas[k+1]
            k += 2
            for i in range(start, start+128):
                a, c, d = r[i], r[i+128], r[i+256]
                t1, t2 = b.fqmul(z1, c), b.fqmul(z2, d)
                t3 = b.fqmul(-886, b.check(b.sub(t1, t2), 16))
                r[i+256] = b.check(b.sub(b.sub(a, t1), t3), 16)
                r[i+128] = b.check(b.add(b.sub(a, t2), t3), 16)
                r[i] = b.check(b.add(b.add(a, t1), t2), 16)
        record('radix3')
        for step in (64, 32, 16, 8, 4):
            for start in range(0, N, 2*step):
                z = zetas[k]
                k += 1
                for i in range(start, start+step):
                    a, c = r[i], r[i+step]
                    t = b.fqmul(z, c)
                    left = b.check(b.add(a, t), 16)
                    right = b.check(b.sub(a, t), 16)
                    if schedule == 'per_layer':
                        left, right = barrett(left), barrett(right)
                    r[i], r[i+step] = left, right
            record(f'radix2_{step}')
        assert k == 192
        raw = [min(a[0] for a in r), max(a[1] for a in r)]
        if schedule == 'final_sweep':
            r = [barrett(a) for a in r]
            record('final_barrett')
        assert all(-HALF <= a[0] <= a[1] <= HALF for a in r)
        certificates[schedule] = {
            'layers': layers, 'before_final_sweep': raw, 'statistics': b.stats,
            'twiddles_consumed': k-1, 'final_range': [-HALF, HALF],
            'all_nonintentional_narrowings_fit': True,
            'intentional_truncation': 'Montgomery low-word casts modulo 2^16 only'}
    return {'input_domain': {'coefficient_0': [-2, 4] if kind == 'f' else [-3, 3],
                             'coefficients_1_through_767': [-3, 3],
                             'coverage': 'Every integer vector in these intervals; not sampling.'},
            'schedules': certificates,
            'conclusion': 'Identical butterflies/twiddles modulo q, no unintended narrowing, '
                          'and unique final representatives imply identical signed output words.'}


def concrete_montgomery(x, stats):
    assert -Q*32768 <= x < Q*32768 and -(1 << 31) <= x < 1 << 31
    low = ((x+32768) % RADIX)-32768
    product = low*QINV
    assert -(1 << 31) <= product < 1 << 31
    t = ((product+32768) % RADIX)-32768
    num = x-t*Q
    assert -(1 << 31) <= num < 1 << 31 and num % RADIX == 0
    out = num//RADIX
    assert -32768 <= out <= 32767 and (RADIX*out-x) % Q == 0
    stats['montgomery_calls'] += 1
    stats['max_abs_montgomery_input'] = max(stats['max_abs_montgomery_input'], abs(x))
    return out


def parse_chain(body):
    """Accept only declarations, fqmul assignments and a final return."""
    assignments = []
    rest = re.sub(r'int16_t\s+(?:t\d\s*,\s*)*t\d\s*;', '', body).strip()
    while True:
        match = re.match(r'(t\d)\s*=\s*fqmul\(\s*(\w+)\s*,\s*(\w+)\s*\)\s*;', rest)
        if not match:
            break
        assignments.append(match.groups())
        rest = rest[match.end():].strip()
    tail = re.fullmatch(r'return\s+(?:(t\d)|fqmul\(\s*(\w+)\s*,\s*(\w+)\s*\))\s*;', rest)
    assert tail and assignments, rest
    return assignments, tail.groups()


def run_chain(chain, a, stats):
    env = {'a': a, 'NTRUPLUS_RINV': -682}
    assignments, (result, left, right) = chain
    for dest, x, y in assignments:
        env[dest] = concrete_montgomery(env[x]*env[y], stats)
    return env[result] if result else concrete_montgomery(env[left]*env[right], stats)


def inverse_certificate(old_body, official_body, zetas):
    old_chain, official_chain = parse_chain(old_body), parse_chain(official_body)
    exhaustive = {'montgomery_calls': 0, 'max_abs_montgomery_input': 0}
    values = []
    for a in range(-Q+1, Q):
        x, y = run_chain(old_chain, a, exhaustive), run_chain(official_chain, a, exhaustive)
        assert x == y, (a, x, y)
        values.append(x)
    inverse_range = (min(values), max(values))
    b = Bounds()
    blocks = []
    a = (-HALF, HALF)
    for zeta in [s*z for z in zetas[96:] for s in (1, -1)]:
        z = (zeta, zeta)
        twice = lambda x: b.mul((2, 2), x)
        t0 = b.montgomery(b.sub(b.square(a), twice(b.mul(a, a))))
        t1 = b.montgomery(b.square(a))
        t0 = b.montgomery(b.add(b.square(a), b.mul(t0, z)))
        t1 = b.montgomery(b.sub(b.add(b.square(a), b.mul(t1, z)), twice(b.mul(a, a))))
        t2 = b.montgomery(b.mul(t1, z))
        t3 = b.montgomery(b.sub(b.square(t0), b.mul(t1, t2)))
        assert -Q < t3[0] <= t3[1] < Q
        # Zero is the unique representative of residue zero in this range.
        assert all((x % Q == 0) == (x == 0) for x in range(t3[0], t3[1]+1))
        numerators = [
            b.montgomery(b.add(b.mul(a, t0), b.mul(a, t2))),
            b.montgomery(b.add(b.mul(a, t2), b.mul(a, t0))),
            b.montgomery(b.add(b.mul(a, t0), b.mul(a, t1))),
            b.montgomery(b.add(b.mul(a, t1), b.mul(a, t0))) ]
        outputs = [b.montgomery(b.mul(x, inverse_range)) for x in numerators]
        for i in (1, 3):
            outputs[i] = b.check((-outputs[i][1], -outputs[i][0]), 16)
        assert all(-Q < lo <= hi < Q for lo, hi in outputs)
        blocks.append({'zeta': zeta, 'determinant': t3, 'output': outputs})
    return {'input_domain': 'Every 4-coefficient vector over [-1728,1728], all 192 scheduled signed twiddles.',
            'fqinv_exhaustive_inputs': 2*Q-1, 'fqinv_input_interval': [-Q+1, Q-1],
            'fqinv_raw_outputs_identical': True, 'fqinv_output_interval': inverse_range,
            'fqinv_statistics': exhaustive, 'baseinv_statistics': b.stats,
            'determinant_interval': [min(x['determinant'][0] for x in blocks),
                                     max(x['determinant'][1] for x in blocks)],
            'successful_output_interval': [min(a[0] for x in blocks for a in x['output']),
                                           max(a[1] for x in blocks for a in x['output'])],
            'all_192_block_bounds': blocks,
            'conclusion': 'Same exact NTT input words and determinant body give the same zero test. '
                          'The changed fqinv chains have equal words on every reachable determinant. '
                          'The identical success body therefore gives identical inverse words; '
                          'the identical poly wrapper returns status 1 and zeros every coefficient on failure.'}


def audit(root):
    pinned = json.loads((HERE/'pinned_sources.json').read_text())
    actual = {name: sha(root/name) for name in pinned}
    assert actual == pinned, [name for name in pinned if actual[name] != pinned[name]]
    test = root/'tests/ntruplus768'
    candidate = load(test/'decap_candidate/audit_compatibility.py', 'keygen_candidate_audit')
    r2 = load(test/'decap_r2_comp/audit_compatibility.py', 'keygen_r2_audit')
    r2_report = r2.audit(root)
    candidate_report = candidate.audit(root)
    body, norm = candidate.function_body, candidate.normalized
    old, official = root/'NTRU+/NTRU+768', test/'decap_guard/reference'
    jasmin = root/'ntruplus/jasmin/768/ref'
    check_baseinv = load(test/'baseinv/check_baseinv.py', 'keygen_baseinv_source')
    check_baseinv.verify_ntt_source_text((old/'ntt.c').read_text())
    check_baseinv.verify_poly_source_text((old/'poly.c').read_text())
    check_baseinv_j = load(test/'baseinv_jasmin/check_baseinv_jasmin.py', 'keygen_baseinv_jasmin')
    check_baseinv_j.verify_all((old/'params.h').read_text(), (old/'ntt.c').read_text(),
                             (jasmin/'baseinv.jazz').read_text())
    check_poly = load(test/'poly_baseinv_jasmin/check_poly_baseinv_jasmin.py', 'keygen_poly_baseinv')
    check_poly.verify_jasmin_source((jasmin/'poly_baseinv.jazz').read_text())
    for name in ('ntt', 'ntt_stage1', 'ntt_radix3', 'ntt_radix2_64',
                 'ntt_radix2_32', 'ntt_radix2_16', 'ntt_radix2_8', 'ntt_radix2_4'):
        checker = load(test/name/f'check_{name}.py', 'keygen_'+name)
        checker.verify_c_text((old/'ntt.c').read_text())
        checker.verify_jasmin_text((jasmin/f'{name}.jazz').read_text())
    checks = {
        'baseinv_body_identical': norm(body(old/'ntt.c', 'baseinv')) == norm(body(official/'ntt.c', 'baseinv')),
        'poly_baseinv_body_identical': norm(body(old/'poly.c', 'poly_baseinv')) == norm(body(official/'poly.c', 'poly_baseinv')),
        'poly_basemul_schedule_identical': norm(body(old/'poly.c', 'poly_basemul')) == norm(body(official/'poly.c', 'poly_basemul')),
        'cbd_body_identical': norm(body(old/'poly.c', 'poly_cbd1')) == norm(body(official/'poly.c', 'poly_cbd1')),
        'serializer_identical_except_unroll_pragma': norm(re.sub(r'#pragma GCC unroll 2', '', body(old/'poly.c', 'poly_tobytes'))) == norm(body(official/'poly.c', 'poly_tobytes')),
        'triple_same_on_inplace_input': norm(body(old/'poly.c', 'poly_triple')).replace('r->coeffs[i]=3*a->coeffs[i];', 'r->coeffs[i]*=3;') == norm(body(official/'poly.c', 'poly_triple')),
    }
    for macro, expected in [('NTRUPLUS_R', -147), ('NTRUPLUS_RINV', -682),
                            ('NTRUPLUS_RSQ', 867), ('NTRUPLUS_QINV', QINV)]:
        checks[macro] = int(re.search(r'^#define\s+'+macro+r'\s+(-?\d+)\b', (official/'ntt.c').read_text(), re.M)[1]) == expected
    assert all(checks.values()), checks
    zetas = list(map(int, re.findall(r'-?\d+', re.search(r'zetas\[192\]\s*=\s*\{(.*?)\}', (official/'ntt.c').read_text(), re.S)[1])))
    assert len(zetas) == 192
    barrett = barrett_certificate()
    inv = inverse_certificate(body(old/'ntt.c', 'fqinv'), body(official/'ntt.c', 'fqinv'), zetas)
    canonical = []
    for x in range(-Q+1, Q):
        y = x + ((x >> 15) & Q)
        assert y == x % Q and 0 <= y < Q
        canonical.append(y)
    return {'status': 'PASS', 'official_commit': '3991b2ae08d6f0008d37e41b8aceaaab27b4ec89',
            'source_sha256': actual, 'source_checks': checks,
            'reused_ntt_source_checks': r2_report['checks'],
            'reused_basemul_source_checks': candidate_report['checks'],
            'barrett': barrett,
            'ntt': {kind: ntt_certificate(zetas, kind, barrett['centred_interval'][1]) for kind in ('f', 'g')},
            'inverse': inv, 'serializer_scalar_inputs_checked': len(canonical),
            'conclusion': 'All allowed KeyGen f/g preimages have identical official/frozen NTT output words. '
                          'The inverse status, successful inverse words, and full zero output on failure coincide. '
                          'Unchanged basemul value expressions and canonical serializer then preserve accepted key bytes.',
            'scope': __doc__.strip()}


def self_test(root):
    """Changing any pinned dependency must reject the arithmetic certificate."""
    pinned = json.loads((HERE/'pinned_sources.json').read_text())
    rejected = []
    with tempfile.TemporaryDirectory(prefix='keygen-compatibility-negative-') as name:
        trial = Path(name)
        for rel in pinned:
            dest = trial/rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(root/rel, dest)
        for rel in pinned:
            path = trial/rel
            before = path.read_bytes()
            path.write_bytes(before+b'\n/* deliberately changed pinned source */\n')
            try:
                audit(trial)
            except AssertionError as error:
                assert error.args == ([rel],), (rel, error.args)
                rejected.append(rel)
            else:
                raise AssertionError('accepted changed source: '+rel)
            finally:
                path.write_bytes(before)
    return {'status': 'PASS', 'changed_dependencies_rejected': len(rejected),
            'dependencies': rejected,
            'scope': 'Exact-source identity gates; these are not semantic mutation proofs.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    report = audit(args.root.resolve())
    if args.self_test:
        report['source_identity_negative_controls'] = self_test(args.root.resolve())
    rendered = json.dumps(report, indent=2)+'\n'
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end='')
