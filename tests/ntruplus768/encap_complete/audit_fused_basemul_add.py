#!/usr/bin/env python3
"""Source-bound integer certificate for official fused basemul_add.

This is an executable arithmetic/source audit, not an EasyCrypt C-AST proof.
Signed narrowing and right shifts use the target's two's-complement semantics.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import runpy


PINS = {
    'ntt.c': 'ac85aea518d2b4251b08d68c372e3fda3d232917542677ae20353433d67f4911',
    'poly.c': '923990d51c526f2c46d1a40dc6fb6ef4e50ada35f74647ad73fd597a25fda592',
    'params.h': '420bef5432154798239e1f09b18f31947e3afff248ff98d4e83346b84d27ebb8',
}


def require(condition, detail):
    if not condition:
        raise ValueError(detail)


def normalized(text):
    return re.sub(r'\s+', '', re.sub(r'/\*.*?\*/|//[^\n]*', '', text, flags=re.S))


def body(source, name):
    match = re.search(r'\b' + re.escape(name) + r'\s*\([^;{}]*\)\s*\{', source)
    require(match is not None, 'missing function ' + name)
    start = end = match.end()
    depth = 1
    while depth:
        require(end < len(source), 'unterminated function ' + name)
        depth += (source[end] == '{') - (source[end] == '}')
        end += 1
    return normalized(source[start:end - 1])


def certify(root):
    ref = root / 'tests/ntruplus768/decap_guard/reference'
    pins = {}
    for name, expected in PINS.items():
        path = ref / name
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        require(digest == expected, 'official source pin changed: ' + name)
        pins[str(path.relative_to(root))] = digest
    ntt, poly = (ref / 'ntt.c').read_text(), (ref / 'poly.c').read_text()
    prefix = '''
      int16_t t0=montgomery_reduce(a[1]*b[3]+a[2]*b[2]+a[3]*b[1]);
      int16_t t1=montgomery_reduce(a[2]*b[3]+a[3]*b[2]);
      int16_t t2=montgomery_reduce(a[3]*b[3]);
      int16_t c0=montgomery_reduce(t0*zeta+a[0]*b[0]);
      int16_t c1=montgomery_reduce(t1*zeta+a[0]*b[1]+a[1]*b[0]);
      int16_t c2=montgomery_reduce(t2*zeta+a[0]*b[2]+a[1]*b[1]+a[2]*b[0]);
      int16_t c3=montgomery_reduce(a[0]*b[3]+a[1]*b[2]+a[2]*b[1]+a[3]*b[0]);
    '''
    ordinary = ''.join(f'r[{j}]=montgomery_reduce(c{j}*NTRUPLUS_RSQ);' for j in range(4))
    fused = ''.join(f'r[{j}]=montgomery_reduce(c[{j}]*NTRUPLUS_R+c{j}*NTRUPLUS_RSQ);' for j in range(4))
    require(body(ntt, 'basemul') == normalized(prefix + ordinary), 'ordinary formula changed')
    require(body(ntt, 'basemul_add') == normalized(prefix + fused), 'fused formula changed')
    require(body(ntt, 'montgomery_reduce') == normalized('''
      int16_t t; t=(int16_t)a*NTRUPLUS_QINV;
      t=(a-(int32_t)t*NTRUPLUS_Q)>>16; return t;
    '''), 'Montgomery reducer changed')
    for suffix in ('', '_add'):
        extra = ',c->coeffs+8*i' if suffix else ''
        extra4 = ',c->coeffs+8*i+4' if suffix else ''
        expected = ('for(int i=0;i<NTRUPLUS_N/8;++i){'
                    f'basemul{suffix}(r->coeffs+8*i,a->coeffs+8*i,b->coeffs+8*i{extra},zetas[96+i]);'
                    f'basemul{suffix}(r->coeffs+8*i+4,a->coeffs+8*i+4,b->coeffs+8*i+4{extra4},-zetas[96+i]);'
                    '}')
        require(body(poly, 'poly_basemul' + suffix) == normalized(expected), 'block schedule changed')
    require(body(poly, 'poly_tobytes') == normalized('''
      int16_t t[2]; for(size_t i=0;i<NTRUPLUS_N/2;i++) {
        t[0]=a->coeffs[2*i]; t[0]+=(t[0]>>15)&NTRUPLUS_Q;
        t[1]=a->coeffs[2*i+1]; t[1]+=(t[1]>>15)&NTRUPLUS_Q;
        r[3*i+0]=(t[0]>>0); r[3*i+1]=(t[0]>>8)|(t[1]<<4);
        r[3*i+2]=(t[1]>>4);
      }
    '''), 'canonical serializer changed')
    constants = {name: int(re.search(r'^#define\s+' + name + r'\s+(-?\d+)\b', ntt, re.M)[1])
                 for name in ('NTRUPLUS_R', 'NTRUPLUS_RSQ', 'NTRUPLUS_QINV')}
    require(constants == {'NTRUPLUS_R': -147, 'NTRUPLUS_RSQ': 867, 'NTRUPLUS_QINV': 12929},
            'Montgomery constants changed')
    q, radix, qinv, r, rsq = 3457, 65536, 12929, -147, 867
    rinv = pow(radix, -1, q)
    require((q*qinv) % radix == 1, 'invalid QINV')
    require((r-radix) % q == 0 and (rsq-radix*radix) % q == 0, 'invalid radix constants')
    require((r*rinv) % q == 1, 'addend does not survive fused Montgomery reduction')
    zetas = list(map(int, re.findall(r'-?\d+', re.search(r'zetas\[192\]\s*=\s*\{(.*?)\}', ntt, re.S)[1])))
    require(len(zetas) == 192, 'wrong twiddle count')
    jasmin_poly = root / 'ntruplus/jasmin/768/ref/poly_basemul.jazz'
    table = re.search(r'NTRUPLUS_ZETAS96\s*=\s*\{(.*?)\}', jasmin_poly.read_text(), re.S)
    require(table is not None, 'missing Jasmin twiddles')
    jasmin_zetas = list(map(int, re.findall(r'-?\d+', table[1])))
    require(jasmin_zetas == [x % radix for x in zetas[96:]], 'Jasmin twiddle mismatch')
    # Reuse the existing bounded symbolic substitution audit for the legacy
    # arithmetic source against which the extracted basemul proof was built.
    compatibility = root / 'tests/ntruplus768/decap_candidate/audit_compatibility.py'
    helpers = runpy.run_path(str(compatibility))
    old_ntt = root / 'NTRU+/NTRU+768/ntt.c'
    require(helpers['substituted_outputs'](helpers['function_body'](old_ntt, 'basemul')) ==
            helpers['substituted_outputs'](helpers['function_body'](ref / 'ntt.c', 'basemul')),
            'legacy basemul arithmetic mismatch')
    for path in (jasmin_poly, root / 'ntruplus/jasmin/768/ref/basemul.jazz', old_ntt, compatibility):
        pins[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
    schedule = [z for x in zetas[96:] for z in (x, -x)]
    require(all(-1728 <= z <= 1728 for z in schedule), 'twiddle outside centered range')

    checks = {'int16': 0, 'int32': 0, 'montgomery_calls': 0}
    maximum = {'int16': 0, 'int32': 0, 'montgomery_input': 0}
    def checked(a, bits):
        lo, hi = a
        require(-(1 << (bits-1)) <= lo <= hi < (1 << (bits-1)), f'int{bits} overflow: {a}')
        checks['int'+str(bits)] += 1
        maximum['int'+str(bits)] = max(maximum['int'+str(bits)], abs(lo), abs(hi))
        return a
    def add(a, b):
        return checked((a[0]+b[0], a[1]+b[1]), 32)
    def mul(a, b):
        endpoints = [x*y for x in a for y in b]
        return checked((min(endpoints), max(endpoints)), 32)
    def total(values):
        result = (0, 0)
        for value in values:
            result = add(result, value)
        return result
    def mont(a):
        checked(a, 32)
        require(-q*32768 <= a[0] <= a[1] < q*32768, 'Montgomery input precondition')
        maximum['montgomery_input'] = max(maximum['montgomery_input'], abs(a[0]), abs(a[1]))
        # The cast to int16 and low-word product truncation are intentional.
        # Their signed representative t lies in [-32768,32767]. Divisibility
        # of a-q*t follows from q*QINV == 1 (mod 2^16), so exact division uses
        # ceil at the lower bound and floor at the upper bound.
        checked((-32768*qinv, 32767*qinv), 32)
        correction = checked((-32768*q, 32767*q), 32)
        numerator = checked((a[0]-correction[1], a[1]-correction[0]), 32)
        output = checked((-((-numerator[0])//radix), numerator[1]//radix), 16)
        require(-q <= output[0] <= output[1] < q, 'Montgomery result outside qrange')
        checks['montgomery_calls'] += 1
        return output

    # Stronger than the Encaps entry domain: both factors may contain every
    # signed qrange coefficient. This includes canonical h and centered NTT(r).
    factor = (-q, q-1)
    summand = (-1728, 1728)
    product = mul(factor, factor)
    per_block = []
    for k, z in enumerate(schedule):
        t = [mont(total([product]*count)) for count in (3, 2, 1)]
        intermediate = [mont(total([mul(t[j], (z,z))]+[product]*(j+1))) for j in range(3)]
        intermediate.append(mont(total([product]*4)))
        ordinary_bounds = [mont(mul(x, (rsq,rsq))) for x in intermediate]
        fused_bounds = [mont(add(mul(summand, (r,r)), mul(x, (rsq,rsq)))) for x in intermediate]
        per_block.append({'block': k, 'zeta_word_signed': z,
                          'shared_intermediate': intermediate,
                          'ordinary_output': ordinary_bounds, 'fused_output': fused_bounds})
    # Exhaust the scalar normalization domain, not the full polynomial space.
    for x in range(-q, q):
        canonical = x + ((x >> 15) & q)
        require(canonical == x % q and 0 <= canonical < 4096, 'canonicalization mismatch')
    require(((q-1) << 4) < 2**31, 'serializer left shift overflow')
    # A symbolic coefficient check: for every shared intermediate x and
    # addend m, fused output is (x*RSQ + m*R)*R^-1, hence ordinary+m modq.
    ordinary_coeff = (rsq*rinv) % q
    fused_coefficients = {'shared_intermediate': (rsq*rinv) % q, 'addend': (r*rinv) % q}
    require(fused_coefficients == {'shared_intermediate': ordinary_coeff, 'addend': 1},
            'symbolic tail congruence failed')
    source = root / 'ntruplus/jasmin/768/ref/poly_centered_add.jazz'
    pins[str(source.relative_to(root))] = hashlib.sha256(source.read_bytes()).hexdigest()
    return {
        'status': 'PASS', 'official_commit': '3991b2ae08d6f0008d37e41b8aceaaab27b4ec89',
        'source_pins': pins,
        'source_checks': {'shared_basemul_prefix': True, 'exact_fused_tail': True,
                          'exact_montgomery_reducer': True, 'same_192_block_schedule': True,
                          'exact_canonical_serializer': True, 'jasmin_twiddles_match': True,
                          'legacy_basemul_same_substituted_outputs': True},
        'arithmetic_certificate': {
            'domain': {'factor_a': list(factor), 'factor_b': list(factor), 'add': list(summand)},
            'quantification': 'All arrays in the domain; sound interval overapproximation, no input sampling.',
            'checks': checks, 'maximum_absolute_bounds': maximum, 'blocks': per_block,
            'fused_output_range': [-q, q-1],
            'ordinary_output_range': [-q, q-1],
            'fused_tail_residue_coefficients': fused_coefficients,
            'ordinary_tail_residue_coefficient': ordinary_coeff,
            'montgomery_relation': 'R*out == input (mod q); low-word t forces exact division by 2^16.',
            'serialization': 'Every coefficient in [-q,q) canonicalizes to x modq; equal residues produce identical 12-bit packed bytes.',
            'scalar_canonicalization_cases': 2*q,
            'intentional_narrowings': 'Montgomery low-word casts/truncations use signed two-complement modulo 2^16; all other narrowing stores fit int16.',
        },
        'claim_boundary': 'Source-bound arithmetic certificate, not a C-AST or binary equivalence theorem. The new Jasmin centered-add and existing basemul have separate extracted EasyCrypt proofs. Fused and separate raw words need not match; canonical ciphertext bytes match under the stated domains.',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', '--root', dest='repo', type=Path,
                        default=Path(__file__).resolve().parents[3])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = certify(args.repo.resolve())
    rendered = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end='')
