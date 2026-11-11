#!/usr/bin/env python3
"""Integer interval certificate for the two pinned NTT reduction schedules.

This certifies a source-audited arithmetic model, not a parsed C-AST theorem.
Target signed narrowing/right shifts are two's-complement x86-64 semantics.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


def certify(root):
    official = root / 'tests/ntruplus768/decap_guard/reference/ntt.c'
    params = official.with_name('params.h')
    text = official.read_text()
    def constant(name, source):
        match = re.search(r'^#define\s+' + name + r'\s+(-?\d+)\b', source, re.M)
        assert match, name
        return int(match.group(1))
    q = constant('NTRUPLUS_Q', params.read_text())
    n = constant('NTRUPLUS_N', params.read_text())
    omega = constant('NTRUPLUS_OMEGA', text)
    qinv = constant('NTRUPLUS_QINV', text)
    match = re.search(r'const int16_t zetas\[192\]\s*=\s*\{(.*?)\};', text, re.S)
    assert match
    zetas = [int(x) for x in re.findall(r'-?\d+', match.group(1))]
    assert (n, q, qinv, omega) == (768, 3457, 12929, -886)
    assert len(zetas) == 192 and all(-32768 <= z <= 32767 for z in zetas)
    radix = 65536
    assert (q * qinv) % radix == 1
    assert -2**31 <= -32768*qinv <= 32767*qinv < 2**31
    v = ((1 << 26) + q // 2) // q
    half = q // 2
    violations = []
    for x in range(-32768, 32768):
        numerator = v*x + (1 << 25)
        assert -2**31 <= numerator < 2**31
        quotient = numerator // (1 << 26)
        assert -32768 <= quotient <= 32767
        correction = quotient*q
        assert -32768 <= correction <= 32767
        y = x-correction
        assert -32768 <= y <= 32767 and (y-x) % q == 0
        if not -half <= y <= half:
            violations.append(x)
    centre_limit = min(abs(x) for x in violations)-1 if violations else 32767
    certificate = {}
    for schedule in ('per_layer', 'final_sweep'):
        statistics = {'fqmul_calls':0, 'int16_checks':0, 'int32_checks':0,
                      'max_abs_int16':0, 'max_abs_int32':0, 'max_abs_montgomery_input':0}
        def check(a, bits):
            lo,hi = a
            assert lo <= hi and -(1 << (bits-1)) <= lo <= hi < (1 << (bits-1)), (schedule,bits,a)
            statistics['int'+str(bits)+'_checks'] += 1
            key = 'max_abs_int'+str(bits)
            statistics[key] = max(statistics[key], abs(lo), abs(hi))
            return a
        def add(a,b):
            return check((a[0]+b[0],a[1]+b[1]),32)
        def sub(a,b):
            return check((a[0]-b[1],a[1]-b[0]),32)
        def fqmul(z,a):
            check(a,16)
            product = check((min(z*a[0],z*a[1]),max(z*a[0],z*a[1])),32)
            assert -q*32768 <= product[0] <= product[1] < q*32768
            check((-32768*qinv,32767*qinv),32)
            statistics['max_abs_montgomery_input'] = max(statistics['max_abs_montgomery_input'],abs(product[0]),abs(product[1]))
            # Low-word multiplication is reduced to a signed16 value t.
            # q*QINV ==1 mod2^16 makes product-q*t divisible by2^16.
            correction = check((-32768*q,32767*q),32)
            numerator = check((product[0]-correction[1],product[1]-correction[0]),32)
            result = (-((-numerator[0])//radix),numerator[1]//radix)
            statistics['fqmul_calls'] += 1
            return check(result,16)
        def barrett(a):
            check(a,16)
            assert -centre_limit <= a[0] <= a[1] <= centre_limit, (schedule,a,centre_limit)
            # Exhaustive integer check above covers every point in this interval.
            return (-half,half)
        r = [(-1,1)]*n
        layers = []
        def record(label):
            layers.append({'stage':label,'lower':min(a[0] for a in r),'upper':max(a[1] for a in r)})
        record('trit_input')
        k=1;z=zetas[k];k+=1
        for i in range(n//2):
            a,b = r[i],r[i+n//2]
            t=fqmul(z,b)
            r[i+n//2]=check(sub(add(a,b),t),16)
            r[i]=check(add(a,t),16)
        record('radix2_initial')
        for start in range(0,n,384):
            z1,z2=zetas[k],zetas[k+1];k+=2
            for i in range(start,start+128):
                a,b,c=r[i],r[i+128],r[i+256]
                t1,t2=fqmul(z1,b),fqmul(z2,c)
                t3=fqmul(omega,check(sub(t1,t2),16))
                r[i+256]=check(sub(sub(a,t1),t3),16)
                r[i+128]=check(add(sub(a,t2),t3),16)
                r[i]=check(add(add(a,t1),t2),16)
        record('radix3')
        for step in (64,32,16,8,4):
            for start in range(0,n,2*step):
                z=zetas[k];k+=1
                for i in range(start,start+step):
                    a,b=r[i],r[i+step]
                    t=fqmul(z,b)
                    right,left=check(sub(a,t),16),check(add(a,t),16)
                    if schedule=='per_layer':right,left=barrett(right),barrett(left)
                    r[i+step],r[i]=right,left
            record('radix2_'+str(step))
        assert k==192
        raw = {'lower':min(a[0] for a in r),'upper':max(a[1] for a in r)}
        if schedule=='final_sweep':
            r=[barrett(a) for a in r];record('final_barrett')
        assert all(-half <= a[0] <= a[1] <= half for a in r)
        certificate[schedule]={'layers':layers,'before_final_sweep':raw,'statistics':statistics,'twiddles_consumed':k-1,'all_butterfly_argument_narrowings_and_stores_fit_int16':True,'intentional_montgomery_lowword_truncations':'modeled modulo 2^16, not asserted to fit before truncation','all_integer_expressions_fit_int32':True,'final_range':[-half,half]}
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    return {'status':'PASS','source_sha256':{str(p.relative_to(root)):sha(p) for p in (official,params)},'input_domain':'all 768-coefficient arrays over {-1,0,1}; interval overapproximation, not sampling','barrett_v':v,'barrett_noncanonical_int16_inputs':violations,'verified_centred_interval':[-centre_limit,centre_limit],'schedules':certificate,'congruence_argument':'The separately token-bound identical butterfly/twiddle schedules agree modulo q. Montgomery results satisfy R*out ==product modq; Barrett subtracts an integer multiple ofq. Certified no-wrap bounds permit integer interpretation. Both final outputs lie in [-1728,1728], so equal residues imply equal signed words.','scope':'Executable integer bound certificate and source comparison; not an EasyCrypt C-AST equivalence theorem. Target signed narrowing/right shifts are two-complement x86-64 semantics.'}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    args=parser.parse_args()
    print(json.dumps(certify(args.root.resolve()),indent=2))
