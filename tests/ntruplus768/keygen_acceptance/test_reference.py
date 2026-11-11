#!/usr/bin/env python3
"""Exact finite diagnostics from prior artifacts; never an EasyCrypt proof claim."""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'ntruplus/proof/768/ref'
SCHEDULE=BASE/'ntt_schedule/NTRUPlus768NTTSchedule.ec'
ARITHMETIC=BASE/'basemul/NTRUPlus768BasemulAlgebra.ec'
TABLE=BASE/'poly_baseinv_jasmin/extracted/NTRUPlus768PolyBaseInv.ec'
EXCEPTIONS=frozenset((252,974,2483,3205))


def require(condition,message):
    if not condition:
        raise ValueError(message)


def inputs():
    arithmetic=ARITHMETIC.read_text()
    schedule=SCHEDULE.read_text()
    def integer(name,text):
        match=re.search(r'\bop\s+'+re.escape(name)+r'\s*:\s*int\s*=\s*(-?\d+)\.',text)
        require(match is not None,'missing concrete integer: '+name)
        return int(match.group(1))
    def integer_list(name,text):
        match=re.search(r'\bop\s+'+re.escape(name)+r'\s*:\s*int\s+list\s*=\s*\[(.*?)\]\.',text,re.S)
        require(match is not None,'missing concrete list: '+name)
        return [int(x) for x in re.findall(r'-?\d+',match.group(1))]
    words=TABLE.read_text().split('module M',1)[0]
    coefficients=[int(x) for x in re.findall(r'W16\.of_int\s+\(?(-?\d+)',words)]
    require(re.search(r'\bop\s+R\s*:\s*int\s*=\s*2\^16\.',arithmetic) is not None,'Montgomery radix drift')
    return {'q':integer('q',arithmetic),'rinv':integer('Rinv',arithmetic),'radix':2**16,
            'generator':integer('zeta_root',schedule),
            'indices':integer_list('figure22_indices192',schedule),'coefficients':coefficients}


def certify_roots(data):
    q=data['q']
    require(q==3457 and all(q%d for d in range(2,59)),'unexpected or nonprime field modulus')
    require(data['radix']*data['rinv']%q==1,'wrong Montgomery decoding inverse')
    require(len(data['coefficients'])==96 and len(data['indices'])==192,'terminal table dimensions')
    z_values=[sign*c*data['rinv']%q for c in data['coefficients'] for sign in (1,-1)]
    scheduled=[pow(data['generator'],e,q) for e in data['indices']]
    require(z_values==scheduled,'actual signed terminal z does not match NTT schedule')
    square_roots={}
    for rho in range(q):
        square_roots.setdefault(rho*rho%q,[]).append(rho)
    pairs=[]
    for z in z_values:
        pair=square_roots.get(z,[])
        require(len(pair)==2 and sum(pair)==q,'terminal z lacks its two nonzero signed roots')
        require(all(pow(rho,(q-1)//2,q)==q-1 for rho in pair),'quadratic root must be a nonsquare')
        pairs.append(tuple(pair))
    roots=[rho for pair in pairs for rho in pair]
    require(len(set(z_values))==192 and len(set(roots))==384,'terminal roots must all be distinct')
    return z_values,pairs,roots


def exponents(rho,exceptions=EXCEPTIONS):
    return (0,1,2,3,5) if rho in exceptions else (0,1,2,3,4)


def binary_sums(rho,positions,q):
    weights=[pow(rho,e,q) for e in positions]
    return [sum(weight*((mask>>j)&1) for j,weight in enumerate(weights))%q
            for mask in range(1<<len(weights))]


def certify_slices(roots,q,exceptions=EXCEPTIONS):
    failures={rho for rho in roots if len(set(binary_sums(rho,range(5),q)))!=32}
    require(failures==EXCEPTIONS,'unexpected exceptional root classification')
    for rho in roots:
        positions=exponents(rho,exceptions)
        values=binary_sums(rho,positions,q)
        require(len(set(values))==32,'five-bit subset map is not injective at rho='+str(rho))
        for offset in (0,1):
            pairs={( (3*x+offset)%q,3*y%q ) for x in values for y in values}
            require(len(pairs)==1024,'joint even/odd slice is not injective')
    return failures


def cbd(buffer,k):
    return ((buffer[k//8]>>(k%8))&1)-((buffer[96+k//8]>>(k%8))&1)


def shape(buffer,offset,scale=3):
    return [scale*cbd(buffer,k)+(offset if k==0 else 0) for k in range(768)]


def certify_shaping(scale=3):
    zero=bytearray(192); positive=bytearray(zero); negative=bytearray(zero)
    positive[0]=1;negative[96]=1
    require(shape(zero,1,scale)[0]==1,'f constant term drift')
    require(shape(positive,1,scale)[0]==4 and shape(negative,1,scale)[0]==-2,'wrong f rescaling')
    require(shape(positive,0,scale)[0]==3 and shape(negative,0,scale)[0]==-3,'wrong g rescaling')


def coordinates(coefficients,rho,q):
    even=odd=0;power=1
    for i in range(384):
        even=(even+coefficients[2*i]*power)%q
        odd=(odd+coefficients[2*i+1]*power)%q
        power=power*rho%q
    return even,odd


def certify_actual_bit_layout(roots,q):
    # Exhaust selected head-bit assignments over a fixed complete 192-byte
    # context. All remaining head bits and all negative/tail bits are retained.
    fixture=bytearray((29*i+7)%256 for i in range(192))
    cases=0
    for rho in (next(r for r in roots if r not in EXCEPTIONS),*sorted(EXCEPTIONS)):
        powers=exponents(rho)
        selected=[2*e for e in powers]+[2*e+1 for e in powers]
        require(len(set(selected))==10 and all(0<=k<768 for k in selected),'selected coordinates overlap')
        baseline=bytearray(fixture)
        for k in selected:baseline[k//8]&=255^(1<<(k%8))
        base_coordinates=coordinates(shape(baseline,1),rho,q)
        scalar=binary_sums(rho,powers,q)
        # Updating just the ten actual CBD head-bit coordinates changes the
        # f/g evaluations by the same 3-scaled binary sums.
        for mask in range(1024):
            candidate=bytearray(baseline)
            for j,k in enumerate(selected):
                if mask>>j&1:candidate[k//8]|=1<<(k%8)
            changed=[k for k in range(768) if cbd(candidate,k)!=cbd(baseline,k)]
            require(all(k in selected for k in changed),'bit update leaks outside the selected coefficient slice')
            actual=(sum(3*(cbd(candidate,k)-cbd(baseline,k))*pow(rho,k//2,q) for k in selected if k%2==0)%q,
                    sum(3*(cbd(candidate,k)-cbd(baseline,k))*pow(rho,k//2,q) for k in selected if k%2==1)%q)
            expected=(3*scalar[mask&31]%q,3*scalar[(mask>>5)&31]%q)
            require(actual==expected,'actual CBD byte layout disagrees with binary slice weights')
            require(candidate[96:]==baseline[96:],'negative CBD bits must remain conditioned context')
            cases+=1
        require(all(0<=x<q for x in base_coordinates),'field-coordinate normalization')
    return cases


def certify_quartic_factorization(z_values,pairs,q):
    fixture=bytearray((29*i+7)%256 for i in range(192))
    cases=0
    for offset in (0,1):
        coefficients=shape(fixture,offset)
        for z,roots in zip(z_values,pairs):
            reduced=[sum(coefficients[4*j+i]*pow(z,j,q) for j in range(192))%q for i in range(4)]
            a0,a1,a2,a3=reduced
            u=(a0*a0+z*(a2*a2-2*a1*a3))%q
            v=(a1*a1+z*a3*a3-2*a0*a2)%q
            norms=[]
            for rho in roots:
                even,odd=coordinates(coefficients,rho,q)
                require((even,odd)==((a0+rho*a2)%q,(a1+rho*a3)%q),'wrong terminal polynomial reduction/rescaling')
                norm=(even*even-rho*odd*odd)%q
                require((norm==0)==(even==0 and odd==0),'nonsquare norm zero criterion')
                norms.append(norm)
            require((u*u-z*v*v)%q==norms[0]*norms[1]%q,'quartic determinant factorization')
            cases+=1
    return cases


def budget_bound(initial_cache):
    require(initial_cache>=0,'negative initial-cache budget')
    total=256+256
    return Q(initial_cache*total+total*(total-1)//2,2**256)+2*Q(1,2)**256


def main():
    data=inputs();z_values,pairs,roots=certify_roots(data);q=data['q']
    exceptional=certify_slices(roots,q)
    certify_shaping()
    layout_cases=certify_actual_bit_layout(roots,q)
    factor_cases=certify_quartic_factorization(z_values,pairs,q)
    checks=['terminal-table-Montgomery-and-schedule-match','all-signed-roots-and-nonsquare-certificates',
            'exception-classification-complete','all-five-bit-subset-maps-injective',
            'all-ten-bit-even-odd-slices-injective','actual-CBD-shaping','actual-CBD-bit-layout',
            'actual-terminal-quartic-determinant-factors']
    def check(label,condition):
        require(condition,label);checks.append(label)
    reject_bound=Q(384,1024)
    check('union-bound-384-over-1024',reject_bound==Q(3,8))
    check('acceptance-complement-five-eighths',1-reject_bound==Q(5,8)>0)
    # Disjoint singleton bad events have exactly this union; multiplying their
    # complements would incorrectly assume independence across roots.
    check('independence-across-roots-is-unsafe',1-Q(1023,1024)**384<reject_bound)
    exact_tail=2*Q(3,8)**256;coarse_tail=2*Q(1,2)**256
    check('exact-tail-is-below-coarse-certified-tail',0<exact_tail<=coarse_tail==Q(2,2**256))
    check('both-phase-collision-count-is-512',512*511//2==130816)
    check('counter-reset-loses-cross-phase-collisions',512*511//2-2*(256*255//2)==256*256)
    for a in (0,1,17,256):
        check('numeric-bound-initial-cache-'+str(a),budget_bound(a)==Q(512*a+130818,2**256))
    check('empty-cache-error-strictly-below-two-minus-239',budget_bound(0)<Q(1,2**239))
    check('retry-tail-cannot-be-omitted',Q(130816,2**256)+exact_tail>Q(130816,2**256))
    for label,action in (
        ('wrong-Montgomery-inverse',lambda:certify_roots({**data,'rinv':1})),
        ('wrong-terminal-generator',lambda:certify_roots({**data,'generator':23})),
        ('exceptional-exponent-rule-omitted',lambda:certify_slices(roots,q,frozenset())),
        ('one-exception-missing',lambda:certify_slices(roots,q,EXCEPTIONS-{252})),
        ('wrong-f-g-rescaling',lambda:certify_shaping(scale=1)),
    ):
        try:action()
        except ValueError:checks.append('rejects-'+label)
        else:raise AssertionError('accepted diagnostic corruption: '+label)
    naive_collision_witnesses={}
    for rho in sorted(exceptional):
        seen={}
        for mask,value in enumerate(binary_sums(rho,range(5),q)):
            if value in seen:
                naive_collision_witnesses[rho]={'masks':[seen[value],mask],'common_residue':value}
                break
            seen[value]=mask
    source_hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (ARITHMETIC,SCHEDULE,TABLE)}
    print(json.dumps({'status':'PASS','scope':'exact finite diagnostics only; not cryptographic proof or empirical DFR',
                      'count':len(checks),'checks':checks,'terminal_z_count':len(z_values),'signed_root_count':len(roots),
                      'binary_subset_cases':len(roots)*32,'joint_slice_cases':len(roots)*1024*2,
                      'actual_layout_cases':layout_cases,'quartic_factorization_cases':factor_cases,
                      'exceptions':sorted(exceptional),'naive_collision_witnesses':naive_collision_witnesses,'rejection_union_bound':'3/8','acceptance_lower_bound':'5/8',
                      'exact_tail':'2*(3/8)^256','coarse_tail':'2/2^256','total_error_bound':'(512*a+130818)/2^256',
                      'empty_cache_upper_bound':'strictly below 2^-239','source_hashes':source_hashes}))


if __name__=='__main__':
    main()
