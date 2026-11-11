#!/usr/bin/env python3
"""Exact algebra and finite-law diagnostics; not a cryptographic proof replay."""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'ntruplus/proof/768/ref'
CONVOLUTION=BASE/'valid_key_m1_recovery/NTRUPlus768IntegerConvolution.ec'
RECOVERY=BASE/'valid_key_m1_recovery/NTRUPlus768ValidKeyM1Recovery.ec'
CBD=BASE/'decap_poly_cbd1/NTRUPlus768PolyCBD1Algebra.ec'
N=768
HALF=384


def require(condition,message):
    if not condition:raise ValueError(message)


def reduced_monomial(s):
    require(0<=s<=1534,'monomial must be reachable by the actual 768-by-768 product')
    if s<768:return {s:1}
    if s<1152:return {s-384:1,s-768:-1}
    return {s-1152:-1}


def long_division_monomial(s):
    coefficients={s:1}
    while max(coefficients)>=N:
        top=max(coefficients);value=coefficients.pop(top)
        for index,weight in ((top-HALF,1),(top-N,-1)):
            coefficients[index]=coefficients.get(index,0)+weight*value
            if coefficients[index]==0:del coefficients[index]
    return coefficients


def integer_product(a,b):
    """Ordinary integer convolution followed by polynomial long division."""
    full=[0]*(2*N-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                if y:full[i+j]+=x*y
    for k in range(2*N-2,N-1,-1):
        value=full[k]
        full[k-HALF]+=value;full[k-N]-=value
    return full[:N]


def block_matrix(k,i):
    """Weights of AB, AD, CB, CD for one four-trit block."""
    h=k%HALF
    if k<HALF:
        return (1,0,0,-1) if i<=h else (0,-1,-1,-1)
    return (0,1,1,1) if i<=h else (1,1,1,0)


def signed_block(a,b,k,i):
    j=(k%HALF-i)%HALF
    aa,cc,bb,dd=a[i],a[i+HALF],b[j],b[j+HALF]
    w=block_matrix(k,i)
    return w[0]*aa*bb+w[1]*aa*dd+w[2]*cc*bb+w[3]*cc*dd


def block_product(a,b):
    return [sum(signed_block(a,b,k,i) for i in range(HALF)) for k in range(N)]


def certify_basis():
    # Exhaust every pair of actual input indices, checking both candidate
    # output halves. This is independent of the dense-product computation.
    checked=0
    for i in range(N):
        for j in range(N):
            h=(i+j)%HALF
            direct=reduced_monomial(i+j)
            slot=2*(i//HALF)+(j//HALF)
            for k in (h,h+HALF):
                require(block_matrix(k,i%HALF)[slot]==direct.get(k,0),
                        'wrong signed block coefficient at '+str((i,j,k)))
                checked+=1
    return checked


def cbd4(head,tail):
    return tuple(((head>>i)&1)-((tail>>i)&1) for i in range(4))


def polynomial_forms(a,b,c,d):
    return {'diag2':a*b-c*d,'path3':a*d+c*b+c*d,'path3_other':a*b+a*d+c*b}


def histogram_mgf(histogram):
    total=sum(histogram.values())
    return sum((Q(count,total)*Q(2)**value for value,count in histogram.items()),Q(0))


def prior_definition_checks():
    def compact(path):return re.sub(r'\s+','',path.read_text())
    source=compact(CONVOLUTION)
    require('ifs<768theninteger_unitselseif s<1152'.replace(' ','') in source,'integer monomial split drift')
    require('integer_add(integer_unit(s-384))(integer_scale(-1)(integer_unit(s-768)))' in source,'middle reduction sign drift')
    require('elseinteger_scale(-1)(integer_unit(s-1152))' in source,'high reduction sign drift')
    recovery=compact(RECOVERY)
    require('integer_scale3(sampled_m1_noisefbufgbufrm)' in recovery,'actual lift must retain factor three')
    require('-1728<=(sampled_m1_integer_liftfbufgbufrm).[j]<=1728' in recovery,'actual inclusive no-wrap interval drift')
    cbd=compact(CBD)
    require('poly_cbd1_head_bitbuf(k%/8)(k%%8)-poly_cbd1_tail_bitbuf(k%/8)(k%%8)' in cbd,'CBD head-minus-tail layout drift')


def main():
    checks=[]
    def check(label,condition):require(condition,label);checks.append(label)
    prior_definition_checks()
    check('prior-integer-and-CBD-definitions-match',True)
    check('all-reachable-monomials-match-long-division',
          all(reduced_monomial(s)==long_division_monomial(s) for s in range(1535)))
    check('reduction-boundaries',all(reduced_monomial(s)==expected for s,expected in (
        (0,{0:1}),(767,{767:1}),(768,{384:1,0:-1}),
        (1151,{767:1,383:-1}),(1152,{0:-1}),(1534,{382:-1}))))
    basis_cases=certify_basis();check('all-signed-384-block-basis-coefficients',basis_cases==2*N*N)
    fixtures=[
        ([1]*N,[1]*N),
        ([i%3-1 for i in range(N)],[((17*i+3)%7)%3-1 for i in range(N)]),
        ([7]*N,[-11]*N),
        ([1 if i in (0,383) else -1 if i in (384,767) else 0 for i in range(N)],
         [-1 if i in (0,384) else 1 if i in (383,767) else 0 for i in range(N)]),
    ]
    for index,(a,b) in enumerate(fixtures):
        check('full-integer-product-versus-blocks-'+str(index),integer_product(a,b)==block_product(a,b))
    ones=integer_product([1]*N,[1]*N)
    check('dense-one-boundary-profile',ones[:HALF]==[-3*(383-i) for i in range(HALF)] and ones[HALF:]==[1152]*HALF)
    large=integer_product([7]*N,[-11]*N)
    check('integer-product-must-not-reduce-mod-q',any(abs(x)>3457 for x in large))
    check('no-wrap-can-fail-despite-small-residue',1+3*(2*ones[384])==6913 and abs((6913+1728)%3457-1728)<=1728)
    no_wrap_cases=0
    for noise in range(-580,581):
        for message in (-1,0,1):
            violation=abs(message+3*noise)>1728
            require(not violation or abs(noise)>=576,'no-wrap violation escaped the tail event')
            no_wrap_cases+=1
    check('no-wrap-violation-implies-inclusive-576-tail',no_wrap_cases==3483)
    check('strict-576-tail-would-miss-boundary',abs(1+3*576)>1728 and not 576>576)
    check('576-is-conservative-for-zero-message',abs(3*576)==1728)
    check('negative-576-boundary',abs(-1-3*576)>1728)
    check('575-guarantees-no-wrap-for-every-message',all(abs(m+3*s)<=1728 for s in (-575,575) for m in (-1,0,1)))
    # In each coefficient's decomposition, the B/D indices permute all 384
    # pairs. Each input coordinate occurs once within its convolution block
    # family; this does not imply independence across output coefficients.
    check('each-block-family-uses-every-input-pair-once',all(
        sorted((h-i)%HALF for i in range(HALF))==list(range(HALF)) for h in range(HALF)))
    check('lower-block-types-count-carry-boundary',all(
        sum(block_matrix(k,i)==(1,0,0,-1) for i in range(HALF))==k+1 for k in range(HALF)))
    check('two-products-have-768-four-trit-blocks',2*HALF==768)
    joint=Counter(cbd4(head,tail) for head in range(256) for tail in range(256))
    weight={-1:1,0:2,1:1}
    expected={v:256*weight[v[0]]*weight[v[1]]*weight[v[2]]*weight[v[3]] for v in product((-1,0,1),repeat=4)}
    check('exact-four-CBD-trit-joint-histogram',dict(joint)==expected and sum(joint.values())==65536)
    histograms={name:Counter() for name in ('diag2','path3','path3_other')}
    for values,count in joint.items():
        for name,value in polynomial_forms(*values).items():histograms[name][value]+=count//256
    path=histogram_mgf(histograms['path3']);diag=histogram_mgf(histograms['diag2'])
    check('path3-MGF-exact',path==Q(1237,1024))
    check('diag2-MGF-exact',diag==Q(289,256) and diag<=path)
    check('all-actual-path3-shapes-have-one-law',histograms['path3']==histograms['path3_other'])
    check('each-block-histogram-is-sign-symmetric',all(hist[-value]==count for hist in histograms.values() for value,count in hist.items()))
    check('path-products-cannot-be-assumed-independent',path>Q(17,16)**3)
    # High-probability conditioning can still correlate coefficients.
    pair={(a,b):Q(weight[a]*weight[b],16) for a,b in product((-1,0,1),repeat=2)}
    accepted={v:p for v,p in pair.items() if v not in ((1,-1),(-1,1))}
    mass=sum(accepted.values())
    p1=sum(p for (a,b),p in accepted.items() if a==1)/mass
    p11=accepted[(1,1)]/mass
    check('accepted-coefficients-need-not-be-independent',mass==Q(7,8) and p11!=p1*p1)
    tiny_pairs=tuple(product(range(8),repeat=2))
    tiny_accepted=tuple(v for v in tiny_pairs if v[0]<5 and v[1]<5)
    before=Q(sum(v==(0,0) for v in tiny_pairs),len(tiny_pairs))
    after=Q(sum(v==(0,0) for v in tiny_accepted),len(tiny_accepted))
    check('whole-buffer-conditioning-factor-is-necessary',after==Q(64,25)*before>before)
    check('MGF-power32-intermediate-certificate',path**32<423)
    check('integer-union-intermediate-certificate',1536*423**24<2**220)
    tail=1536*path**768/Q(2)**576
    conditioned=Q(64,25)*tail
    keygen=Q(130818,2**256)
    check('exact-unconditioned-rational-tail',tail<Q(1,2**356))
    check('exact-whole-key-conditioned-tail',conditioned<Q(1,2**354))
    check('actual-target-including-KeyGen-error',keygen+conditioned<Q(1,2**238))
    check('coarse-conditioned-target-plus-KeyGen-error',keygen+Q(1,2**354)<Q(1,2**238))
    # A repeated oracle query returns its cached answer with probability one;
    # the fresh uniform bit law would assign only one half to that value.
    def lazy_get(table,query,fresh_value):
        if query not in table:table[query]=fresh_value
        return table[query]
    cached=Counter(lazy_get({'query':0},'query',value) for value in (0,1))
    fresh=Counter(lazy_get({},'query',value) for value in (0,1))
    check('cached-H-or-G-query-is-not-fresh-uniform',cached=={0:2} and fresh=={0:1,1:1} and cached!=fresh)
    source_hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (CONVOLUTION,RECOVERY,CBD)}
    print(json.dumps({'status':'PASS','scope':'exact finite algebra/distribution diagnostics only; not a cryptographic proof',
        'count':len(checks),'checks':checks,'monomial_cases':1535,'basis_coefficient_cases':basis_cases,
        'dense_or_sparse_product_cases':len(fixtures),'no_wrap_cases':no_wrap_cases,'CBD_byte_pair_cases':65536,
        'four_trit_histograms':{name:dict(sorted(hist.items())) for name,hist in histograms.items()},
        'MGF_path3':str(path),'MGF_diag2':str(diag),'unconditioned_tail':'1536*(1237/1024)^768/2^576 < 2^-356',
        'conditioned_tail':'(64/25)*unconditioned_tail < 2^-354',
        'combined_target':'130818/2^256 + conditioned_tail < 2^-238','source_hashes':source_hashes}))


if __name__=='__main__':main()
