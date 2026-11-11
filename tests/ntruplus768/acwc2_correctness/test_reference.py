#!/usr/bin/env python3
"""Exact small probability counterexamples and numerical checks, not an ACWC2 proof."""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
import json

R=(-1,0,1)
WEIGHTS=(F(1,4),F(1,2),F(1,4))
PADS=tuple(product(range(4),repeat=3))
BITS=tuple(product((0,1),repeat=3))


def weighted(values):return sum(w*v for w,v in zip(WEIGHTS,values))
def get(table,r):return table[r+1]
def center(x):return (x+3)%7-3


def sotp_encode(message,pad):return ((pad&1)^message)-(pad>>1)


def sotp_decode(code,pad):
    if code not in R:return None
    total=code+(pad>>1)
    return (total+(pad&1))%2 if total in (0,1) else None


def base_enc(code,r):return (code+3*r)%7

def base_dec(ct):
    if ct is None or not 0<=ct<7:return None
    return (center(ct)+1)%3-1


def base_failure(ct,recovered,code):return ct is None or recovered!=code


def checked_rr(code,ct):
    if code not in R or not 0<=ct<7:return None
    r=center(5*(ct-code))
    return r if r in R and base_enc(code,r)==ct else None


def transformed_dec(ct,table):
    code=base_dec(ct)
    if code is None:return None
    r=checked_rr(code,ct)
    return None if r is None else sotp_decode(code,get(table,r))


def trial(message,r,table):
    code=sotp_encode(message,get(table,r));ct=base_enc(code,r)
    return transformed_dec(ct,table)!=message,base_failure(ct,base_dec(ct),code)


def central_moment(q,n):return q*(1-q)**n+(1-q)*(-q)**n


def expanded_eighth(qs,even_only=False):
    result=F(0)
    for a in range(9):
        for b in range(9-a):
            powers=(a,b,8-a-b)
            if even_only and any(n%2 for n in powers):continue
            term=F(factorial(8),factorial(a)*factorial(b)*factorial(8-a-b))
            for w,q,n in zip(WEIGHTS,qs,powers):term*=w**n*central_moment(q,n)
            result+=term
    return result


def enumerated_eighth(thresholds):
    qs=tuple(F(x,4) for x in thresholds)
    return sum(weighted(F(g<t)-q for g,t,q in zip(table,thresholds,qs))**8 for table in PADS)/64


def main():
    checks=[]
    def check(label,condition):
        assert condition,label
        checks.append(label)

    collision=sum(w*w for w in WEIGHTS)
    check('CBD-collision-is-three-eighths-not-uniform-one-third',collision==F(3,8) and collision!=F(1,3))
    coins=tuple(product((0,1),repeat=2))
    coin_collision=sum(F(1,16) for x,y in product(coins,repeat=2) if x[0]-x[1]==y[0]-y[1])
    check('CBD-buffer-aliases-increase-collision-above-buffer-equality',coin_collision==collision and coin_collision>F(1,4))
    check('distinct-CBD-preimages-use-the-same-G-coordinate',(0-0)==(1-1) and all(get(g,0-0)==get(g,1-1) for g in PADS))
    two_weights=tuple(a*b for a,b in product(WEIGHTS,repeat=2))
    check('independent-CBD-coordinates-multiply-collision-mass',sum(x*x for x in two_weights)==collision**2)

    def err(key,message,table):return weighted(F((g^key)==message) for g in table)
    desired=sum(max(err(k,m,g) for m in (0,1)) for k in (0,1) for g in BITS)/16
    swapped=max(sum(err(k,m,g) for k in (0,1) for g in BITS)/16 for m in (0,1))
    before_G=sum(max(sum(err(k,m,g) for g in BITS)/8 for m in (0,1)) for k in (0,1))/2
    check('EkeyG-max-message-is-not-max-message-EkeyG',desired==F(3,4) and swapped==F(1,2))
    check('message-maximum-cannot-move-before-G-expectation',desired>before_G)
    check('finite-G-coordinate-pairs-have-product-law',sum(F(1,64) for g in PADS if g[0]==0 and g[2]==0)==F(1,16))
    check('repeated-G-input-is-cached-not-resampled',all(get(g,0)==get(g,0) for g in PADS) and sum(F(1,16) for a,b in product(range(4),repeat=2) if a==b)<1)

    q=F(1,4)
    exact=enumerated_eighth((1,1,1))
    check('weighted-eighth-moment-agrees-with-independent-multinomial-expansion',exact==expanded_eighth((q,q,q)))
    check('centered-failure-indicators-have-nonzero-odd-higher-moments',central_moment(q,1)==0 and central_moment(q,3)==F(3,32))
    check('dropping-odd-multiplicity-terms-underestimates-eighth-moment',exact>expanded_eighth((q,q,q),True))
    check('different-base-failure-means-do-not-require-iid-indicators',enumerated_eighth((1,2,3))==expanded_eighth((F(1,4),F(1,2),F(3,4))))
    correlated=sum((F(g==0)-q)**8 for g in range(4))/4
    check('correlated-G-coordinates-invalidate-product-moment-factorization',correlated>exact)
    key_means=tuple(sum(weighted(F(g<t) for g in table) for table in PADS)/64 for t in (1,3))
    global_mean=sum(key_means)/2
    check('centering-must-use-the-conditional-key-mean',
          key_means==(F(1,4),F(3,4)) and global_mean==F(1,2) and
          tuple(c-global_mean for c in key_means)==(-F(1,4),F(1,4)))
    # Thirty-two fair coordinates suffice to expose an erroneous S^8 replacement
    # under the declared conservative moment constant, without a large experiment.
    fair_moment=sum(F(comb(32,k),2**32)*(F(k,32)-F(1,2))**8 for k in range(33))
    check('eighth-moment-uses-fourth-not-eighth-power-of-collision',fair_moment>2**16*F(1,32)**8 and fair_moment<=2**16*F(1,32)**4)

    cases=0
    for table,message,r in product(PADS,(0,1),R):
        failure,envelope=trial(message,r,table)
        assert not failure or envelope
        cases+=1
    check('actual-toy-transformed-failure-is-pointwise-below-base-envelope',cases==384)
    for code,ct in product(R,range(7)):
        recovered=checked_rr(code,ct)
        assert recovered is None or (recovered in R and base_enc(code,recovered)==ct)
    check('toy-recovery-acceptance-retains-trit-and-re-encryption-checks',checked_rr(2,0) is None and checked_rr(0,7) is None)
    check('base-failure-includes-encryption-and-decryption-rejection',base_failure(None,0,0) and base_failure(0,None,0))
    check('successful-zero-message-and-zero-ciphertext-are-not-rejection',not base_failure(0,0,0) and transformed_dec(0,(0,0,0))==0)
    class NoOracleReads:
        def __getitem__(self,index):
            raise AssertionError('oracle queried after base decoding rejected')
    check('decoder-rejection-propagates-without-an-oracle-query',transformed_dec(None,NoOracleReads()) is None)
    # On wrap: original r=-1, code=-1, c=3, recovered code=0, recovered r=+1.
    good_other=(2,0,0);bad_other=(2,0,1)
    check('actual-Dec-failure-can-depend-on-a-different-G-entry',
          get(good_other,-1)==get(bad_other,-1) and trial(0,-1,good_other)==(False,True) and trial(0,-1,bad_other)==(True,True))
    pminus=sum(F(trial(0,-1,g)[0],64) for g in PADS)
    pplus=sum(F(trial(0,1,g)[0],64) for g in PADS)
    joint=sum(F(trial(0,-1,g)[0] and trial(0,1,g)[0],64) for g in PADS)
    check('independent-G-does-not-make-actual-Dec-failures-independent',pminus==pplus==F(1,8) and joint==F(1,16)>pminus*pplus)
    ct=base_enc(sotp_encode(0,0),0)
    check('resampling-G-on-decryption-breaks-the-base-failure-envelope',not base_failure(ct,base_dec(ct),0) and transformed_dec(ct,(0,1,0))!=0)
    actual_max=sum(max(weighted(F(trial(mu,r,g)[0]) for r in R) for mu in (0,1)) for g in PADS)/64
    base_max=sum(max(weighted(F(trial(mu,r,g)[1]) for r in R) for mu in (0,1)) for g in PADS)/64
    check('pointwise-envelope-survives-maximum-then-expectation',actual_max<=base_max)
    check('zero-base-failure-has-zero-centered-moments',central_moment(F(0),8)==0)

    eps=F(1,2**356);constant=2**16;S=collision**768
    check('message-union-count-is-bits-of-96-byte-messages',256**96==2**768)
    check('eight-coordinate-CBD-collision-has-required-dyadic-bound',collision**8<=F(1,2**11))
    check('full-CBD-collision-bound-is-two-to-minus-1056',S<=F(1,2**1056))
    coarse_tail=F(2**768*constant,2**(1056*4))/eps**8
    exact_tail=2**768*constant*S**4/eps**8
    check('eighth-moment-union-Markov-arithmetic-gives-minus-592',eps>0 and coarse_tail==F(1,2**592) and exact_tail<=coarse_tail)
    check('average-plus-threshold-plus-union-tail-is-below-minus-353',F(1,2**354)+eps+coarse_tail<F(1,2**353))
    print(json.dumps({'status':'PASS','count':len(checks),'checks':checks,
                      'toy_G_tables':len(PADS),'toy_transformed_cases':cases,
                      'toy_EkeyG_max_error':str(desired),'toy_max_EkeyG_error':str(swapped),
                      'toy_actual_failure_correlation':{'marginals':[str(pminus),str(pplus)],'joint':str(joint),'independent_product':str(pminus*pplus)},
                      'toy_cross_entry_case':{'message':0,'original_r':-1,'ciphertext':3,'recovered_code':0,'recovered_r':1,'G_tables':[good_other,bad_other],'base_failure':[True,True],'actual_failure':[False,True]},
                      'numeric_certificate':{'epsilon':'2^-356','moment_constant':constant,'collision_bound':'2^-1056','union_tail_bound':'2^-592','target':'2^-353','not_a_cryptographic_proof':True},
                      'scope':'Exact tiny biased-randomness and finite-oracle counterexamples, scalar PKE/RR/SOTP diagnostics, and independent rational arithmetic. Not actual NTRU+ execution or a replacement for the EasyCrypt worst-message proof.'}))


if __name__=='__main__':main()
