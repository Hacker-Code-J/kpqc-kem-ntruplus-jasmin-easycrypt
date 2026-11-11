#!/usr/bin/env python3
"""Exact small RR/ring, SOTP bit and packing diagnostics; not cryptographic proof."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
import json

Q=7
TRITS=tuple(product((-1,0,1),repeat=2))
FIELD=tuple(product(range(Q),repeat=2))


def mul(a,b):
    # F7[X]/(X^2-X+1), a small surrogate, not the NTRU+ parameter ring.
    return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]+a[1]*b[1]


def mod(a):return tuple(x%Q for x in a)
def center(a):return tuple((x+Q//2)%Q-Q//2 for x in a)
def trits(a):return len(a)==2 and all(-1<=x<=1 for x in a)
def canonical(a):return len(a)==2 and all(0<=x<Q for x in a)


@lru_cache(None)
def inverse(h):
    return next((v for v in FIELD if mod(mul(h,v))==(1,0)),None)


def enc(pk,m,r):
    return mod(tuple(x+y for x,y in zip(mul(pk,r),m))) if canonical(pk) else None


def verify_candidate(pk,m,ct,candidate):
    if candidate is None:return None
    return candidate if enc(pk,m,candidate)==ct else None


def public_rr(pk,m,ct):
    if not canonical(pk) or not canonical(ct) or not trits(m):return None
    inv=inverse(pk)
    if inv is None:return None
    candidate=center(mul(tuple(x-y for x,y in zip(ct,m)),inv))
    if not trits(candidate):return None
    return verify_candidate(pk,m,ct,candidate)


def sotp_encode(message,head,tail):return (head ^ message)-tail


def sotp_kernel_decode(code,head,tail):
    total=code+tail
    return ((total+head)%2,0) if total in (0,1) else (0,1)


def sotp_guarded_decode(code,head,tail):
    if code not in (-1,0,1):return None
    message,status=sotp_kernel_decode(code,head,tail)
    return message if status==0 else None


def pack_pair(a,b):
    assert 0<=a<4096 and 0<=b<4096
    return bytes((a&255,(a>>8)|((b&15)<<4),b>>4))


def unpack_pair(raw):return raw[0]+256*(raw[1]%16),raw[1]//16+16*raw[2]


def eval_transform(p):return mod((p[0]+2*p[1],p[0]+4*p[1]))


def inverse_transform(t):
    p1=(t[1]-t[0])*pow(2,-1,Q)%Q
    return center((t[0]-2*p1,p1))


def main():
    checks=[]
    def check(label,condition):
        assert condition,label
        checks.append(label)

    units=tuple(h for h in FIELD if inverse(h) is not None)
    forward_cases=0
    for h,m,r in product(units,TRITS,TRITS):
        assert public_rr(h,m,enc(h,m,r))==r
        forward_cases+=1
    check('public-RR-forward-for-all-small-ring-trit-message-and-randomness',forward_cases>0)
    sound_cases=0
    for h,m,ct in product(FIELD,TRITS,FIELD):
        candidate=public_rr(h,m,ct)
        if candidate is not None:
            assert trits(candidate) and enc(h,m,candidate)==ct
        sound_cases+=1
    check('arbitrary-ciphertext-accepted-RR-candidate-re-encrypts-exactly',sound_cases>forward_cases)
    check('nonunit-public-key-is-rejected-without-secret-advice',public_rr((0,0),(0,0),(0,0)) is None)
    check('noncanonical-key-and-ciphertext-aliases-are-rejected',
          public_rr((8,0),(0,0),(0,0)) is None and public_rr((1,0),(0,0),(7,0)) is None)
    check('nontrit-message-is-rejected',public_rr((1,0),(2,0),(2,0)) is None)
    check('nontrit-recovered-randomness-is-rejected',public_rr((1,0),(0,0),(2,0)) is None)
    check('re-encryption-guard-rejects-a-wrong-but-trit-candidate',verify_candidate((1,0),(0,0),(1,0),(0,0)) is None)
    check('zero-randomness-is-Some-zero-not-rejection',public_rr((1,0),(1,0),(1,0))==(0,0))
    f=(-2,-3);g=(-3,-3);m=r=(-1,-1);h=mod(mul(g,inverse(mod(f))));ct=enc(h,m,r)
    ordinary_dec=tuple((x+1)%3-1 for x in center(mul(f,ct)))
    check('RR-recovers-even-when-ordinary-decryption-wraps',ordinary_dec!=m and public_rr(h,m,ct)==r)
    residues=(-32768,-3458,-3457,-1729,-1728,-1,0,1,1728,1729,3456,3457,32767)
    centered=lambda x:(x+1728)%3457-1728
    check('actual-word-normalization-boundaries-preserve-residue-and-range',
          all(-1728<=centered(x)<=1728 and centered(x)%3457==x%3457 for x in residues))
    check('normalization-is-needed-before-trit-check',centered(3456)==-1 and 3456 not in (-1,0,1))
    check('positive-center-boundary-remains-positive',centered(1728)==1728 and centered(1729)==-1728)

    for message,head,tail in product((0,1),repeat=3):
        code=sotp_encode(message,head,tail)
        assert sotp_guarded_decode(code,head,tail)==message
    check('SOTP-roundtrip-all-single-bit-inputs',True)
    for message in (0,1):
        histogram=Counter(sotp_encode(message,h,t) for h,t in product((0,1),repeat=2))
        assert {k:F(v,4) for k,v in histogram.items()}=={-1:F(1,4),0:F(1,2),1:F(1,4)}
    check('fixed-message-uniform-pad-gives-exact-CBD-law',True)
    for msg in product((0,1),repeat=2):
        histogram=Counter(tuple(sotp_encode(msg[i],pad[i],pad[i+2]) for i in (0,1))
                          for pad in product((0,1),repeat=4))
        weights={-1:F(1,4),0:F(1,2),1:F(1,4)}
        assert all(F(histogram[a,b],16)==weights[a]*weights[b] for a,b in TRITS)
    check('two-coordinate-SOTP-law-uses-disjoint-pad-bits',True)
    for code,head,tail in product((-1,0,1),(0,1),(0,1)):
        decoded=sotp_guarded_decode(code,head,tail)
        if decoded is not None:assert sotp_encode(decoded,head,tail)==code
    check('successful-decode-rigidity-all-single-bit-cases',True)
    check('decode-success-status-distinguishes-zero-message-from-failure',
          sotp_kernel_decode(0,0,0)==(0,0) and sotp_kernel_decode(-1,0,0)==(0,1))
    check('rigidity-without-success-premise-is-false',sotp_encode(sotp_kernel_decode(-1,0,0)[0],0,0)!=-1)
    check('added-trit-wrapper-rejects-nondomain-words',all(sotp_guarded_decode(x,0,0) is None for x in (-32768,-2,2,32767)))
    adaptive=Counter(sotp_encode(h,h,t) for h,t in product((0,1),repeat=2))
    check('fixed-message-hiding-does-not-cover-pad-dependent-message',adaptive[1]==0)
    check('hiding-needs-uniform-pad',sotp_encode(0,0,0)!=sotp_encode(1,0,0))

    boundary_pairs=((0,0),(3456,3456),(255,256),(256,255),(4095,4095),(3457,0))
    check('twelve-bit-wire-layout-roundtrips-boundary-coefficients',all(unpack_pair(pack_pair(a,b))==(a,b) for a,b in boundary_pairs))
    check('packing-preserves-noncanonical-values-until-a-separate-check',unpack_pair(pack_pair(3457,0))[0]==3457)
    encoded={r:pack_pair(*eval_transform(r)) for r in TRITS}
    check('small-evaluation-transform-serialization-is-injective-on-trits',len(set(encoded.values()))==len(TRITS))
    check('small-transform-serialization-roundtrips-before-G-tagging',all(inverse_transform(unpack_pair(encoded[r]))==r for r in TRITS))
    check('transform-encoding-injectivity-needs-the-trit-domain',
          eval_transform((1,0))==eval_transform((1+Q,0)))
    payload=pack_pair(3456,0)*384
    check('actual-G-wire-width-includes-one-tag-plus-1152-byte-payload',
          len(payload)==1152 and len(b'\x01'+payload)==1153 and (b'\x01'+payload)[1:]==payload)
    check('G-domain-tag-is-separate-from-F-domain',all(b'\x01'+s != b'\x00'+s for s in encoded.values()))
    check('serializing-coefficients-is-not-serializing-their-transform',pack_pair(*mod((-1,0)))!=encoded[(-1,0)])
    print(json.dumps({'status':'PASS','count':len(checks),'checks':checks,
                      'toy_forward_cases':forward_cases,'toy_arbitrary_ciphertext_cases':sound_cases,
                      'scope':'Small F7 degree-2 ring and exact one/two-bit SOTP diagnostics plus raw wire-packing boundaries. Not actual NTRU+ execution, full-transform proof, native-wrapper equivalence, ACWC2, or cryptographic security proof.'}))


if __name__=='__main__':main()
