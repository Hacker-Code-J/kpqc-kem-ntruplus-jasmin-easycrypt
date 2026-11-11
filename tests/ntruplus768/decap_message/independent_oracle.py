#!/usr/bin/env python3
"""Bit-stream/Python hashlib oracle across real native calls, including canaries."""
import argparse
import ctypes as C
import hashlib
import json
import random
from pathlib import Path
N, Q = 768, 3457
counts = dict(message_cases=0, message_accepts=0, message_rejects=0, raw_sotp_cases=0,
              raw_sotp_accepts=0, raw_sotp_rejects=0, raw_u16_values_covered=0, assertions=0)


def require(ok, msg):
    counts['assertions'] += 1
    if not ok: raise AssertionError(msg + ' counts=' + repr(counts))


class Buffer:
    def __init__(self, n, data=None):
        self.n=n; self.raw=(C.c_uint8*(n+64))(*([0xa5]*(n+64)))
        self.ptr=C.cast(C.byref(self.raw,32), C.c_void_p)
        if data is not None:
            require(len(data)==n,'fixture byte count'); C.memmove(self.ptr,data,n)
    def bytes(self): return C.string_at(self.ptr,self.n)
    def guards(self): return bytes(self.raw[:32])==bytes([0xa5])*32 and bytes(self.raw[-32:])==bytes([0xa5])*32


def words(a): return b''.join((x&65535).to_bytes(2,'little') for x in a)


def serialize(a):
    # Independent little-endian bit stream, not paired-byte shifts from C/Jasmin.
    value=sum((x%Q) << (12*i) for i,x in enumerate(a))
    return value.to_bytes(1152,'little')


def decode(a,pad):
    result=bytearray(96); valid=True
    for i,coefficient in enumerate(a):
        offset,bit=divmod(i,8)
        v=((coefficient&65535)+((pad[96+offset]>>bit)&1))&65535
        valid &= v <= 1
        result[offset] |= ((v ^ (pad[offset]>>bit)) & 1)<<bit
    return (0,bytes(result)) if valid else (1,bytes(96))


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('library',type=Path);args=parser.parse_args()
    lib=C.CDLL(str(args.library.resolve()))
    message=lib.ntruplus768_decap_message;message.argtypes=[C.c_void_p]*4;message.restype=C.c_uint32
    prepare=lib.jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare;prepare.argtypes=[C.c_void_p]*3;prepare.restype=None
    sotp=lib.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode;sotp.argtypes=[C.c_void_p]*3;sotp.restype=C.c_uint32
    official_sotp=lib.poly_sotp_decode;official_sotp.argtypes=[C.c_void_p]*3;official_sotp.restype=C.c_int
    official_serialize=lib.poly_tobytes;official_serialize.argtypes=[C.c_void_p]*2;official_serialize.restype=None
    official_hash=lib.oracle_hash_g;official_hash.argtypes=[C.c_void_p]*2;official_hash.restype=None
    capture_in=(C.c_uint8*1153).in_dll(lib,'message_shake_input')
    capture_out=(C.c_uint8*192).in_dll(lib,'message_shake_output')
    rng=random.Random(0x768cafe)

    def check_message(a,r):
        expected_serialized=serialize(r); expected_pad=hashlib.shake_256(b'\x01'+expected_serialized).digest(192)
        fail,msg=decode(a,expected_pad)
        ab,rb=Buffer(1536,words(a)),Buffer(1536,words(r));mb,sb=Buffer(96),Buffer(1152)
        pre_serialized,pre_input=Buffer(1152),Buffer(1153)
        prepare(pre_serialized.ptr,pre_input.ptr,rb.ptr)
        require(pre_serialized.bytes()==expected_serialized and pre_input.bytes()==b'\x01'+expected_serialized,'prepare encoding/prefix')
        actual=message(mb.ptr,sb.ptr,ab.ptr,rb.ptr)
        require(actual==fail and mb.bytes()==msg and sb.bytes()==expected_serialized,'native pipeline Python oracle')
        require(bytes(capture_in)==b'\x01'+expected_serialized and bytes(capture_out)==expected_pad,'actual SHAKE invocation bytes and output')
        cb,pb,cm=Buffer(1152),Buffer(192),Buffer(96)
        official_serialize(cb.ptr,rb.ptr);official_hash(pb.ptr,cb.ptr);cfail=official_sotp(cm.ptr,ab.ptr,pb.ptr)
        require(cb.bytes()==expected_serialized and pb.bytes()==expected_pad and cfail==fail and cm.bytes()==msg,'official three calls independent oracle')
        require(ab.bytes()==words(a) and rb.bytes()==words(r),'pipeline inputs preserved')
        require(all(b.guards() for b in (ab,rb,mb,sb,pre_serialized,pre_input,cb,pb,cm)),'pipeline canaries')
        counts['message_cases']+=1;counts['message_rejects' if fail else 'message_accepts']+=1

    def valid_message(r,payload):
        pad=hashlib.shake_256(b'\x01'+serialize(r)).digest(192)
        return [(((payload[i//8]^pad[i//8])>>(i%8))&1)-((pad[96+i//8]>>(i%8))&1) for i in range(N)]

    bounds=(-Q,-Q+1,-1729,-1728,-1,0,1,1728,1729,Q-2,Q-1)
    for v in bounds:
        r=[v]*N
        for payload in (bytes(96),bytes([255])*96):check_message(valid_message(r,payload),r)
    base=[(97*i+23)%(2*Q)-Q for i in range(N)]
    for i in range(N):
        r=base.copy();r[i]=bounds[i%len(bounds)]
        payload=bytes(rng.getrandbits(8) for _ in range(96));a=valid_message(r,payload)
        check_message(a,r)
        # A valid signed trit chosen to make the recovered v=-1 or 2 at this bit.
        pad=hashlib.shake_256(b'\x01'+serialize(r)).digest(192)
        a[i]=1 if (pad[96+i//8]>>(i%8))&1 else -1
        check_message(a,r)
    for _ in range(1024):
        r=[rng.randrange(-Q,Q) for _ in range(N)]
        a=valid_message(r,bytes(rng.getrandbits(8) for _ in range(96))) if _%2 else [rng.randrange(-1,2) for _ in range(N)]
        check_message(a,r)

    def check_sotp(a,pad):
        status,msg=decode(a,pad);ab,pb=Buffer(1536,words(a)),Buffer(192,pad);out,ref=Buffer(96),Buffer(96)
        result=sotp(out.ptr,ab.ptr,pb.ptr);official=official_sotp(ref.ptr,ab.ptr,pb.ptr)
        require(result==status==official and out.bytes()==msg==ref.bytes(),'raw SOTP exact bytes/status')
        require(ab.bytes()==words(a) and pb.bytes()==pad,'raw SOTP input preservation')
        require(all(b.guards() for b in (ab,pb,out,ref)),'raw SOTP canaries')
        counts['raw_sotp_cases']+=1;counts['raw_sotp_rejects' if status else 'raw_sotp_accepts']+=1

    for i in range(N):
        for bit in (0,1):
            pad=bytes([0x96])*96+bytes([255 if bit else 0])*96
            for v in (0,1,65535,2,65534):
                a=[0]*N;a[i]=v;check_sotp(a,pad)
    # Every u16 value appears in a real input, in bounded batches. This is not
    # exhaustive coverage of all polynomial vectors or coefficient positions.
    for start in range(0,65536,N):
        a=[(start+i)&65535 for i in range(N)]
        check_sotp(a,bytes(rng.getrandbits(8) for _ in range(192)))
    counts['raw_u16_values_covered']=65536
    for _ in range(512):check_sotp([rng.randrange(65536) for _ in range(N)],bytes(rng.getrandbits(8) for _ in range(192)))
    require(counts['message_cases']==2582 and counts['raw_sotp_cases']==8278,'complete oracle coverage')
    require(counts['message_accepts'] and counts['message_rejects'] and counts['raw_sotp_accepts'] and counts['raw_sotp_rejects'],'acceptance and rejection paths')
    print(json.dumps({'status':'PASS',**counts,'hash_oracle':'Python hashlib.shake_256',
                     'u16_coverage':'all 65536 values across 86 batches; not all vectors/positions'}))


if __name__=='__main__':main()
