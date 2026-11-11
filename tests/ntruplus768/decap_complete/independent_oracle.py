#!/usr/bin/env python3
"""Independent bit/hash/key-selection oracles for actual full Decaps and kernels."""
import argparse
import ctypes as C
import hashlib
import json
import random
from pathlib import Path
counts=dict(assertions=0,cbd_cases=0,cbd_byte_pairs_covered=65536,hash_h_cases=0,finish_cases=0,clear_cases=0,full_api_cases=0,full_hash_pairs=0)


def require(ok,msg):
    counts['assertions']+=1
    if not ok:raise AssertionError(msg+' counts='+repr(counts))


class Buffer:
    def __init__(self,n,data=None):
        self.n=n;self.raw=(C.c_uint8*(n+64))(*([0xa5]*(n+64)));self.ptr=C.cast(C.byref(self.raw,32),C.c_void_p)
        if data is not None:require(len(data)==n,'fixture length');C.memmove(self.ptr,data,n)
    def bytes(self):return C.string_at(self.ptr,self.n)
    def guards(self):return bytes(self.raw[:32])==bytes([165])*32 and bytes(self.raw[-32:])==bytes([165])*32


def words(xs):return b''.join((x&65535).to_bytes(2,'little') for x in xs)
def signed(data):return [int.from_bytes(data[i:i+2],'little',signed=True) for i in range(0,len(data),2)]
def serialize(xs):return sum((x%3457)<<(12*i) for i,x in enumerate(xs)).to_bytes(1152,'little')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('library',type=Path);parser.add_argument('kat',type=Path);args=parser.parse_args()
    lib=C.CDLL(str(args.library.resolve()));rng=random.Random(0x768decaf)
    def function(name,n,result=None):
        f=getattr(lib,name);f.argtypes=[C.c_void_p]*n;f.restype=result;return f
    cbd=function('jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1',2)
    c_cbd=function('poly_cbd1',2)
    ntt=function('jade_ntruplus_ntruplus768_amd64_ref_ntt',2)
    c_ntt=function('poly_ntt',1)
    tobytes=function('jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes',2)
    c_tobytes=function('poly_tobytes',2)
    prep=function('jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare',3)
    c_hashh=function('oracle_hash_h',2)
    finish=getattr(lib,'jade_ntruplus_ntruplus768_amd64_ref_decap_finish');finish.argtypes=[C.c_void_p]*4+[C.c_uint32];finish.restype=C.c_uint32
    clear=function('jade_ntruplus_ntruplus768_amd64_ref_decap_clear',1)
    decaps=function('ntruplus768_decaps',3,C.c_int)
    ginput=(C.c_uint8*1153).in_dll(lib,'message_shake_input');goutput=(C.c_uint8*192).in_dll(lib,'message_shake_output')
    hinput=(C.c_uint8*129).in_dll(lib,'hash_h_input');houtput=(C.c_uint8*224).in_dll(lib,'hash_h_output')
    message=(C.c_uint8*96).in_dll(lib,'decoded_message')

    def check_cbd(raw):
        expected=[((raw[i//8]>>(i%8))&1)-((raw[96+i//8]>>(i%8))&1) for i in range(768)]
        source=Buffer(192,raw);out,ref=Buffer(1536),Buffer(1536)
        cbd(out.ptr,source.ptr);c_cbd(ref.ptr,source.ptr)
        require(out.bytes()==ref.bytes()==words(expected),'CBD signed bit differences')
        require(all(-1<=x<=1 for x in signed(out.bytes())),'CBD signed trits')
        transformed,reftrans=Buffer(1536),Buffer(1536,ref.bytes())
        ntt(transformed.ptr,out.ptr);c_ntt(reftrans.ptr)
        require(transformed.bytes()==reftrans.bytes(),'existing Jasmin/official NTT equality on CBD trits')
        serial,refserial=Buffer(1152),Buffer(1152)
        tobytes(serial.ptr,transformed.ptr);c_tobytes(refserial.ptr,reftrans.ptr)
        require(serial.bytes()==refserial.bytes()==serialize(signed(transformed.bytes())),'regenerated canonical serialization')
        require(source.bytes()==raw and out.bytes()==words(expected),'CBD/NTT input preservation')
        require(all(b.guards() for b in (source,out,ref,transformed,reftrans,serial,refserial)),'CBD/regeneration canaries')
        counts['cbd_cases']+=1
    for start in range(0,65536,96):
        raw=bytearray(192)
        for i in range(96):v=(start+i)&65535;raw[i]=v&255;raw[i+96]=v>>8
        check_cbd(bytes(raw))
    boundaries=(0,1,2,0x55,0x80,0xaa,0xfe,0xff)
    for i in range(192):
        for v in boundaries:
            raw=bytearray(192);raw[i]=v;check_cbd(bytes(raw))
    for i in range(768):
        for half in (0,96):
            raw=bytearray(192);raw[half+i//8]=1<<(i%8);check_cbd(bytes(raw))
    for _ in range(512):check_cbd(bytes(rng.getrandbits(8) for _ in range(192)))

    def check_hashh(msg,suffix):
        mb,sb,ib=Buffer(96,msg),Buffer(32,suffix),Buffer(129)
        prep(ib.ptr,mb.ptr,sb.ptr)
        require(ib.bytes()==b'\x02'+msg+suffix,'HashH domain/message/key-suffix order')
        payload=Buffer(128,msg+suffix);output=Buffer(224);c_hashh(output.ptr,payload.ptr)
        require(output.bytes()==hashlib.shake_256(ib.bytes()).digest(224),'official HashH independent hashlib oracle')
        require(mb.bytes()==msg and sb.bytes()==suffix,'HashH preparation input preservation')
        require(all(b.guards() for b in (mb,sb,ib,payload,output)),'HashH canaries')
        counts['hash_h_cases']+=1
    for v in range(256):check_hashh(bytes((v+i)&255 for i in range(96)),bytes((v-3*i)&255 for i in range(32)))
    for i in range(128):
        for v in boundaries:
            payload=bytearray(128);payload[i]=v;check_hashh(bytes(payload[:96]),bytes(payload[96:]))

    def check_finish(left,right,hashout,decodefail):
        lb,rb,hb=Buffer(1152,left),Buffer(1152,right),Buffer(224,hashout);ss=Buffer(32)
        expected=int(bool(decodefail) or left!=right)
        actual=finish(ss.ptr,hb.ptr,lb.ptr,rb.ptr,decodefail)
        require(actual==expected and ss.bytes()==(bytes(32) if expected else hashout[:32]),'finish comparison/failure combination/shared-secret mask')
        require(lb.bytes()==left and rb.bytes()==right and hb.bytes()==hashout,'finish all inputs preserved')
        require(all(b.guards() for b in (lb,rb,hb,ss)),'finish canaries')
        counts['finish_cases']+=1
    baseline=bytes((i*17+29)&255 for i in range(1152));hashout=bytes((i*71+11)&255 for i in range(224))
    for flag in (0,1):check_finish(baseline,baseline,hashout,flag)
    for i in range(1152):
        for bit in range(8):
            changed=bytearray(baseline);changed[i]^=1<<bit
            for flag in (0,1):check_finish(baseline,bytes(changed),hashout,flag)
    for _ in range(256):
        left=bytes(rng.getrandbits(8) for _ in range(1152));right=left if _%2 else bytes(rng.getrandbits(8) for _ in range(1152))
        h=bytes(rng.getrandbits(8) for _ in range(224));check_finish(left,right,h,_%2)

    for value in (0,1,127,128,165,255):
        workspace=Buffer(13506,bytes([value])*13506);clear(workspace.ptr)
        require(workspace.bytes()==bytes(13506) and workspace.guards(),'all workspace bytes zero and canaries preserved');counts['clear_cases']+=1
    for _ in range(16):
        workspace=Buffer(13506,bytes(rng.getrandbits(8) for _ in range(13506)));clear(workspace.ptr)
        require(workspace.bytes()==bytes(13506) and workspace.guards(),'random full workspace clear');counts['clear_cases']+=1

    kats=[];current={}
    for line in args.kat.read_text().splitlines():
        if line.startswith('count = '):
            if current:kats.append(current)
            current={}
        elif ' = ' in line:
            k,v=line.split(' = ',1)
            if k in ('ct','sk','ss'):current[k]=bytes.fromhex(v)
    if current:kats.append(current)
    require(len(kats)==100,'100 official KAT vectors')
    def check_full(ct,sk,expected_ss=None,canonical=True):
        cb,kb,ss=Buffer(1152,ct),Buffer(2336,sk),Buffer(32)
        lib.trace_reset();fail=decaps(ss.ptr,cb.ptr,kb.ptr)
        require(fail in (0,1),'full API binary status')
        require(lib.oracle_clear_calls()==1 and lib.oracle_clear_bad()==0,'actual full-API cleanup every path')
        require(lib.oracle_hash_g_calls()==int(canonical) and lib.oracle_hash_h_calls()==int(canonical),'exact full-API hash calls or rejection skip')
        if canonical:
            require(bytes(ginput)[0]==1 and bytes(goutput)==hashlib.shake_256(bytes(ginput)).digest(192),'actual HashG invocation hashlib oracle')
            require(bytes(hinput)==b'\x02'+bytes(message)+sk[2304:],'actual full HashH input')
            require(bytes(houtput)==hashlib.shake_256(bytes(hinput)).digest(224),'actual HashH invocation hashlib oracle')
            require(ss.bytes()==(bytes(32) if fail else bytes(houtput)[:32]),'full API key mask')
            counts['full_hash_pairs']+=1
        else:require(fail==1 and ss.bytes()==bytes(32),'early rejection zero key')
        if expected_ss is not None:require(fail==0 and ss.bytes()==expected_ss,'full API official KAT secret')
        require(cb.bytes()==ct and kb.bytes()==sk and all(b.guards() for b in (cb,kb,ss)),'full API byte inputs/canaries')
        counts['full_api_cases']+=1
    for kat in kats:check_full(kat['ct'],kat['sk'],kat['ss'])
    for i in range(32):
        sk=bytearray(kats[0]['sk']);sk[2304+i]^=1;check_full(kats[0]['ct'],bytes(sk))
    for i in range(128):
        kat=kats[i%100];ct=bytearray(kat['ct']);value=(int.from_bytes(ct[:2],'little')&4095);value=(value+1)%3457
        ct[0]=value&255;ct[1]=(ct[1]&240)|(value>>8);check_full(bytes(ct),kat['sk'])
    for component in range(3):
        ct=bytearray(kats[0]['ct']);sk=bytearray(kats[0]['sk']);target=ct if component==0 else sk;offset=0 if component<2 else 1152
        target[offset]=255;target[offset+1]|=15;check_full(bytes(ct),bytes(sk),canonical=False)
    expected={'cbd_cases':4267,'hash_h_cases':1280,'finish_cases':18690,'clear_cases':22,'full_api_cases':263,'full_hash_pairs':260}
    require(all(counts[k]==v for k,v in expected.items()),'complete oracle coverage')
    print(json.dumps({'status':'PASS',**counts,'hash_oracle':'Python hashlib.shake_256',
          'cbd_byte_pair_scope':'all 65536 two-byte values across 683 batches, not all positions/vectors',
          'cleanup_scope':'13506-byte caller-owned workspace after real Jasmin clear, excludes registers/spills/nested workspace'}))


if __name__=='__main__':main()
