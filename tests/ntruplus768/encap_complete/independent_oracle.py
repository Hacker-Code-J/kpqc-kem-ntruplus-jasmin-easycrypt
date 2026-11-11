#!/usr/bin/env python3
"""Independent Encaps bit/hash/modular oracles; KAT is not a failure bound."""
import argparse
import ctypes as C
import hashlib
import json
import random
from pathlib import Path
counts=dict(assertions=0,encode_cases=0,centered_add_cases=0,fused_cases=0,fused_raw_word_differences=0,hash_f_cases=0,copy_cases=0,workspace_clear_cases=0,coin_clear_cases=0,full_api_cases=0,full_hash_triples=0)

def require(ok,msg):
 counts['assertions']+=1
 if not ok:raise AssertionError(msg+' counts='+repr(counts))
class Buffer:
 def __init__(self,n,data=None):
  self.n=n;self.raw=(C.c_uint8*(n+64))(*([165]*(n+64)));self.ptr=C.cast(C.byref(self.raw,32),C.c_void_p)
  if data is not None:require(len(data)==n,'fixture size');C.memmove(self.ptr,data,n)
 def bytes(self):return C.string_at(self.ptr,self.n)
 def guards(self):return bytes(self.raw[:32])==bytes([165])*32 and bytes(self.raw[-32:])==bytes([165])*32

def words(xs):return b''.join((x&65535).to_bytes(2,'little') for x in xs)
def signed(b):return [int.from_bytes(b[i:i+2],'little',signed=True) for i in range(0,len(b),2)]
def serialize(xs):return sum((x%3457)<<(12*i) for i,x in enumerate(xs)).to_bytes(1152,'little')

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('library',type=Path);p.add_argument('kat',type=Path);args=p.parse_args()
 lib=C.CDLL(str(args.library.resolve()));rng=random.Random(0x768eacaf)
 def function(name,n,result=None):
  f=getattr(lib,name);f.argtypes=[C.c_void_p]*n;f.restype=result;return f
 prefix='jade_ntruplus_ntruplus768_amd64_ref_'
 encode=function(prefix+'poly_sotp_encode',3);c_encode=function('poly_sotp_encode',3)
 decode=function(prefix+'poly_sotp_decode',3,C.c_uint32)
 ntt=function(prefix+'ntt',2);c_ntt=function('poly_ntt',1)
 tobytes=function(prefix+'poly_tobytes',2);c_tobytes=function('poly_tobytes',2)
 add=function(prefix+'poly_centered_add',3);basemul=function(prefix+'poly_basemul',3);c_fused=function('poly_basemul_add',4)
 prep=function(prefix+'encap_hash_f_prepare',2);c_hashf=function('oracle_hash_f',2)
 copy=function(prefix+'encap_copy_key',2);clear=function(prefix+'encap_clear',1);clearcoins=function(prefix+'encap_clear_coins',1)
 derand=function('ntruplus768_encaps_derand',4,C.c_int);encaps=function('ntruplus768_encaps',3,C.c_int)
 decaps=function('ntruplus768_decaps',3,C.c_int);keypair=function('official_keypair',2,C.c_int)
 seed=function('seed_rng',1);randombytes=lib.e_randombytes;randombytes.argtypes=[C.c_void_p,C.c_size_t];randombytes.restype=None
 fi=(C.c_uint8*1153).in_dll(lib,'hash_f_input');fo=(C.c_uint8*32).in_dll(lib,'hash_f_output')
 gi=(C.c_uint8*1153).in_dll(lib,'hash_g_input');go=(C.c_uint8*192).in_dll(lib,'hash_g_output')
 hi=(C.c_uint8*129).in_dll(lib,'hash_h_input');ho=(C.c_uint8*224).in_dll(lib,'hash_h_output');sampled=(C.c_uint8*96).in_dll(lib,'last_coins')
 def check_encode(msg,pad):
  expected=[(((msg[i//8]^pad[i//8])>>(i%8))&1)-((pad[96+i//8]>>(i%8))&1) for i in range(768)]
  mb,pb,out,ref=Buffer(96,msg),Buffer(192,pad),Buffer(1536),Buffer(1536)
  encode(out.ptr,mb.ptr,pb.ptr);c_encode(ref.ptr,mb.ptr,pb.ptr)
  require(out.bytes()==ref.bytes()==words(expected),'SOTP trits vs independent bit differences and official C')
  require(all(-1<=x<=1 for x in signed(out.bytes())),'encoder output trits')
  recovered=Buffer(96);require(decode(recovered.ptr,out.ptr,pb.ptr)==0 and recovered.bytes()==msg,'actual encoder/decoder roundtrip')
  nt,cn=Buffer(1536),Buffer(1536,ref.bytes());ntt(nt.ptr,out.ptr);c_ntt(cn.ptr)
  require(nt.bytes()==cn.bytes(),'existing NTT exact trit-input compatibility')
  require(mb.bytes()==msg and pb.bytes()==pad and out.bytes()==words(expected),'encode/NTT inputs preserved')
  require(all(x.guards() for x in (mb,pb,out,ref,recovered,nt,cn)),'encode canaries');counts['encode_cases']+=1
 for start in range(0,65536,96):
  msg=bytes((start+i*29)&255 for i in range(96));pad=bytearray(192)
  for i in range(96):v=(start+i)&65535;pad[i]=(v&255)^msg[i];pad[96+i]=v>>8
  check_encode(msg,bytes(pad))
 for i in range(768):
  for component in range(3):
   msg=bytearray(96);pad=bytearray(192)
   if component==0:msg[i//8]=1<<(i%8)
   else:pad[(component-1)*96+i//8]=1<<(i%8)
   check_encode(bytes(msg),bytes(pad))
 for _ in range(256):check_encode(bytes(rng.getrandbits(8) for _ in range(96)),bytes(rng.getrandbits(8) for _ in range(192)))
 def check_add(a,b):
  ab,bb,out=Buffer(1536,words(a)),Buffer(1536,words(b)),Buffer(1536);add(out.ptr,ab.ptr,bb.ptr);actual=signed(out.bytes())
  require(all(-3457<=x<3457 for x in actual),'centered-add serialization range')
  require(all((x-a[i]-b[i])%3457==0 for i,x in enumerate(actual)),'centered-add modular sum')
  require(all(actual[i]==a[i]+b[i] for i in range(768) if -3457<=a[i]+b[i]<3457),'sum unchanged when already inside admitted range')
  require(serialize(actual)==serialize([a[i]+b[i] for i in range(768)]),'canonical sum bytes')
  require(ab.bytes()==words(a) and bb.bytes()==words(b) and all(x.guards() for x in (ab,bb,out)),'add inputs/canaries');counts['centered_add_cases']+=1
 for a in (-3457,-3456,-1729,-1728,-1,0,1,1728,1729,3455,3456):
  for b in (-1728,-1727,-1,0,1,1727,1728):check_add([a]*768,[b]*768)
 for i in range(768):
  for a,b in [(-3457,-1),(-3457,0),(-3457,1),(3456,0),(3456,1),(3456,1728)]:
   aa=[0]*768;bb=[0]*768;aa[i]=a;bb[i]=b;check_add(aa,bb)
 for _ in range(512):check_add([rng.randrange(-3457,3457) for _ in range(768)],[rng.randrange(-1728,1729) for _ in range(768)])
 for _ in range(256):
  h=[rng.randrange(3457) for _ in range(768)];r=[rng.randrange(-1,2) for _ in range(768)];m=[rng.randrange(-1,2) for _ in range(768)]
  hb,rb,mb=Buffer(1536,words(h)),Buffer(1536,words(r)),Buffer(1536,words(m));rn,mn=Buffer(1536),Buffer(1536)
  ntt(rn.ptr,rb.ptr);ntt(mn.ptr,mb.ptr);prod,out,ref=Buffer(1536),Buffer(1536),Buffer(1536)
  basemul(prod.ptr,hb.ptr,rn.ptr);add(out.ptr,prod.ptr,mn.ptr);c_fused(ref.ptr,hb.ptr,rn.ptr,mn.ptr)
  actual,official=signed(out.bytes()),signed(ref.bytes())
  require(all(-3457<=x<3457 for x in actual+official),'fused/product-add ranges')
  require(all((a-b)%3457==0 for a,b in zip(actual,official)) and serialize(actual)==serialize(official),'fused/product-add congruence and exact canonical bytes')
  serial,refserial=Buffer(1152),Buffer(1152);tobytes(serial.ptr,out.ptr);c_tobytes(refserial.ptr,ref.ptr)
  require(serial.bytes()==refserial.bytes()==serialize(actual),'actual Jasmin/official canonical serialization of fused alternatives')
  counts['fused_raw_word_differences']+=sum(a!=b for a,b in zip(actual,official))
  require(hb.bytes()==words(h) and rb.bytes()==words(r) and mb.bytes()==words(m),'fused input preservation')
  require(all(x.guards() for x in (hb,rb,mb,rn,mn,prod,out,ref,serial,refserial)),'fused canaries');counts['fused_cases']+=1
 def check_hashf(pk):
  pb,ib,out=Buffer(1152,pk),Buffer(1153),Buffer(32);prep(ib.ptr,pb.ptr);c_hashf(out.ptr,pb.ptr)
  require(ib.bytes()==b'\0'+pk and out.bytes()==hashlib.shake_256(ib.bytes()).digest(32),'HashF payload/domain and official SHAKE output')
  require(pb.bytes()==pk and all(x.guards() for x in (pb,ib,out)),'HashF inputs/canaries');counts['hash_f_cases']+=1
 for v in range(256):check_hashf(bytes((v+i*23)&255 for i in range(1152)))
 for i in range(1152):
  for v in (1,255):pk=bytearray(1152);pk[i]=v;check_hashf(bytes(pk))
 for v in range(256):
  h=bytes((v+i*17)&255 for i in range(224));hb,out=Buffer(224,h),Buffer(32);copy(out.ptr,hb.ptr)
  require(out.bytes()==h[:32] and hb.bytes()==h and hb.guards() and out.guards(),'key copy exact prefix and preserved input');counts['copy_cases']+=1
 for kernel,size,key in [(clear,13634,'workspace_clear_cases'),(clearcoins,96,'coin_clear_cases')]:
  for v in (0,1,127,128,165,255):
   b=Buffer(size,bytes([v])*size);kernel(b.ptr);require(b.bytes()==bytes(size) and b.guards(),'all clear bytes and canaries');counts[key]+=1
  for _ in range(8):
   b=Buffer(size,bytes(rng.getrandbits(8) for _ in range(size)));kernel(b.ptr);require(b.bytes()==bytes(size) and b.guards(),'random clear bytes and canaries');counts[key]+=1
 kats=[];current={}
 for line in args.kat.read_text().splitlines():
  if line.startswith('count = '):
   if current:kats.append(current)
   current={}
  elif ' = ' in line:
   k,v=line.split(' = ',1)
   if k in ('seed','pk','sk','ct','ss'):current[k]=bytes.fromhex(v)
 if current:kats.append(current)
 require(len(kats)==100,'official KAT inventory')
 def check_full(kat,randomized,invalid=False,position=0):
  sb=Buffer(48,kat['seed']);seed(sb.ptr);pkout,skout=Buffer(1152),Buffer(2336);require(keypair(pkout.ptr,skout.ptr)==0,'reference KAT keypair')
  require(pkout.bytes()==kat['pk'] and skout.bytes()==kat['sk'],'reference KAT exact keys')
  coins=Buffer(96)
  if not randomized:randombytes(coins.ptr,96)
  original_pk=bytearray(kat['pk'])
  if invalid:
   bit=12*position;num=int.from_bytes(original_pk,'little');num=(num&~(4095<<bit))|(4095<<bit);original_pk=bytearray(num.to_bytes(1152,'little'))
  pk,ct,ss=Buffer(1152,bytes(original_pk)),Buffer(1152),Buffer(32);coins_before=coins.bytes()
  lib.trace_reset();status=encaps(ct.ptr,ss.ptr,pk.ptr) if randomized else derand(ct.ptr,ss.ptr,pk.ptr,coins.ptr)
  require(status==int(invalid),'full API canonical acceptance')
  require(lib.oracle_rng_calls()==int(randomized) and lib.oracle_rng_bytes()==96*int(randomized),'full API RNG order/count')
  require(lib.oracle_clear_calls()==1 and lib.oracle_coin_clear_calls()==int(randomized) and lib.oracle_clear_bad()==0,'real workspace/coins cleanup')
  require(lib.oracle_hash_calls()==(0 if invalid else 3),'invalid pk hashes skipped')
  if invalid:require(ct.bytes()==bytes(1152) and ss.bytes()==bytes(32),'invalid pk zero outputs')
  else:
   used_coins=bytes(sampled) if randomized else coins_before
   require(bytes(fi)==b'\0'+kat['pk'] and bytes(fo)==hashlib.shake_256(bytes(fi)).digest(32),'actual HashF independent oracle')
   require(bytes(hi)==b'\x02'+used_coins+bytes(fo) and bytes(ho)==hashlib.shake_256(bytes(hi)).digest(224),'actual HashH independent oracle')
   r=[((ho[32+i//8]>>(i%8))&1)-((ho[128+i//8]>>(i%8))&1) for i in range(768)]
   nr=Buffer(1536,words(r));c_ntt(nr.ptr)
   require(bytes(gi)==b'\x01'+serialize(signed(nr.bytes())) and bytes(go)==hashlib.shake_256(bytes(gi)).digest(192),'actual HashG regenerated polynomial and hash oracle')
   require(ct.bytes()==kat['ct'] and ss.bytes()==kat['ss']==bytes(ho)[:32],'actual complete KAT bytes')
   recovered=Buffer(32);key=Buffer(2336,kat['sk']);require(decaps(recovered.ptr,ct.ptr,key.ptr)==0 and recovered.bytes()==ss.bytes(),'existing Decaps roundtrip on KAT')
   require(recovered.guards() and key.guards() and key.bytes()==kat['sk'],'roundtrip key/canaries');counts['full_hash_triples']+=1
  require(pk.bytes()==bytes(original_pk) and coins.bytes()==coins_before and all(x.guards() for x in (pk,ct,ss,coins)),'full API inputs/canaries');counts['full_api_cases']+=1
 for kat in kats:
  for mode in (False,True):check_full(kat,mode)
 for i in range(32):
  for mode in (False,True):check_full(kats[i],mode,True,i*23)
 expected={'encode_cases':3243,'centered_add_cases':5197,'fused_cases':256,'hash_f_cases':2560,'copy_cases':256,'workspace_clear_cases':14,'coin_clear_cases':14,'full_api_cases':264,'full_hash_triples':200}
 require(all(counts[k]==v for k,v in expected.items()),'complete oracle coverage')
 print(json.dumps({'status':'PASS',**counts,'hash_oracle':'Python hashlib.shake_256','fused_scope':'Congruence, ranges and canonical byte equality; raw word equality is deliberately not required.','roundtrip_scope':'KAT regression is not a no-wrap theorem or decryption-failure probability bound.'}))

if __name__=='__main__':main()
