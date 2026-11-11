#!/usr/bin/env python3
"""Independent Python integers/hashlib over actual compiled KeyGen primitives.

Controlled retry fixtures replace seed SHAKE output only; their actual inverse
statuses are rechecked. They are distinct from real-hash API executions and do
not estimate rejection/decryption-failure probabilities.
"""
import ctypes as C
import hashlib
import json
from pathlib import Path
import sys
lib=C.CDLL(sys.argv[1]);U8=C.c_uint8;U16=C.c_uint16
A=lambda n:U8*n
W=lambda n:U16*n
P='jade_ntruplus_ntruplus768_amd64_ref_'
checks=0
counts={'shape_cases':0,'pack_cases':0,'clear_cases':0,'ntt_inverse_cases':0,'inverse_failures':0,'inverse_successes':0,'real_hash_keypairs':0,'seed_hashes':0,'scripted_keypairs':0}
def check(b,msg):
 global checks
 checks+=1
 if not b:raise AssertionError(msg)
def fun(name,args,result=None):
 f=getattr(lib,name);f.argtypes=args;f.restype=result;return f
ptr8=C.POINTER(U8);ptr16=C.POINTER(U16)
shape=[fun(P+'keygen_shape_'+s,[ptr16]) for s in ('f','g')]
ntt=fun(P+'ntt',[ptr16,ptr16]);baseinv=fun(P+'poly_baseinv',[ptr16,ptr16],C.c_uint64)
tobytes=fun(P+'poly_tobytes',[ptr8,ptr16]);pack=fun(P+'keygen_pack_sk',[ptr8,ptr8,ptr8,ptr8]);clear=fun(P+'keygen_clear',[ptr8])
o_ntt=fun('poly_ntt',[ptr16]);o_inv=fun('poly_baseinv',[ptr16,ptr16],C.c_int);o_bytes=fun('poly_tobytes',[ptr8,ptr16]);o_cbd=fun('poly_cbd1',[ptr16,ptr8])
keypair=fun('ntruplus768_keypair',[ptr8,ptr8],C.c_int);seed=fun('seed_rng',[ptr8]);reset=fun('trace_reset',[C.c_uint,C.c_uint,C.c_int]);prepare=fun('prepare_retry_fixtures',[])
rngcalls=fun('oracle_rng_calls',[],C.c_uint);clearcalls=fun('oracle_clear_calls',[],C.c_uint);bad=fun('oracle_bad',[],C.c_uint)
getseed=fun('oracle_seed',[ptr8,C.c_uint]);getbuf=fun('oracle_buffer',[ptr8,C.c_uint]);gethfinput=fun('oracle_hash_f_input',[ptr8]);gethfoutput=fun('oracle_hash_f_output',[ptr8])
fixture=fun('retry_fixture',[ptr8,C.c_uint,C.c_uint]);getf=fun('oracle_f_attempts',[],C.c_uint);getg=fun('oracle_g_attempts',[],C.c_uint)
def guarded8(n,data=None):
 a=A(n+64)(*([165]*(n+64)));p=C.cast(C.byref(a,32),ptr8)
 if data is not None:C.memmove(p,bytes(data),n)
 return a,p
def intact(a,n):check(bytes(a[:32])==bytes([165])*32 and bytes(a[n+32:])==bytes([165])*32,'byte canaries')
def signed(x):return x if x<32768 else x-65536
def word_values(p):return [signed(int(p[i])) for i in range(768)]
patterns=[[-1]*768,[0]*768,[1]*768]
patterns += [[((i*73+k*31)^(i//8+k))%3-1 for i in range(768)] for k in range(128)]
for values in patterns:
 for phase in range(2):
  a=W(800)(*([0xa55a]*800));p=C.cast(C.byref(a,32),ptr16)
  for i,v in enumerate(values):p[i]=v&65535
  shape[phase](p);expected=[3*x+(1 if not phase and i==0 else 0) for i,x in enumerate(values)]
  check(word_values(p)==expected,'actual shaped coefficients / integer oracle');check(list(a[:16])+list(a[784:])==[0xa55a]*32,'shape canaries');counts['shape_cases']+=1
  before=list(p[:768]);j=W(768)();o=W(768)(*before);ntt(j,p);o_ntt(o)
  check(list(p[:768])==before,'NTT input preserved');jv,ov=word_values(j),word_values(o)
  check(jv==ov,'full f/g domain NTT raw words');check(all((x-y)%3457==0 for x,y in zip(jv,ov)),'full f/g domain NTT residues');check(all(-3457<=x<3457 for x in jv+ov),'serializer ranges')
  jb,ob=A(1152)(),A(1152)();tobytes(jb,j);o_bytes(ob,o);check(bytes(jb)==bytes(ob),'NTT canonical bytes')
  ji,oi=W(768)(*([0xa55a]*768)),W(768)(*([0xa55a]*768));jr,orr=baseinv(ji,j),o_inv(oi,o)
  check(jr==orr and jr in (0,1),'inverse exact status');counts['ntt_inverse_cases']+=1
  check(word_values(j)==jv and word_values(o)==ov,'inverse input preservation')
  if jr:
   check(all(x==0 for x in ji),'Jasmin inverse failure zeroization');counts['inverse_failures']+=1
  else:
   check(list(ji)==list(oi),'successful inverse raw words')
   check(all((x-y)%3457==0 for x,y in zip(word_values(ji),word_values(oi))),'inverse successful residues')
   tobytes(jb,ji);o_bytes(ob,oi);check(bytes(jb)==bytes(ob),'successful inverse canonical bytes');counts['inverse_successes']+=1
for k in range(64):
 f=bytes((i*29+k)&255 for i in range(1152));h=bytes((i*73-k)&255 for i in range(1152));v=bytes((i*11+k)&255 for i in range(32))
 fa,fp=guarded8(1152,f);ha,hp=guarded8(1152,h);va,vp=guarded8(32,v);out,p=guarded8(2336,bytes([k])*2336)
 pack(p,fp,hp,vp);check(bytes(p[:2336])==f+h+v,'secret key concatenation')
 for a,n in ((fa,1152),(ha,1152),(va,32),(out,2336)):intact(a,n)
 check(bytes(fp[:1152])==f and bytes(hp[:1152])==h and bytes(vp[:32])==v,'pack inputs preserved');counts['pack_cases']+=1
for k in (0,1,2,3,7,31,63,127,128,165,170,254,255):
 a,p=guarded8(14466,bytes([k])*14466);clear(p);check(bytes(p[:14466])==bytes(14466),'actual full workspace clear');intact(a,14466);counts['clear_cases']+=1
prepare()
for k in range(100):
 seed(A(48)(*[(k*73+i*31)&255 for i in range(48)]));reset(0,0,0)
 pka,pk=guarded8(1152,bytes([k])*1152);ska,sk=guarded8(2336,bytes([255-k])*2336)
 check(keypair(pk,sk)==0,'real SHAKE API success');intact(pka,1152);intact(ska,2336)
 check(clearcalls()==1 and bad()==0,'actual cleanup and trace diagnostics');n=rngcalls();check(2<=n<=64,'bounded observed trace')
 for i in range(n):
  s,b=A(32)(),A(192)();getseed(s,i);getbuf(b,i)
  check(hashlib.shake_256(bytes(s)).digest(192)==bytes(b),'independent real seed SHAKE input/output');counts['seed_hashes']+=1
 hi,ho=A(1153)(),A(32)();gethfinput(hi);gethfoutput(ho)
 check(bytes(hi)==b'\0'+bytes(pk[:1152]),'actual HashF input');check(hashlib.shake_256(bytes(hi)).digest(32)==bytes(ho)==bytes(sk[2304:2336]),'independent HashF and serialized secret suffix');counts['real_hash_keypairs']+=1
fixture_hashes={}
for phase in range(2):
 for success in range(2):
  b=A(192)();fixture(b,phase,success);fixture_hashes[f'{"f" if phase==0 else "g"}-{success}']=hashlib.sha256(bytes(b)).hexdigest()
  x,j,inv=W(768)(),W(768)(),W(768)();o_cbd(x,b);shape[phase](x);ntt(j,x)
  check(baseinv(inv,j)==1-success,'controlled SHAKE fixture actual inverse status')
for f in range(4):
 for g in range(4):
  seed(A(48)(*range(48)));reset(f,g,1);pk,sk=A(1152)(),A(2336)();check(keypair(pk,sk)==0,'scripted API success')
  check(getf()==f+1 and getg()==g+1 and rngcalls()==f+g+2,'scripted independent retry counts');check(clearcalls()==1 and bad()==0,'scripted cleanup');counts['scripted_keypairs']+=1
print(json.dumps({'status':'PASS',**counts,'assertions':checks,'retry_fixture_sha256':fixture_hashes,'scope':'Actual helpers, f/g domain boundary transforms/inverses, real SHAKE/hashlib checks and controlled SHAKE-output retries. No probability estimation; official failed inverse output intentionally unspecified.'}))
