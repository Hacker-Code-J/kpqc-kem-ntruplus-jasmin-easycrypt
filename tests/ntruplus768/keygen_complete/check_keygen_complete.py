#!/usr/bin/env python3
"""Bind exact sources, independent rejection loops, initialized layout and helpers."""
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode=True
import prepare_reference as reference
ROOT,TEST=reference.ROOT,reference.TEST
require,sha=reference.require,reference.sha
sys.path.insert(0,str(TEST.parent/'poly_frombytes_checked'))
from check_poly_frombytes_checked import check_proof_text
JASMIN=ROOT/'ntruplus/jasmin/768/ref';C_SOURCE=ROOT/'ntruplus/c/768/ref/keygen_complete.c'
ENCAP_C=C_SOURCE.with_name('encap_complete.c');DECAP_C=C_SOURCE.with_name('decap_complete.c');MESSAGE_C=C_SOURCE.with_name('decap_message.c')
PREFIX='jade_ntruplus_ntruplus768_amd64_ref_'
EXTRACTIONS=[('keygen_shape_checked','keygen_shape_f','NTRUPlus768KeygenShapeF.ec'),('keygen_shape_checked','keygen_shape_g','NTRUPlus768KeygenShapeG.ec'),('keygen_pack_sk_checked','keygen_pack_sk','NTRUPlus768KeygenPackSK.ec'),('keygen_clear_checked','keygen_clear','NTRUPlus768KeygenClear.ec')]
NEW_KERNELS={
 'keygen_shape_checked':{'Array768.ec','WArray1536.ec','NTRUPlus768KeygenShapeF.ec','NTRUPlus768KeygenShapeG.ec'},
 'keygen_pack_sk_checked':{'Array1152.ec','Array2336.ec','Array32.ec','WArray1152.ec','WArray2336.ec','WArray32.ec','NTRUPlus768KeygenPackSK.ec'},
 'keygen_clear_checked':{'Array14466.ec','WArray14466.ec','NTRUPlus768KeygenClear.ec'}}
STAGES=[(name,JASMIN/(('keygen_shape' if name in ('keygen_shape_f','keygen_shape_g') else name)+'.jazz'),PREFIX+name) for name in
 ('encap_guard','decap_hash_h_prepare','poly_cbd1','ntt','decap_message_prepare','poly_basemul','poly_tobytes',
 'decap_guard','decap_candidate','decap_r2','poly_sotp_decode','decap_finish','decap_clear','poly_sotp_encode','poly_centered_add',
 'encap_hash_f_prepare','encap_copy_key','encap_clear','encap_clear_coins','poly_baseinv','keygen_shape_f','keygen_shape_g','keygen_pack_sk','keygen_clear')]
PROOF_DIRS=('keygen_complete','keygen_retry',*NEW_KERNELS)
def dependencies(path):
 out={path.resolve()}
 for relative in re.findall(r'\brequire\s+"([^"\n]+)"',path.read_text()):
  target=(path.parent/relative).resolve();require(target.is_relative_to(JASMIN.resolve()),'Jasmin dependency escapes');out|=dependencies(target)
 return out
def source_dependencies():
 out={p for c in (C_SOURCE,ENCAP_C,DECAP_C,MESSAGE_C) for p in (c,c.with_suffix('.h'))}
 for _,path,_ in STAGES:out|=dependencies(path)
 return out
def check_source(data=None):
 pins=json.loads((TEST/'source-pins.json').read_text());paths=source_dependencies()
 require(set(pins)=={str(p.relative_to(ROOT)) for p in paths},'source inventory drift')
 for path in paths:
  contents=data if data is not None and path==C_SOURCE else path.read_bytes()
  require(sha(contents)==pins[str(path.relative_to(ROOT))],'source pin drift: '+str(path))
 c=(C_SOURCE.read_bytes() if data is None else data).decode();body=c[c.index('int ntruplus768_keypair('):]
 ordered=['struct keygen_workspace w = {0};']
 for v,inv in (('f','finv'),('g','ginv')):
  ordered += ['do {','randombytes(w.seed, sizeof w.seed);','shake256(w.buf, sizeof w.buf, w.seed, sizeof w.seed);',PREFIX+'poly_cbd1(w.pre, w.buf);',PREFIX+'keygen_shape_'+v+'(w.pre);',PREFIX+'ntt(w.'+v+', w.pre);','status = '+PREFIX+'poly_baseinv(w.'+inv+', w.'+v+');','} while (status != 0);']
 ordered += [PREFIX+'poly_basemul(w.h, w.g, w.finv);',PREFIX+'poly_basemul(w.hinv, w.f, w.ginv);',PREFIX+'poly_tobytes(pk, w.h);',PREFIX+'poly_tobytes(w.fbytes, w.f);',PREFIX+'poly_tobytes(w.hinvbytes, w.hinv);',PREFIX+'encap_hash_f_prepare(w.hash_input, pk);','shake256(w.hash_f, sizeof w.hash_f, w.hash_input, sizeof w.hash_input);',PREFIX+'keygen_pack_sk(\n        sk, w.fbytes, w.hinvbytes, w.hash_f);',PREFIX+'keygen_clear((uint8_t *)&w);','return 0;']
 start=0
 for token in ordered:start=body.index(token,start)+len(token)
 require(body.count('randombytes(')==2 and body.count('while (status != 0)')==2,'exactly two independent rejection loops')
 require(c.count('_Static_assert(offsetof(struct keygen_workspace,')==14 and '_Static_assert(sizeof(struct keygen_workspace) == 14466' in c,'workspace exact size and all fields')
 require('uint8_t reserved[1];' in c and '_Alignof(struct keygen_workspace) == 2' in c,'explicit final byte/alignment')
 for _,stem,_ in EXTRACTIONS:
  code=re.sub(r'//[^\n]*|/\*.*?\*/','',(JASMIN/(('keygen_shape' if stem in ('keygen_shape_f','keygen_shape_g') else stem)+'.jazz')).read_text(),flags=re.S)
  require('#declassify' not in code,'new helpers must not declassify')
def check_extraction(stored,fresh,expected):
 def read(directory):
  paths=list(directory.rglob('*'));require(all(not p.is_symlink() for p in paths),'symlink in extraction');require(all(p.suffix=='.ec' for p in paths if p.is_file()),'unexpected extraction file')
  return {str(p.relative_to(directory)):p.read_bytes() for p in paths if p.is_file()}
 before,after=read(stored),read(fresh);require(set(before)==set(after)==expected,'whole extraction inventory drift');require(before==after,'raw extraction byte drift');return {p:sha(v) for p,v in before.items()}
def check():reference.guard.check_reference();check_source()
if __name__=='__main__':check();print('PASS: exact KeyGen independent rejection loops, RNG/hash/cleanup order, layout and official fixture')
