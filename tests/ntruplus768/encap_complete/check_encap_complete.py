#!/usr/bin/env python3
"""Exact source, RNG order, cleanup, official body and extraction gates."""
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
JASMIN=ROOT/'ntruplus/jasmin/768/ref';C_SOURCE=ROOT/'ntruplus/c/768/ref/encap_complete.c'
DECAP_C=C_SOURCE.with_name('decap_complete.c');MESSAGE_C=C_SOURCE.with_name('decap_message.c')
PREFIX='jade_ntruplus_ntruplus768_amd64_ref_'
NEW_KERNELS={
 'poly_sotp_encode_checked':('encode','poly_sotp_encode','NTRUPlus768PolySOTPEncodeChecked.ec',{'Array96.ec','Array192.ec','Array768.ec','WArray96.ec','WArray192.ec','WArray1536.ec','NTRUPlus768PolySOTPEncodeChecked.ec'}),
 'poly_centered_add_checked':('add','poly_centered_add','NTRUPlus768PolyCenteredAdd.ec',{'Array768.ec','WArray1536.ec','NTRUPlus768PolyCenteredAdd.ec'}),
 'encap_hash_f_prepare_checked':('hashf','encap_hash_f_prepare','NTRUPlus768EncapHashFPrepare.ec',{'Array1152.ec','Array1153.ec','WArray1152.ec','WArray1153.ec','NTRUPlus768EncapHashFPrepare.ec'}),
 'encap_copy_key_checked':('copy','encap_copy_key','NTRUPlus768EncapCopyKey.ec',{'Array224.ec','Array32.ec','WArray224.ec','WArray32.ec','NTRUPlus768EncapCopyKey.ec'}),
 'encap_clear_checked':('clear','encap_clear','NTRUPlus768EncapClear.ec',{'Array13634.ec','WArray13634.ec','NTRUPlus768EncapClear.ec'}),
 'encap_clear_coins_checked':('clearcoins','encap_clear_coins','NTRUPlus768EncapClearCoins.ec',{'Array96.ec','WArray96.ec','NTRUPlus768EncapClearCoins.ec'})}
STAGES=[(label,JASMIN/(name+'.jazz'),PREFIX+name) for label,name in
 [('guard','encap_guard'),('hashh','decap_hash_h_prepare'),('cbd','poly_cbd1'),('ntt','ntt'),('message_prepare','decap_message_prepare'),('basemul','poly_basemul'),('tobytes','poly_tobytes'),
  ('decapguard','decap_guard'),('candidate','decap_candidate'),('r2','decap_r2'),('sotpdecode','poly_sotp_decode'),('finish','decap_finish'),('decapclear','decap_clear')]]
STAGES += [(label,JASMIN/(name+'.jazz'),PREFIX+name) for label,name,_,_ in NEW_KERNELS.values()]
PROOF_DIRS=('encap_complete','kem_agreement',*NEW_KERNELS)

def dependencies(path):
 out={path.resolve()}
 for relative in re.findall(r'\brequire\s+"([^"\n]+)"',path.read_text()):
  target=(path.parent/relative).resolve();require(target.is_relative_to(JASMIN.resolve()),'Jasmin dependency escapes');out|=dependencies(target)
 return out

def source_dependencies():
 out={p for c in (C_SOURCE,DECAP_C,MESSAGE_C) for p in (c,c.with_suffix('.h'))}
 for _,path,_ in STAGES:out|=dependencies(path)
 return out

def check_source(data=None):
 pins=json.loads((TEST/'source-pins.json').read_text());paths=source_dependencies()
 require(set(pins)=={str(p.relative_to(ROOT)) for p in paths},'source inventory drift')
 for path in paths:
  contents=data if data is not None and path==C_SOURCE else path.read_bytes()
  require(sha(contents)==pins[str(path.relative_to(ROOT))],'source pin drift: '+str(path))
 c=(C_SOURCE.read_bytes() if data is None else data).decode()
 ordered=['struct encap_workspace w = {0};','status = '+PREFIX+'encap_guard(w.h, ct, ss, pk);','if (status != 0)','goto cleanup;',
  PREFIX+'encap_hash_f_prepare(w.input, pk);','shake256(w.hash_f, sizeof w.hash_f, w.input, sizeof w.input);',
  PREFIX+'decap_hash_h_prepare(\n        w.hash_h_input, coins, w.hash_f);','shake256(w.hash_output, sizeof w.hash_output,',
  PREFIX+'poly_cbd1(w.r, w.hash_output + 32);',PREFIX+'ntt(w.r_ntt, w.r);',PREFIX+'decap_message_prepare(',
  'shake256(w.pad, sizeof w.pad, w.input, sizeof w.input);',PREFIX+'poly_sotp_encode(w.m, coins, w.pad);',PREFIX+'ntt(w.m_ntt, w.m);',
  PREFIX+'poly_basemul(w.product, w.h, w.r_ntt);',PREFIX+'poly_centered_add(w.c, w.product, w.m_ntt);',
  PREFIX+'poly_tobytes(ct, w.c);',PREFIX+'encap_copy_key(ss, w.hash_output);','cleanup:',PREFIX+'encap_clear((uint8_t *)&w);','return (int)status;',
  'uint8_t coins[96] = {0};','randombytes(coins, sizeof coins);','status = ntruplus768_encaps_derand(ct, ss, pk, coins);',PREFIX+'encap_clear_coins(coins);','return status;']
 positions=[c.index(x,c.index('int ntruplus768_encaps_derand(')) for x in ordered]
 require(positions==sorted(positions),'C API/hash/RNG/cleanup order drift')
 require(c.count('_Static_assert(offsetof(struct encap_workspace,')==13 and '_Static_assert(sizeof(struct encap_workspace) == 13634' in c,'workspace layout assertions drift')
 require(c.count('randombytes(coins, sizeof coins);')==1,'exactly one RNG request in randomized wrapper')
 for _,name,_,_ in NEW_KERNELS.values():
  code=re.sub(r'//[^\n]*|/\*.*?\*/','',(JASMIN/(name+'.jazz')).read_text(),flags=re.S)
  require('#declassify' not in code,'new kernels must not declassify')

def check_extraction(stored,fresh,expected):
 def read(directory):
  paths=list(directory.rglob('*'));require(all(not p.is_symlink() for p in paths),'symlink in extraction')
  require(all(p.suffix=='.ec' for p in paths if p.is_file()),'unexpected extraction file')
  return {str(p.relative_to(directory)):p.read_bytes() for p in paths if p.is_file()}
 before,after=read(stored),read(fresh);require(set(before)==set(after)==expected,'whole extraction inventory drift');require(before==after,'raw extraction byte drift')
 return {p:sha(v) for p,v in before.items()}

def check():reference.guard.check_reference();check_source()
if __name__=='__main__':check();print('PASS: exact Encaps core, RNG/cleanup order, dependencies and official fixture')
