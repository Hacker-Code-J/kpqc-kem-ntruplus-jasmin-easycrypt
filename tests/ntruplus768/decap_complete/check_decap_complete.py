#!/usr/bin/env python3
"""Bind new complete Decaps wiring to exact source, reference and extraction."""
import importlib.util
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
JASMIN=ROOT/'ntruplus/jasmin/768/ref'
C_SOURCE=ROOT/'ntruplus/c/768/ref/decap_complete.c'
MESSAGE_C=C_SOURCE.with_name('decap_message.c')
PREFIX='jade_ntruplus_ntruplus768_amd64_ref_'
NEW_KERNELS={
 'poly_cbd1_checked':('cbd','poly_cbd1','NTRUPlus768PolyCBD1Checked.ec',{'Array192.ec','Array768.ec','WArray192.ec','WArray1536.ec','NTRUPlus768PolyCBD1Checked.ec'}),
 'decap_finish_checked':('finish','decap_finish','NTRUPlus768DecapFinish.ec',{'Array32.ec','Array224.ec','Array1152.ec','WArray32.ec','WArray224.ec','WArray1152.ec','NTRUPlus768DecapFinish.ec'}),
 'decap_hash_h_prepare_checked':('hashh','decap_hash_h_prepare','NTRUPlus768DecapHashHPrepare.ec',{'Array129.ec','Array32.ec','Array96.ec','WArray129.ec','WArray32.ec','WArray96.ec','NTRUPlus768DecapHashHPrepare.ec'}),
 'decap_clear_checked':('clear','decap_clear','NTRUPlus768DecapClear.ec',{'Array13506.ec','WArray13506.ec','NTRUPlus768DecapClear.ec'})}
STAGES=[(label,JASMIN/(name+'.jazz'),PREFIX+name) for label,name in
 [('guard','decap_guard'),('candidate','decap_candidate'),('r2','decap_r2'),
  ('message_prepare','decap_message_prepare'),('sotp','poly_sotp_decode'),('ntt','ntt'),('tobytes','poly_tobytes')]]
STAGES += [(label,JASMIN/(name+'.jazz'),PREFIX+name) for label,name,_,_ in NEW_KERNELS.values()]
PROOF_DIRS=('decap_complete',*NEW_KERNELS)


def dependencies(path):
    result={path.resolve()}
    for relative in re.findall(r'\brequire\s+"([^"\n]+)"',path.read_text()):
        target=(path.parent/relative).resolve();require(target.is_relative_to(JASMIN.resolve()),'Jasmin require escapes source directory')
        result|=dependencies(target)
    return result


def source_dependencies():
    paths={C_SOURCE,C_SOURCE.with_suffix('.h'),MESSAGE_C,MESSAGE_C.with_suffix('.h')}
    for _,source,_ in STAGES:paths|=dependencies(source)
    return paths


def check_source(data=None):
    pins=json.loads((TEST/'source-pins.json').read_text());paths=source_dependencies()
    require(set(pins)=={str(p.relative_to(ROOT)) for p in paths},'source dependency inventory drift')
    for path in paths:
        value=data if data is not None and path==C_SOURCE else path.read_bytes()
        require(sha(value)==pins[str(path.relative_to(ROOT))],'source/dependency pin drift: '+str(path))
    c=(C_SOURCE.read_bytes() if data is None else data).decode()
    ordered=['struct decap_workspace w = {0};',
      'fail = '+PREFIX+'decap_guard(', 'if (fail != 0)', 'goto cleanup;',
      PREFIX+'decap_candidate(w.m, w.c, w.f);',PREFIX+'decap_r2(w.r, w.c, w.m, w.h);',
      'fail = ntruplus768_decap_message(w.msg, w.serialized, w.m, w.r);',
      PREFIX+'decap_hash_h_prepare(\n        w.hash_input, w.msg, sk + 2304);',
      'shake256(w.hash_output, sizeof w.hash_output,\n             w.hash_input, sizeof w.hash_input);',
      PREFIX+'poly_cbd1(w.r1, w.hash_output + 32);',PREFIX+'ntt(w.n1, w.r1);',
      PREFIX+'poly_tobytes(w.regenerated, w.n1);','fail = '+PREFIX+'decap_finish(',
      'cleanup:',PREFIX+'decap_clear((uint8_t *)&w);','return (int)fail;']
    offsets=[c.index(x) for x in ordered];require(offsets==sorted(offsets),'full C call/failure/clear order drift')
    require(c.count('goto cleanup;')==1 and c.count('return (int)fail;')==1,'single cleanup return required')
    require('_Static_assert(sizeof(struct decap_workspace) == 13506' in c,'workspace size assertion missing')
    require(c.count('_Static_assert(offsetof(struct decap_workspace,')==12,'workspace field offset assertions drift')
    require('randombytes(' not in c,'Decaps must not call RNG')
    for _,name,_,_ in NEW_KERNELS.values():
        code=re.sub(r'//[^\n]*|/\*.*?\*/','',(JASMIN/(name+'.jazz')).read_text(),flags=re.S)
        require('#declassify' not in code,'new kernels must not declassify')


def check_extraction(stored,fresh,expected):
    def read(directory):
        paths=list(directory.rglob('*'));require(all(not p.is_symlink() for p in paths),'symlink in extraction')
        require(all(p.suffix=='.ec' for p in paths if p.is_file()),'unexpected extraction file')
        return {str(p.relative_to(directory)):p.read_bytes() for p in paths if p.is_file()}
    before,after=read(stored),read(fresh)
    require(set(before)==set(after)==expected,'whole extraction inventory drift');require(before==after,'raw extraction byte drift')
    return {name:sha(data) for name,data in before.items()}


def check():reference.guard.check_reference();check_source()


if __name__=='__main__':
    check();print('PASS: exact complete Decaps wiring, source dependencies and official fixture')
