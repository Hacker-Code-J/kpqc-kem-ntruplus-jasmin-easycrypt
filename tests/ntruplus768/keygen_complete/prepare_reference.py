#!/usr/bin/env python3
"""Trace and namespace a byte-identical pinned official KeyGen body."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
TEST=Path(__file__).resolve().parent;ROOT=TEST.parents[2];GUARD=TEST.parent/'decap_guard'
spec=importlib.util.spec_from_file_location('guard_reference',GUARD/'prepare_reference.py');guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
require,sha,REFERENCE=guard.require,guard.sha,GUARD/'reference'
DEPENDENCIES=('randombytes','shake256','poly_cbd1','poly_triple','poly_ntt','poly_baseinv','poly_basemul','poly_tobytes','hash_f')
def generate(output):
 guard.check_reference();original=(REFERENCE/'kem.c').read_bytes()
 preamble='#include "trace.h"\n'+''.join('#define '+name+' k_'+name+'\n' for name in DEPENDENCIES)
 preamble+=''.join('#define crypto_kem_'+name+' official_'+name+'\n' for name in ('keypair','enc','dec'))
 output.mkdir(parents=True,exist_ok=True);path=output/'official_kem.c';path.write_bytes(preamble.encode()+original)
 report={'official_kem.c':{'sha256':sha(path.read_bytes()),'body_sha256':sha(original),'preamble_bytes':len(preamble.encode()),'body_bytes':len(original)},'contract':'Official kem.c body byte-identical, trace and API namespace macros only. New KeyGen compiles from independent production C source.'}
 (output/'reference.json').write_text(json.dumps(report,indent=2)+'\n');return report
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True,type=Path);generate(p.parse_args().output)
