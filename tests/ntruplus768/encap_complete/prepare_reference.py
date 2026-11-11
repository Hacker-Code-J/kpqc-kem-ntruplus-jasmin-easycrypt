#!/usr/bin/env python3
"""Expose official static deterministic Encaps without changing its body."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
TEST=Path(__file__).resolve().parent;ROOT=TEST.parents[2];GUARD=TEST.parent/'decap_guard'
spec=importlib.util.spec_from_file_location('guard_reference',GUARD/'prepare_reference.py');guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
require,sha,REFERENCE=guard.require,guard.sha,GUARD/'reference'
DEPENDENCIES=('randombytes','poly_frombytes','hash_f','hash_g','hash_h','poly_cbd1','poly_ntt','poly_tobytes','poly_sotp_encode','poly_basemul_add')
WRAPPER=b'''\nint official_derand(uint8_t *ct, uint8_t *ss, const uint8_t *pk, const uint8_t *coins)
{
    return crypto_kem_enc_derand(ct, ss, pk, coins);
}
'''

def generate(output):
    guard.check_reference();original=(REFERENCE/'kem.c').read_bytes()
    require(original.count(b'static inline int crypto_kem_enc_derand(')==1,'official deterministic entry drift')
    preamble='#include "trace.h"\n'+''.join('#define '+name+' e_'+name+'\n' for name in DEPENDENCIES)
    preamble+=''.join('#define crypto_kem_'+s+' official_'+n+'\n' for s,n in [('keypair','keypair'),('enc','enc'),('dec','dec')])
    output.mkdir(parents=True,exist_ok=True);path=output/'official_kem.c';path.write_bytes(preamble.encode()+original+WRAPPER)
    report={'official_kem.c':{'sha256':sha(path.read_bytes()),'body_sha256':sha(original),'preamble_bytes':len(preamble.encode()),'body_bytes':len(original),'wrapper_sha256':sha(WRAPPER)},
      'contract':'Official kem.c body remains byte-identical. A common preamble traces/namespaces APIs; a fixed appended wrapper calls the actual static inline deterministic function in the same translation unit. New APIs compile from independent production C source.'}
    (output/'reference.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True,type=Path);generate(p.parse_args().output)
