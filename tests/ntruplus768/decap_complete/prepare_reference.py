#!/usr/bin/env python3
"""Namespace and instrument the immutable official API; no body splice."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
TEST=Path(__file__).resolve().parent
ROOT=TEST.parents[2]
GUARD=TEST.parent/'decap_guard'
spec=importlib.util.spec_from_file_location('guard_reference',GUARD/'prepare_reference.py')
guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
require,sha,REFERENCE=guard.require,guard.sha,GUARD/'reference'


def generate(output):
    guard.check_reference();original=(REFERENCE/'kem.c').read_bytes()
    preamble='#include "trace.h"\n'
    preamble+=''.join('#define '+dep+' trace_'+dep+'\n' for dep in guard.DEPENDENCIES)
    preamble+=''.join('#define crypto_kem_'+suffix+' official_'+local+'\n'
                     for suffix,local in [('keypair','keypair'),('enc','enc'),('dec','dec')])
    output.mkdir(parents=True,exist_ok=True)
    path=output/'official_kem.c';path.write_bytes(preamble.encode()+original)
    report={'official_kem.c':{'sha256':sha(path.read_bytes()),'body_sha256':sha(original),
              'preamble_bytes':len(preamble.encode()),'body_bytes':len(original)},
            'contract':'No official body splice. Test preamble namespaces the three official APIs and traces dependency calls. New Decaps is compiled separately from its production C source; compile macros redirect calls through wrappers which call the real primitives.'}
    (output/'reference.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',required=True,type=Path)
    generate(parser.parse_args().output)
