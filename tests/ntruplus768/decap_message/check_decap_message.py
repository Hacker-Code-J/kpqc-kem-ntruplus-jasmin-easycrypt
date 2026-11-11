#!/usr/bin/env python3
"""Pin exact sources, external C wiring, immutable fixture and fresh extraction."""
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
import prepare_reference as reference
ROOT, TEST = reference.ROOT, reference.TEST
require, sha = reference.require, reference.sha
sys.path.insert(0, str(TEST.parent / 'poly_frombytes_checked'))
from check_poly_frombytes_checked import check_proof_text
SOURCE = ROOT / 'ntruplus/jasmin/768/ref/decap_message_prepare.jazz'
SOTP = SOURCE.parent / 'poly_sotp_decode.jazz'
C_SOURCE = ROOT / 'ntruplus/c/768/ref/decap_message.c'
SLICE = 'jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare'
SOTP_SLICE = 'jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode'
EXTRACTIONS = {
 'decap_message': ('NTRUPlus768DecapMessagePrepare.ec', SOURCE, SLICE,
   {'Array1152.ec','Array1153.ec','Array768.ec','WArray1152.ec','WArray1153.ec','WArray1536.ec','NTRUPlus768DecapMessagePrepare.ec'}),
 'poly_sotp_decode_checked': ('NTRUPlus768PolySOTPDecodeChecked.ec', SOTP, SOTP_SLICE,
   {'Array96.ec','Array192.ec','Array768.ec','WArray96.ec','WArray192.ec','WArray1536.ec','NTRUPlus768PolySOTPDecodeChecked.ec'})}


def dependencies(path):
    result = {path.resolve()}
    for relative in re.findall(r'\brequire\s+"([^"\n]+)"', path.read_text()):
        target=(path.parent/relative).resolve()
        require(target.is_relative_to(SOURCE.parent.resolve()), 'Jasmin require escapes source directory')
        result |= dependencies(target)
    return result


def source_dependencies():
    paths = dependencies(SOURCE) | dependencies(SOTP) | {C_SOURCE, C_SOURCE.with_suffix('.h')}
    for name in ('decap_guard', 'decap_candidate', 'decap_r2'):
        paths |= dependencies(SOURCE.parent / (name+'.jazz'))
    return paths


def check_source(data=None, cdata=None):
    pins=json.loads((TEST/'source-pins.json').read_text())
    paths=source_dependencies()
    require(set(pins)=={str(p.relative_to(ROOT)) for p in paths}, 'source dependency inventory drift')
    for path in paths:
        value = data if data is not None and path==SOURCE else cdata if cdata is not None and path==C_SOURCE else path.read_bytes()
        require(sha(value)==pins[str(path.relative_to(ROOT))], 'source pin drift: '+str(path))
    for path in (SOURCE,SOTP):
        code=re.sub(r'//[^\n]*|/\*.*?\*/','',path.read_text(),flags=re.S)
        require('#declassify' not in code, 'message procedures may not declassify')
    c=(C_SOURCE.read_bytes() if cdata is None else cdata).decode()
    ordered=['uint8_t input[1153];','uint8_t pad[192];','jade_ntruplus_ntruplus768_amd64_ref_decap_message_prepare(\n        serialized, input, r2);',
        'shake256(pad, sizeof pad, input, sizeof input);',
        'fail = jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode(msg, m1, pad);',
        'secure_clear(input, sizeof input);','secure_clear(pad, sizeof pad);','return fail;']
    offsets=[c.index(x) for x in ordered]
    require(offsets==sorted(offsets), 'C glue ABI/call/clear order drift')
    require('secure_clear(serialized' not in c, 'serialized must remain for later verify')


def check_extraction(stored,fresh,expected):
    def read(directory):
        paths=list(directory.rglob('*'))
        require(all(not p.is_symlink() for p in paths),'symlink in extraction')
        require(all(p.suffix=='.ec' for p in paths if p.is_file()),'unexpected extraction file')
        return {str(p.relative_to(directory)):p.read_bytes() for p in paths if p.is_file()}
    before,after=read(stored),read(fresh)
    require(set(before)==set(after)==expected,'whole extraction inventory drift')
    require(before==after,'raw extraction byte drift')
    return {n:sha(v) for n,v in before.items()}


def check():
    reference.guard.check_reference(); check_source()
    original=(reference.REFERENCE/'kem.c').read_bytes()
    for previous in (False,True): reference.check_mixed(original,reference.splice(original,previous),previous)


if __name__=='__main__':
    check(); print('PASS: exact message sources, C wiring, immutable reference and splices')
