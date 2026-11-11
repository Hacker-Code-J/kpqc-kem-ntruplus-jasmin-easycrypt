#!/usr/bin/env python3
"""Negative controls for exact wiring, extraction, reference and proof policy."""
from pathlib import Path
import tempfile
import check_decap_message as policy
import prepare_reference as reference
cases=0

def rejected(action):
    global cases
    try: action()
    except (ValueError,AssertionError): cases+=1; return
    raise AssertionError('negative control was accepted')

source=policy.SOURCE.read_bytes();csource=policy.C_SOURCE.read_bytes()
for old,new in [(b'input[0] = 1;',b'input[0] = 0;'),(b'input[i + 1] = b;',b'input[i] = b;'),
                (b'secret',b'public')]:
    policy.require(old in source,'mutation target absent');rejected(lambda old=old,new=new:policy.check_source(source.replace(old,new,1)))
for old,new in [(b'uint8_t input[1153]',b'uint8_t input[1152]'),(b'uint8_t pad[192]',b'uint8_t pad[96]'),
                (b'secure_clear(input, sizeof input);',b''),(b'return fail;',b'return 0;')]:
    policy.require(old in csource,'C mutation target absent');rejected(lambda old=old,new=new:policy.check_source(cdata=csource.replace(old,new,1)))
original=(reference.REFERENCE/'kem.c').read_bytes()
rejected(lambda:reference.splice(original+b'\n'))
for previous in (False,True):
    mixed=reference.splice(original,previous)
    rejected(lambda mixed=mixed,previous=previous:reference.check_mixed(original,mixed+b'\n',previous))
for text in ('lemma bad : true. proof. admit. qed.','axiom bad : false.'):
    rejected(lambda text=text:policy.check_proof_text(text))
with tempfile.TemporaryDirectory() as temp:
    base=Path(temp);a,b=base/'stored',base/'fresh';a.mkdir();b.mkdir()
    (a/'A.ec').write_text('a');(b/'A.ec').write_text('a')
    policy.check_extraction(a,b,{'A.ec'})
    (b/'A.ec').write_text('b');rejected(lambda:policy.check_extraction(a,b,{'A.ec'}))
    (b/'A.ec').write_text('a');(b/'B.ec').write_text('b');rejected(lambda:policy.check_extraction(a,b,{'A.ec'}))
    (b/'B.ec').unlink();(b/'x.pyc').write_text('x');rejected(lambda:policy.check_extraction(a,b,{'A.ec'}))
policy.require(cases==15,'negative control inventory')
print('PASS: 15 expected gate rejections')
