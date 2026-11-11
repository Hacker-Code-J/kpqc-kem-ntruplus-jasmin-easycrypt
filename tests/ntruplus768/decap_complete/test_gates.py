#!/usr/bin/env python3
"""Negative controls for key suffix, sampling offset, rejection and cleanup wiring."""
from pathlib import Path
import tempfile
import check_decap_complete as policy
import prepare_reference as reference
cases=0

def rejected(action):
    global cases
    try:action()
    except (ValueError,AssertionError):cases+=1;return
    raise AssertionError('negative control was accepted')

source=policy.C_SOURCE.read_bytes()
for old,new in [(b'w = {0};',b'w = {1};'),(b'sk + 2304',b'sk + 2305'),(b'w.hash_output + 32',b'w.hash_output + 31'),
 (b'if (fail != 0)',b'if (fail == 0)'),(b'goto cleanup;',b''),
 (b'jade_ntruplus_ntruplus768_amd64_ref_decap_clear((uint8_t *)&w);',b''),
 (b'return (int)fail;',b'return 0;'),(b'sizeof w.hash_output',b'223')]:
    policy.require(old in source,'mutation target absent');rejected(lambda old=old,new=new:policy.check_source(source.replace(old,new,1)))
for text in ('lemma bad : true. proof. admit. qed.','axiom bad : false.'):
    rejected(lambda text=text:policy.check_proof_text(text))
with tempfile.TemporaryDirectory() as temp:
    base=Path(temp);a,b=base/'stored',base/'fresh';a.mkdir();b.mkdir()
    (a/'A.ec').write_text('a');(b/'A.ec').write_text('a');policy.check_extraction(a,b,{'A.ec'})
    (b/'A.ec').write_text('b');rejected(lambda:policy.check_extraction(a,b,{'A.ec'}))
    (b/'A.ec').write_text('a');(b/'B.ec').write_text('b');rejected(lambda:policy.check_extraction(a,b,{'A.ec'}))
    (b/'B.ec').unlink();(b/'x.pyc').write_text('x');rejected(lambda:policy.check_extraction(a,b,{'A.ec'}))
policy.require(cases==13,'negative control inventory')
print('PASS: 13 expected source/extraction/proof gate rejections')
