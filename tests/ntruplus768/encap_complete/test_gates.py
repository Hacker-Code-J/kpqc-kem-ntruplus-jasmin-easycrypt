#!/usr/bin/env python3
"""Reject changes to RNG order/size, failure handling, hashes and cleanup."""
from pathlib import Path
import tempfile
import check_encap_complete as policy
cases=0
def rejected(action):
 global cases
 try:action()
 except (ValueError,AssertionError):cases+=1;return
 raise AssertionError('negative control accepted')
source=policy.C_SOURCE.read_bytes()
for old,new in [(b'w = {0};',b'w = {1};'),(b'w.hash_output + 32',b'w.hash_output + 31'),(b'if (status != 0)',b'if (status == 0)'),
 (b'goto cleanup;',b''),(b'randombytes(coins, sizeof coins);',b'randombytes(coins, 32);'),
 (b'encap_clear((uint8_t *)&w);',b'encap_clear((uint8_t *)&w + 1);'),(b'encap_clear_coins(coins);',b'encap_clear_coins(coins + 1);'),
 (b'return (int)status;',b'return 0;'),(b'poly_centered_add(w.c, w.product, w.m_ntt)',b'poly_centered_add(w.c, w.product, w.r_ntt)')]:
 policy.require(old in source,'mutation target absent');rejected(lambda old=old,new=new:policy.check_source(source.replace(old,new,1)))
for text in ('lemma bad : true. proof. admit. qed.','axiom bad : false.'):
 rejected(lambda text=text:policy.check_proof_text(text))
with tempfile.TemporaryDirectory() as tmp:
 a,b=Path(tmp)/'a',Path(tmp)/'b';a.mkdir();b.mkdir();(a/'A.ec').write_text('a');(b/'A.ec').write_text('a');policy.check_extraction(a,b,{'A.ec'})
 (b/'A.ec').write_text('b');rejected(lambda:policy.check_extraction(a,b,{'A.ec'}));(b/'A.ec').write_text('a');(b/'B.ec').write_text('b');rejected(lambda:policy.check_extraction(a,b,{'A.ec'}))
 (b/'B.ec').unlink();(b/'x.pyc').write_text('x');rejected(lambda:policy.check_extraction(a,b,{'A.ec'}))
policy.require(cases==14,'mutation inventory');print('PASS: 14 expected source/proof/extraction gate rejections')
