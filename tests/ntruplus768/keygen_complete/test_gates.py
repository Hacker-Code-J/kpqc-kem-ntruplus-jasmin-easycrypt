#!/usr/bin/env python3
"""Negative controls for KeyGen source, proof syntax and fresh extraction gates."""
from pathlib import Path
import tempfile
import check_keygen_complete as policy
cases=0
def rejected(action):
 global cases
 try:action()
 except (ValueError,AssertionError):cases+=1;return
 raise AssertionError('negative control accepted')
source=policy.C_SOURCE.read_bytes()
for old,new in [(b'w = {0};',b'w = {1};'),(b'randombytes(w.seed, sizeof w.seed);',b'randombytes(w.seed, 31);'),(b'w.seed, sizeof w.seed);',b'w.seed, 31);'),(b'while (status != 0)',b'while (status == 0)'),(b'keygen_shape_f(w.pre)',b'keygen_shape_g(w.pre)'),(b'poly_baseinv(w.finv, w.f)',b'poly_baseinv(w.f, w.finv)'),(b'poly_baseinv(w.ginv, w.g)',b'poly_baseinv(w.g, w.ginv)'),(b'poly_basemul(w.hinv, w.f, w.ginv)',b'poly_basemul(w.hinv, w.g, w.ginv)'),(b'sk, w.fbytes, w.hinvbytes, w.hash_f',b'sk, w.hinvbytes, w.fbytes, w.hash_f'),(b'keygen_clear((uint8_t *)&w);',b'keygen_clear((uint8_t *)&w + 1);'),(b'uint8_t reserved[1];',b'uint8_t reserved[2];')]:
 policy.require(old in source,'mutation target absent');rejected(lambda old=old,new=new:policy.check_source(source.replace(old,new,1)))
for text in ('lemma bad : true. proof. admit. qed.','axiom bad : false.'):rejected(lambda text=text:policy.check_proof_text(text))
with tempfile.TemporaryDirectory() as tmp:
 a,b=Path(tmp)/'a',Path(tmp)/'b';a.mkdir();b.mkdir();(a/'A.ec').write_text('a');(b/'A.ec').write_text('a');policy.check_extraction(a,b,{'A.ec'})
 (b/'A.ec').write_text('b');rejected(lambda:policy.check_extraction(a,b,{'A.ec'}));(b/'A.ec').write_text('a');(b/'B.ec').write_text('b');rejected(lambda:policy.check_extraction(a,b,{'A.ec'}));(b/'B.ec').unlink();(b/'x.pyc').write_text('x');rejected(lambda:policy.check_extraction(a,b,{'A.ec'}))
policy.require(cases==16,'mutation inventory');print('PASS: 16 expected source/proof/extraction gate rejections')
