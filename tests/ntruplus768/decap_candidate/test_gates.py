#!/usr/bin/env python3
"""Bounded negative controls for candidate source and exact reference seams."""
import json
from pathlib import Path
import tempfile
import sys
sys.dont_write_bytecode = True
import check_decap_candidate as policy
import prepare_reference as reference


def reject(label, function):
    try:
        function()
    except ValueError:
        print('EXPECTED_REJECTION', label)
        return
    raise AssertionError('gate accepted mutation: ' + label)


def main():
    policy.check()
    source = policy.SOURCE.read_bytes()
    reject('source-byte-drift', lambda: policy.check_source(source + b'\n'))
    original = (reference.REFERENCE / 'kem.c').read_bytes()
    reject('official-source-drift', lambda: reference.splice(original + b'\n'))
    for both in (False, True):
        mixed = reference.splice(original, both)
        reject('post-splice-arithmetic-drift-' + str(both), lambda: reference.check_mixed(
            original, mixed.replace(b'fail |=', b'fail ='), both))
    reject('proof-admit', lambda: policy.check_proof_text('lemma bad : true. proof. admit. qed.'))
    reject('proof-axiom', lambda: policy.check_proof_text('axiom bad : false.'))
    stored = policy.ROOT / 'ntruplus/proof/768/ref/decap_candidate/extracted'
    with tempfile.TemporaryDirectory(prefix='candidate-gates-') as raw:
        copied = Path(raw)
        for path in stored.glob('*.ec'):
            (copied / path.name).write_bytes(path.read_bytes())
        policy.check_extraction(stored, copied)
        main = copied / 'NTRUPlus768DecapCandidate.ec'
        main.write_bytes(main.read_bytes() + b'\n')
        reject('raw-extraction-drift', lambda: policy.check_extraction(stored, copied))
        main.write_bytes((stored / main.name).read_bytes())
        (copied / 'unexpected.ec').write_text('')
        reject('extra-extraction-file', lambda: policy.check_extraction(stored, copied))
    print(json.dumps({'status': 'PASS', 'expected_rejections': 8}))


if __name__ == '__main__':
    main()
