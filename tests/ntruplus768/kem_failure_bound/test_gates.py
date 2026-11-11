#!/usr/bin/env python3
"""Adversarial mutations of events, privacy, RNG order and proof trust gates."""
import json
import check_kem_failure_bound as policy
from model_contract import MODEL
from verify_kem_failure_bound import check_negative_diagnostic


def main():
    controls = []
    policy.check_structure()
    def rejects(label, action):
        try:
            action()
        except (ValueError, AssertionError, IndexError):
            controls.append({'label': label, 'result': 'EXPECTED_REJECTION'})
            return
        raise AssertionError('accepted negative control: ' + label)

    def mutation(label, relative, old, new):
        text = (policy.ROOT / relative).read_text()
        policy.require(old in text, 'absent mutation target: ' + label)
        altered = text.replace(old, new, 1)
        policy.require(altered != text, 'ineffective mutation: ' + label)
        rejects(label, lambda: policy.check_structure({relative: altered}))

    for label, old, new in (
        ('encap-status-omitted', 'er.`3 <> W32.zero \\/ ', ''),
        ('decap-status-omitted', 'dr.`2 <> W32.zero \\/ ', ''),
        ('key-mismatch-omitted', ' \\/ er.`2 <> dr.`1', ''),
        ('failure-conjunction', 'er.`3 <> W32.zero \\/ ', 'er.`3 <> W32.zero /\\ '),
        ('bad-event-negation', '!keygen_coins_no_wrap w coins', 'keygen_coins_no_wrap w coins'),
        ('bad-event-fixed-coins', '!keygen_coins_no_wrap w coins', '!keygen_coins_no_wrap w witness'),
        ('public-fixed-coins-api', 'er <@ EncapRandom(F,G,H,Q).run(pk,witness);', 'er <@ EncapDerand(F,G,H).run(pk,witness,witness);'),
        ('public-secret-witness', 'return kem_failure er dr;', 'return(kem_failure er dr,sk);'),
        ('private-extra-output', 'return(kem_failure er dr,!keygen_coins_no_wrap w coins);', 'return(kem_failure er dr,!keygen_coins_no_wrap w coins,w);'),
        ('rng-snapshot-order', 'coins <@ Q.sample();\n    original <- coins;', 'original <- coins;\n    coins <@ Q.sample();'),
        ('extra-rng-draw', 'coins <@ Q.sample();', 'coins <@ Q.sample(); coins <@ Q.sample();'),
        ('rng-fixed-witness', 'coins <@ Q.sample();', 'coins <- witness;'),
        ('encap-module-substitution', 'EncapDerand(F,G,H).run(pk,coins,workspace)', 'EncapRandom(F,G,H,Q).run(pk,workspace)'),
        ('decap-module-substitution', 'CompleteDecaps(G,H).run(er.`1,sk,witness)', 'CompleteDecaps(G,H).run(er.`1,witness,witness)'),
        ('public-keygen-substitution', '(pk,sk) <@ Keygen(R,E,F).run();', '(pk,sk) <@ KeygenInstrumented(R,E,F).run(witness);'),
        ('instrumentation-global', 'module EncapRandomInstrumented(F:EncapSHAKEF,G:MessageSHAKE,H:CompleteSHAKEH,Q:EncapRNG) = {',
         'module EncapRandomInstrumented(F:EncapSHAKEF,G:MessageSHAKE,H:CompleteSHAKEH,Q:EncapRNG) = { var leaked:W8.t Array96.t;'),
        ('shared-seed-port-width', 'proc seed32() : W8.t Array32.t', 'proc seed32() : W8.t Array96.t'),
        ('shared-coins-port-width', 'proc coins96() : W8.t Array96.t', 'proc coins96() : W8.t Array32.t'),
        ('shared-seed-port-draw', 'x <@ B.seed32();', 'x <@ B.coins96();'),
        ('shared-coins-port-draw', 'x <@ B.coins96();', 'x <@ B.seed32();'),
        ('shared-coins-port-fixed', 'x <@ B.coins96();', 'x <- witness;'),
    ):
        mutation(label, MODEL, old, new)
    mutation('old-public-projection', policy.KEYGEN_MODEL, 'return(w.`kg_pk,w.`kg_sk);', 'return(w,w.`kg_sk);')
    mutation('old-rng-before-body', policy.RNG_MODEL, 'coins <@ R.sample();', 'coins <- witness;')
    mutation('native-rng-width', policy.ENCAP_C, 'uint8_t coins[96] = {0};', 'uint8_t coins[32] = {0};')
    mutation('native-rng-call', policy.ENCAP_C, 'randombytes(coins, sizeof coins);', 'randombytes(coins, 32);')
    for label, text in (
        ('admitted-proof', 'lemma forged : false. proof. admit. qed.'),
        ('axiom', 'axiom forged : false.'),
        ('disabled-checker', 'pragma -check.'),
        ('abstract-op', 'op arbitrary_bad : bool.'),
        ('unclosed-comment', '(* mask the final proof'),
    ):
        rejects(label, lambda text=text: policy.check_proof_text(text))
    own = '/isolated/0/Main.ec'
    valid = '[critical] [' + own + ': line 80] cannot process [axiom] inside a proof script'
    check_negative_diagnostic(valid, own)
    rejects('eof-wrong-main', lambda: check_negative_diagnostic(valid, '/isolated/1/Other.ec'))
    rejects('eof-import-contamination', lambda: check_negative_diagnostic(
        '[critical] [' + own + ': line 4] In external theory Broken: cannot process [axiom] inside a proof script', own))
    rejects('eof-unrelated-error', lambda: check_negative_diagnostic(
        '[critical] [' + own + ': line 80] unknown type', own))
    policy.require(len(controls) == 33, 'mutation inventory drift')
    print(json.dumps({'status': 'PASS', 'count': len(controls), 'controls': controls}))


if __name__ == '__main__':
    main()
