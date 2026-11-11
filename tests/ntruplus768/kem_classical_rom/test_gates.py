#!/usr/bin/env python3
"""Adversarial structure/trust/diagnostic controls; no native replay claims."""
import json
import check_kem_classical_rom as policy
from model_contract import DOMAINS, LAWS, ORACLES, OBSERVER, COLLISION, KEYGENOBSERVER, KEYGEN, ENCAP, DECAP, GAME, HASH, PAYLOADSPEC, PAYLOADALGEBRA, SOTPMASK, SOTPDEF, SAMPLING, FAILURE
from verify_kem_classical_rom import check_negative_diagnostic, check_sentinel
import eof_sentinels as eof

MUTATIONS = (
    ('F-prefix', DOMAINS, 'then W8.zero else pk.[i-1]', 'then W8.one else pk.[i-1]'),
    ('G-prefix', DOMAINS, 'then W8.one else serialized.[i-1]', 'then W8.zero else serialized.[i-1]'),
    ('H-prefix', DOMAINS, 'then W8.of_int 2 else', 'then W8.zero else'),
    ('H-coins-width', DOMAINS, 'if i <= 96 then coins.[i-1]', 'if i <= 32 then coins.[i-1]'),
    ('H-suffix-offset', DOMAINS, 'else pkhash.[i-97]', 'else pkhash.[i-96]'),
    ('E-query-length', DOMAINS, 'with q = E seed => Array32.to_list seed', 'with q = E seed => Array96.to_list seed'),
    ('F-query-length', DOMAINS, 'with q = F pk => Array1153.to_list (encode_f pk)', 'with q = F pk => Array1152.to_list pk'),
    ('G-query-F-alias', DOMAINS, 'with q = G serialized => Array1153.to_list (encode_g serialized)', 'with q = G serialized => Array1153.to_list (encode_f serialized)'),
    ('H-query-ignores-coins', DOMAINS, 'encode_h payload.`1 payload.`2', 'encode_h witness payload.`2'),
    ('H-query-ignores-suffix', DOMAINS, 'encode_h payload.`1 payload.`2', 'encode_h payload.`1 witness'),
    ('H-key-width', DOMAINS, 'H of (W8.t Array96.t * W8.t Array32.t)', 'H of W8.t Array96.t'),
    ('domain-injection-omitted', DOMAINS, 'lemma raw_query_inj : injective raw_query', 'lemma raw_query_inj : true'),
    ('nonuniform-law', LAWS, 'dlist W8.dword 32', 'dlist (dunit W8.zero) 32'),
    ('uniform32-wrong-array', LAWS, 'op uniform32 = dmap (dlist W8.dword 32) (Array32.of_list W8.zero)', 'op uniform32 = dmap (dlist W8.dword 32) (Array192.of_list W8.zero)'),
    ('uniform32-wrong-point', LAWS, 'mu1 uniform32 x = (1%r / 256%r)^32', 'mu1 uniform32 x = (1%r / 256%r)^31'),
    ('cache-overwrites-repeat', ORACLES, 'if (input \\notin m) {', 'if (true) {'),
    ('cache-samples-repeat', ORACLES, 'var r; if (input \\notin m) {', 'var r; r <$ uniform192; if (input \\notin m) {'),
    ('cache-returns-fresh-value', ORACLES, 'return oget m.[input];', 'r <$ uniform192; return r;'),
    ('cache-omits-store', ORACLES, 'm.[input] <- r;', ''),
    ('cache-RNG-interference', ORACLES, 'r <$ uniform192;', 'r <@ SeedObserver.seed32();'),
    ('cache-table-interference', ORACLES, 'm.[input] <- r;', 'ROF.m <- empty; m.[input] <- r;'),
    ('cache-extra-RNG-module', ORACLES, 'module ROE : ROEPort', 'module RNG = { var state:int; }. module ROE : ROEPort'),
    ('fresh-query-condition-omitted', ORACLES, 'ROE.m=m0 /\\ input=x0 /\\ x0 \\notin m0 ==> res=y0', 'ROE.m=m0 /\\ input=x0 ==> res=y0'),
    ('cached-query-output-changed', ORACLES, 'm0.[x0]=Some y0 ==> res=y0 /\\ ROE.m=m0', 'm0.[x0]=Some y0 ==> res=witness /\\ ROE.m=m0'),
    ('cached-query-store-forgotten', ORACLES, 'm0.[x0]=Some y0 ==> res=y0 /\\ ROE.m=m0', 'm0.[x0]=Some y0 ==> res=y0'),
    ('F-port-alias-G', ORACLES, 'ROF.get(peel1153 input)', 'ROG.get(peel1153 input)'),
    ('H-port-ignores-suffix', ORACLES, 'ROH.get(peel_h input)', 'ROH.get((peel_h input).`1,witness)'),
    ('RO-table-reset-on-query', ORACLES, 'var r; r <@ ROE.get(seed); return r;', 'var r; ROE.init(); r <@ ROE.get(seed); return r;'),
    ('RO-initial-table-omitted', ORACLES, 'ROE.init(); ROF.init(); ROG.init(); ROH.init();', 'ROE.init(); ROF.init(); ROG.init();'),
    ('actual-KeyGen-substituted-reference', KEYGEN, 'hoare[Keygen(R,E,SHAKEFROM).run:', 'hoare[KeygenSpec(R,E,SHAKEFROM).run:'),
    ('actual-KeyGen-private-witness-omitted', KEYGEN, 'w.`kg_fbuf w.`kg_gbuf', 'witness witness'),
    ('actual-KeyGen-G-attempts-omitted', KEYGEN, 'call(keygen_retry_g_accepted R E);', ''),
    ('actual-KeyGen-F-attempts-omitted', KEYGEN, 'call(keygen_retry_f_accepted R E)', 'call(keygen_retry_g_accepted R E)'),
    ('actual-KeyGen-cached-F-omitted', KEYGEN, 'fm.[w.`kg_pk]=Some (complete_sk_suffix w.`kg_sk)', 'true'),
    ('actual-Encap-substituted-reference', ENCAP, 'hoare[EncapBody(SHAKEGROM).run:', 'hoare[EncapBodySpec(SHAKEGROM).run:'),
    ('actual-Encap-randomized-substituted-derand', ENCAP, 'hoare[EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,Q).run:', 'hoare[EncapDerand(SHAKEFROM,SHAKEGROM,SHAKEHROM).run:'),
    ('actual-Encap-fixed-SHAKE-contract', ENCAP, 'ecall(poly_sotp_encode_functional witness coins0 pad)', 'ecall(message_shake_spec witness coins0 pad)'),
    ('actual-Encap-RNG-F-interference', ENCAP, '(Q<:EncapRNG {-ROF,-ROG,-ROH})', '(Q<:EncapRNG {-ROG,-ROH})'),
    ('actual-Encap-RNG-G-interference', ENCAP, '(Q<:EncapRNG {-ROF,-ROG,-ROH})', '(Q<:EncapRNG {-ROF,-ROH})'),
    ('actual-Encap-RNG-H-interference', ENCAP, '(Q<:EncapRNG {-ROF,-ROG,-ROH})', '(Q<:EncapRNG {-ROF,-ROG})'),
    ('realized-H-value-substituted', ENCAP, 'let hout=oget hm.[(coins,suffix)]', 'let hout=complete_shake_h_spec witness'),
    ('realized-G-pad-substituted', ENCAP, 'let pad=oget gm.[payload_serialized hout]', 'let pad=message_shake_spec witness'),
    ('realized-H-key-coins-omitted', ENCAP, 'let hout=oget hm.[(coins,suffix)]', 'let hout=oget hm.[(witness,suffix)]'),
    ('realized-H-key-suffix-omitted', ENCAP, 'let hout=oget hm.[(coins,suffix)]', 'let hout=oget hm.[(coins,witness)]'),
    ('old-F-preparation-domain', HASH, 'encap_hash_f_input_spec pk=encode_f pk', 'encap_hash_f_input_spec pk=encode_g pk'),
    ('old-G-preparation-domain', HASH, 'message_hash_input bs=encode_g bs', 'message_hash_input bs=encode_f bs'),
    ('old-H-preparation-suffix', HASH, 'hash_h_prepare_spec coins suffix=encode_h coins suffix', 'hash_h_prepare_spec coins suffix=encode_h coins witness'),
    ('actual-Decaps-substituted-reference', DECAP, 'hoare[CompleteDecaps(SHAKEGROM,SHAKEHROM).run:', 'hoare[CompleteDecapsSpec(SHAKEGROM,SHAKEHROM).run:'),
    ('actual-Decaps-fixed-G-contract', DECAP, 'call(rom_g_cached', 'call(message_shake_spec'),
    ('actual-Decaps-fixed-H-contract', DECAP, 'call(rom_h_cached coins0 suffix0 hout0 hm0 hc)', 'call(complete_shake_h_spec witness)'),
    ('actual-Decaps-no-wrap-omitted', DECAP, 'sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf (payload_r hout0) (payload_m coins0 pad0)', 'true'),
    ('actual-Decaps-cached-H-key', DECAP, 'hm0.[(coins0,complete_sk_suffix w.`kg_sk)]=Some hout0', 'hm0.[(coins0,witness)]=Some hout0'),
    ('actual-game-public-substitution', GAME, 'failed <@ KEMCorrectness(KeygenRNGPort(B),ExpandROM,SHAKEFROM,SHAKEGROM,SHAKEHROM,EncapRNGPort(B)).run();', 'failed <@ MathematicalCorrectness.run();'),
    ('actual-game-private-keygen-substitution', GAME, '(w,cleared) <@ KeygenInstrumented(KeygenRNGPort(B),ExpandROM,SHAKEFROM).run(witness);', '(w,cleared) <@ KeygenSpec.run(witness);'),
    ('actual-game-private-encap-fixed-coins', GAME, '(er,coins) <@ EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,EncapRNGPort(B)).run(w.`kg_pk,witness);', '(er,coins) <@ EncapDerand(SHAKEFROM,SHAKEGROM,SHAKEHROM).run(w.`kg_pk,witness,witness);'),
    ('actual-game-private-decaps-substitution', GAME, 'dr <@ CompleteDecaps(SHAKEGROM,SHAKEHROM).run(er.`1,w.`kg_sk,witness);', 'dr <@ CompleteDecapsSpec(SHAKEGROM,SHAKEHROM).run(er.`1,w.`kg_sk,witness);'),
    ('actual-game-Bad-negation', GAME, 'bad <- !sampled_m1_no_wrap', 'bad <- sampled_m1_no_wrap'),
    ('actual-game-Bad-fbuf-witness', GAME, 'bad <- !sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf', 'bad <- !sampled_m1_no_wrap witness w.`kg_gbuf'),
    ('actual-game-Bad-fixed-coins', GAME, '(payload_r hout) (payload_m coins pad)', '(payload_r hout) (payload_m witness pad)'),
    ('actual-game-Bad-fixed-H', GAME, 'hout <- oget ROH.m.[(coins,suffix)]', 'hout <- complete_shake_h_spec witness'),
    ('actual-game-Bad-fixed-G', GAME, 'pad <- oget ROG.m.[payload_serialized hout]', 'pad <- message_shake_spec witness'),
    ('actual-game-private-secret-leak', GAME, 'return (kem_failure er dr,bad)', 'return (kem_failure er dr,bad,w)'),
    ('actual-game-extra-query', GAME, 'suffix <- complete_sk_suffix w.`kg_sk;', 'suffix <- complete_sk_suffix w.`kg_sk; hout <@ ROH.get((coins,suffix));'),
    ('actual-game-RNG-E-interference', GAME, 'B<:KEMRNG {-ROE,-ROF,-ROG,-ROH}', 'B<:KEMRNG {-ROF,-ROG,-ROH}'),
    ('actual-game-RNG-F-interference', GAME, 'B<:KEMRNG {-ROE,-ROF,-ROG,-ROH}', 'B<:KEMRNG {-ROE,-ROG,-ROH}'),
    ('actual-game-RNG-G-interference', GAME, 'B<:KEMRNG {-ROE,-ROF,-ROG,-ROH}', 'B<:KEMRNG {-ROE,-ROF,-ROH}'),
    ('actual-game-RNG-H-interference', GAME, 'B<:KEMRNG {-ROE,-ROF,-ROG,-ROH}', 'B<:KEMRNG {-ROE,-ROF,-ROG}'),
    ('failure-encap-status-omitted', FAILURE, 'er.`3 <> W32.zero \\/', ''),
    ('failure-decap-status-omitted', FAILURE, 'dr.`2 <> W32.zero \\/', ''),
    ('failure-key-mismatch-omitted', FAILURE, '\\/ er.`2 <> dr.`1', ''),
    ('SOTP-law-coin-width', SOTPMASK, 'lemma sotp_encode_uniform_law (coins : W8.t Array96.t)', 'lemma sotp_encode_uniform_law (coins : W8.t Array32.t)'),
    ('SOTP-law-pad-width', SOTPMASK, 'dmap uniform192 (poly_sotp_encode_spec coins) = cbd1_uniform', 'dmap uniform96 (poly_sotp_encode_spec coins) = cbd1_uniform'),
    ('SOTP-law-fixed-SHAKE', SOTPMASK, 'op cbd1_uniform = dmap uniform192 poly_cbd1_spec', 'op cbd1_uniform = dmap (dunit (message_shake_spec witness)) poly_cbd1_spec'),
    ('SOTP-law-CBD-target', SOTPMASK, 'op cbd1_uniform = dmap uniform192 poly_cbd1_spec', 'op cbd1_uniform = dmap uniform192 witness'),
    ('SOTP-law-mask-involution', SOTPMASK, '(byte +^ mask) +^ mask = byte', '(byte +^ mask) +^ mask = mask'),
    ('SOTP-actual-head-width', SOTPDEF, 'if 0 <= k < 96 then', 'if 0 <= k < 192 then'),
    ('SOTP-actual-mask-tail', SOTPDEF, 'else pad.[k]', 'else pad.[k] +^ msg.[k]'),
    ('SOTP-actual-mask-XOR', SOTPDEF, 'pad.[k] +^ msg.[k]', 'pad.[k] + msg.[k]'),
    ('sampling-actual-encoder-substituted-spec', SAMPLING, 'rp <@ NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(rp, coins, pad);', 'rp <- poly_sotp_encode_spec coins pad;'),
    ('sampling-fresh-G-key-omitted', SAMPLING, 'serialized0 \\notin ROG.m{m} =>', ''),
    ('sampling-fresh-G-substituted-F', SAMPLING, 'pad <@ SHAKEGROM.shake(encode_g serialized);', 'pad <@ SHAKEFROM.shake(encode_f serialized);'),
    ('sampling-uniform-pad-truncated', SAMPLING, 'pad <$ uniform192;', 'pad <$ uniform96;'),
    ('observer-stops-RNG', OBSERVER, 'x <$ law; if (size prefix < q)', 'if (size prefix < q) { x <$ law; } if (size prefix < q)'),
    ('observer-redraws', OBSERVER, 'x <$ law;', 'x <$ law; x <$ law;'),
    ('initial-E-queries-omitted', OBSERVER, 'known <- undup prior;', 'known <- [];'),
    ('known-mark-omitted', OBSERVER, 'known <- x::known;', ''),
    ('external-E-mark-lost', OBSERVER, 'if (!(x \\in draws) /\\ !(x \\in known))', 'if (x \\in draws /\\ !(x \\in known))'),
    ('known-query-dedup-omitted', OBSERVER, 'if (!(x \\in draws) /\\ !(x \\in known))', 'if (!(x \\in draws))'),
    ('prefix-boundary-off-by-one', OBSERVER, 'if (size prefix < q)', 'if (size prefix <= q)'),
    ('query-budget-omitted', OBSERVER, 'size known <= a /\\', 'true /\\'),
    ('known-seed-collision-omitted', OBSERVER, 'x \\in known \\/ x \\in prefix', 'false \\/ x \\in prefix'),
    ('draw-seed-collision-omitted', OBSERVER, 'x \\in known \\/ x \\in prefix', 'x \\in known \\/ false'),
    ('full-event-fixed', OBSERVER, 'fullbad <- fullbad \\/ (x \\in known \\/ x \\in draws);', 'fullbad <- false;'),
    ('draw-tail-omitted', OBSERVER, 'q < size ds \\/ a < size ks', 'false \\/ a < size ks'),
    ('query-tail-omitted', OBSERVER, 'q < size ds \\/ a < size ks', 'q < size ds \\/ false'),
    ('collision-bound-wrong-triangle', OBSERVER, '(q0*(q0-1))%r/2%r*p', '(q0*(q0-2))%r/2%r*p'),
    ('point-bound-omitted', OBSERVER, '(forall x, mu1 d x <= p) => Pr[SeedExperiment(A).run(d,q0,a0,prior)', 'Pr[SeedExperiment(A).run(d,q0,a0,prior)'),
    ('unrestricted-tail-omitted', OBSERVER, '(ab*qb)%r*p + (qb*(qb-1))%r/2%r*p + Pr[SeedExperiment(A).run(d,qb,ab,prior)', '(ab*qb)%r*p + (qb*(qb-1))%r/2%r*p'),
    ('uniform-seed-point-wrong-width', COLLISION, 'op seed_probability = (1%r / 256%r)^32', 'op seed_probability = (1%r / 256%r)^31'),
    ('uniform-collision-tail-omitted', COLLISION, '(ab*qb)%r/(2%r^256) + (qb*(qb-1))%r/(2%r*(2%r^256)) + Pr[SeedExperiment(A).run(uniform32,qb,ab,prior)', '(ab*qb)%r/(2%r^256) + (qb*(qb-1))%r/(2%r*(2%r^256))'),
    ('uniform-collision-nonuniform-seeds', COLLISION, 'Pr[SeedExperiment(A).run(uniform32,qb,ab,prior) @ &m : SeedObserver.fullbad]', 'Pr[SeedExperiment(A).run(d,qb,ab,prior) @ &m : SeedObserver.fullbad]'),
    ('observer-actual-KeyGen-replaced', KEYGENOBSERVER, 'result <@ Keygen(ObserverSeedPort(O),ObservedExpand(O),SHAKEFROM).run();', 'result <@ KeygenSpec.run();'),
    ('observer-drops-initial-cache', KEYGENOBSERVER, 'SeedObserver.init(uniform32,q0,a0,elems(fdom ROE.m));', 'SeedObserver.init(uniform32,q0,a0,[]);'),
    ('observer-nonuniform-seed-law', KEYGENOBSERVER, 'SeedObserver.init(uniform32,q0,a0,elems(fdom ROE.m));', 'SeedObserver.init(dunit witness,q0,a0,elems(fdom ROE.m));'),
    ('observer-mark-after-E', KEYGENOBSERVER, 'O.mark(seed); y <@ ROE.get(seed);', 'y <@ ROE.get(seed); O.mark(seed);'),
    ('observer-E-query-unmarked', KEYGENOBSERVER, 'O.mark(seed);', ''),
    ('observer-cache-union-draws-omitted', KEYGENOBSERVER, 'x \\in ds \\/ x \\in ks', 'false \\/ x \\in ks'),
    ('observer-cache-union-known-omitted', KEYGENOBSERVER, 'x \\in ds \\/ x \\in ks', 'x \\in ds \\/ false'),
    ('observer-projection-cached-E-state-omitted', KEYGENOBSERVER, '={q0,a0,ROE.m,ROF.m} ==> ={res,ROE.m,ROF.m}', '={q0,a0,ROE.m,ROF.m} ==> ={res,ROF.m}'),
    ('observer-projection-cached-F-state-omitted', KEYGENOBSERVER, '={q0,a0,ROE.m,ROF.m} ==> ={res,ROE.m,ROF.m}', '={q0,a0,ROE.m,ROF.m} ==> ={res,ROE.m}'),
    ('observer-context-prior-omitted', KEYGENOBSERVER, 'prior{2}=elems(fdom ROE.m{1})', 'prior{2}=[]'),
    ('observer-actual-bound-draw-tail-omitted', KEYGENOBSERVER, 'qb < size SeedObserver.draws \\/ ab < size SeedObserver.known', 'false \\/ ab < size SeedObserver.known'),
    ('observer-actual-bound-query-tail-omitted', KEYGENOBSERVER, 'qb < size SeedObserver.draws \\/ ab < size SeedObserver.known', 'qb < size SeedObserver.draws \\/ false'),
    ('observer-actual-KeyGen-capped', KEYGENOBSERVER, '(pk,sk) <@ Keygen(ObserverSeedPort(SeedObserver),ObservedExpand(SeedObserver),SHAKEFROM).run();', 'if(q0>0){(pk,sk) <@ Keygen(ObserverSeedPort(SeedObserver),ObservedExpand(SeedObserver),SHAKEFROM).run();}'),
    ('observer-erasure-mark-losslessness-omitted', KEYGENOBSERVER, 'islossless O.mark =>', ''),
    ('observer-erasure-E-interference', KEYGENOBSERVER, '(O <: SeedQueryOracle {-ROE})', '(O <: SeedQueryOracle)'),
    ('public-private-shared-RNG-state-omitted', GAME, 'res{1}=res{2}.`1 /\\ ={glob B,glob ROE,glob ROF,glob ROG,glob ROH}', 'res{1}=res{2}.`1 /\\ ={glob ROE,glob ROF,glob ROG,glob ROH}'),
    ('payload-spec-fixed-SHAKE-injected', PAYLOADSPEC, 'require import AllCore', 'op forbidden = message_shake_spec witness. require import AllCore'),
    ('payload-algebra-fixed-SHAKE-injected', PAYLOADALGEBRA, 'require import AllCore', 'op forbidden = complete_shake_h_spec witness. require import AllCore'),
    ('generic-fixed-SHAKE-call-injected', PAYLOADALGEBRA, 'require import AllCore', 'op forbidden = SHAKE256 witness 192. require import AllCore'),
    ('payload-shared-key-wrong-prefix', PAYLOADSPEC, 'Array32.init (fun i => hout.[i])', 'Array32.init (fun i => hout.[i+32])'),
    ('payload-r-fixed-uniform-bytes', PAYLOADSPEC, 'poly_cbd1_spec (complete_hash_tail hout)', 'poly_cbd1_spec witness'),
    ('payload-m-fixed-coins', PAYLOADSPEC, 'poly_sotp_encode_spec coins pad', 'poly_sotp_encode_spec witness pad'),
    ('actual-KeyGen-seed-RNG-F-interference', KEYGEN, '(R<:KeygenSeedRNG {-ROF})', '(R<:KeygenSeedRNG)'),
    ('actual-KeyGen-expand-F-interference', KEYGEN, '(E<:KeygenExpand {-ROF})', '(E<:KeygenExpand)'),
    ('sampling-coupling-good-premise-omitted', SAMPLING, '/\\ serialized0 \\notin ROG.m{1}', ''),
    ('sampling-cached-pad-law-substituted', SAMPLING, 'res = poly_sotp_encode_spec coins0 pad0 /\\ ROG.m = m0', 'res = poly_sotp_encode_spec coins0 witness /\\ ROG.m = m0'),
    ('sampling-cached-table-preservation-omitted', SAMPLING, 'res = poly_sotp_encode_spec coins0 pad0 /\\ ROG.m = m0', 'res = poly_sotp_encode_spec coins0 pad0'),
    ('observer-cache-exact-weakened-to-coverage', KEYGENOBSERVER, 'x \\in m <=> x \\in ds \\/ x \\in ks', 'x \\in m => x \\in ds \\/ x \\in ks'),
    ('observer-cache-exact-weakened-to-inclusion', KEYGENOBSERVER, 'x \\in m <=> x \\in ds \\/ x \\in ks', 'x \\in ds \\/ x \\in ks => x \\in m'),
    ('observer-pending-seed-condition-forgotten', KEYGENOBSERVER, 'x \\in m \\/ x=pending', 'true'),
    ('observer-returned-cache-exact-forgotten', KEYGENOBSERVER, 'hoare[ObservedActualKeygen.run : true ==> observer_cache_exact ROE.m SeedObserver.draws SeedObserver.known]', 'hoare[ObservedActualKeygen.run : true ==> true]'),
    ('observer-exact-f-retry-omitted', KEYGENOBSERVER, 'call observed_retry_g_cache_exact; call observed_retry_f_cache_exact;', 'call observed_retry_g_cache_exact;'),
    ('observer-exact-g-retry-omitted', KEYGENOBSERVER, 'call observed_retry_g_cache_exact; call observed_retry_f_cache_exact;', 'call observed_retry_f_cache_exact;'),
)


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

    for label, relative, old, new in MUTATIONS:
        text = policy.compact((policy.ROOT / relative).read_text())
        old, new = policy.compact(old), policy.compact(new)
        policy.require(old in text, 'absent mutation target: ' + label)
        altered = text.replace(old, new, 1)
        policy.require(altered != text, 'ineffective mutation: ' + label)
        rejects(label, lambda relative=relative, altered=altered: policy.check_structure({relative: altered}))
    for label, text in (
        ('admitted-proof', 'lemma forged : false. proof. admit. qed.'),
        ('local-axiom', 'axiom forged : false.'),
        ('disabled-checker', 'pragma -check.'),
        ('abstract-local-law', 'op arbitrary_uniform : int distr.'),
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
    for name, sentinel in eof.SENTINELS.items():
        check_sentinel(name, sentinel, eof.SEMANTIC_TARGETS[name], eof.MODULE_BINDERS[name])
    name = 'kem_rom_bridge/NTRUPlus768ROMCorrectness.ec'
    sentinel = eof.SENTINELS[name]
    def validates(altered):
        check_sentinel(name, altered, eof.SEMANTIC_TARGETS[name], eof.MODULE_BINDERS[name])
    rejects('eof-implicit-module-binder', lambda: validates(sentinel.replace('B <: KEMRNG', 'B : KEMRNG')))
    rejects('eof-wrong-semantic-target', lambda: validates(sentinel.replace('exact (rom_failure_probability', 'exact (irrelevant')))
    rejects('eof-open-sentinel', lambda: validates(sentinel.replace('qed.', '')))
    rejects('eof-constant-proposition', lambda: validates('lemma __forged (B <: KEMRNG) : true. proof. exact rom_failure_probability. qed.'))
    policy.require(len(controls) == len(MUTATIONS) + 12, 'mutation inventory drift')
    print(json.dumps({'status': 'PASS', 'declared': len(MUTATIONS) + 12,
                      'count': len(controls), 'controls': controls}))


if __name__ == '__main__':
    main()
