"""Explicit NTRU conditioning, whole-ring uniformity and RLWE secret targets."""
import policy

SOURCES = {
    "uniform": policy.PROOF / "NTRUPlus768OWUniform.ec",
    "codec": policy.PROOF / "NTRUPlus768OWCodec.ec",
    "games": policy.PROOF / "NTRUPlus768OWGames.ec",
    "key": policy.PROOF / "NTRUPlus768OWKeyAlgebra.ec",
    "conditioning": policy.PROOF / "NTRUPlus768OWKeyConditioning.ec",
}


def check(texts=None):
    texts = texts or {key: path.read_text() for key, path in SOURCES.items()}
    code = {key: policy.compact(texts[key]) for key in SOURCES}
    policy.shared.ordered(code["uniform"], (
        "op ow_rq_domain(p:NTRUPoly.poly) = NTRUPoly.deg p<=768.",
        "op ow_uniform_rq : NTRUPoly.poly distr =",
        "dmap (dlist CycloFq.DZmodP.dunifin 768) NTRUPoly.polyL.",
        "op ow_scale3(p:NTRUPoly.poly)",
        "NTRUPoly.PolyComRing.( * ) (NTRUPoly.polyC(lift_int 3)) p.",
        "op ow_unscale3(p:NTRUPoly.poly)",
        "NTRUPoly.PolyComRing.( * ) (NTRUPoly.polyC(CycloFq.inv(lift_int 3))) p."))
    distribution = code["uniform"].split("opow_uniform_rq", 1)[1].split("opow_scale3", 1)[0]
    for forbidden in ("dcond", "dexcepted", "pke_rq_unit", "uniform1152", "ow_unit_test"):
        policy.require(forbidden not in distribution, "uniform ring distribution altered: " + forbidden)
    policy.shared.ordered(code["codec"], (
        "op [opaque] ow_coeff_words", "Array768.init(fun i=>W16.of_int(CycloFq.asint (NTRUPoly.\"_.[_]\" p i))).",
        "op [opaque] ow_encode", "poly_tobytes_spec(rrec_canonical_forward(ow_coeff_words p)).",
        "op [opaque] ow_unit_test", "rrec_public_inverse(decoded_poly(ow_encode a))<>None.",
        "op [opaque] ow_rlwe_value", "ow_key_poly(pke_ciphertext(ow_encode a)error secret).",
        "op [opaque] ow_recover", "let answer=rrec_linear_spec(ow_encode a)code(ow_encode b) in",
        "if answer=None then NTRUPoly.poly0 else input_poly(oget answer)."))
    policy.shared.ordered(code["key"], (
        "op [opaque] ow_ntru_key (f g:NTRUPoly.poly) = ow_unscale3(gen_public_key f g).",))
    policy.shared.ordered(code["conditioning"], (
        "op [opaque] ow_alpha_g = mu pke_field_psi1 pke_rq_unit.",
        "op [opaque] ow_raw_fg_law = gen_f_law `*` pke_field_psi1.",
        "op ow_g_unit (fg:NTRUPoly.poly*NTRUPoly.poly) = pke_rq_unit fg.`2."))
    policy.shared.ordered(code["games"], (
        "module OWKernel(B:SecOWAdversary)", "code<$pke_psi1;r<$pke_psi1;ct<-pke_ciphertext pk code r;",
        "answer<@B.run(pk,ct);return answer=code;",
        "module OWFieldKernel(B:SecOWAdversary)", "win<-false;",
        "if(ow_unit_test a){win<@OWKernel(B).run(ow_encode a);}",
        "module OWNTRUReduction(B:SecOWAdversary)", "win<@OWFieldKernel(B).guess(ow_scale3 h);",
        "module OWNTRURealGame(D:OWNTRUAdversary)", "fg<$ow_raw_fg_law;",
        "win<@D.run(ow_ntru_key fg.`1 fg.`2);", "module OWNTRUUniformGame(D:OWNTRUAdversary)",
        "h<$ow_uniform_rq;win<@D.run(h);", "module OWUniformTest(B:SecOWAdversary)",
        "a<$ow_uniform_rq;win<@OWFieldKernel(B).guess(a);",
        "module OWUniformSource(B:SecOWAdversary)", "a<$ow_uniform_rq;code<$pke_psi1;r<$pke_psi1;win<-false;",
        "if(ow_unit_test a){", "pk<-ow_encode a;ct<-pke_ciphertext pk code r;",
        "answer<@B.run(pk,ct);win<-answer=code;",
        "module OWRLWESolver(B:SecOWAdversary)", "answer<-NTRUPoly.poly0;",
        "if(ow_unit_test a){", "code<@B.run(ow_encode a,ow_encode b);", "answer<-ow_recover a b code;",
        "module OWRLWEGame(C:OWRLWEAdversary)", "a<$ow_uniform_rq;error<$pke_psi1;secret<$pke_psi1;",
        "b<-ow_rlwe_value a secret error;", "answer<@C.run(a,b);return answer=input_poly secret;"))
    body = code["games"].split("moduleOWNTRURealGame", 1)[1].split("moduletypeOWBoolPolyPort", 1)[0]
    for forbidden in ("ROMInit", "ROF.get", "ROG.get", "ROH.get", "ROE.get", "dcond"):
        policy.require(forbidden not in body, "hardness experiment adds oracle or hidden conditioning: " + forbidden)


MUTATIONS = (
    ("conditioning", "alpha-unit-predicate-deleted", "mu pke_field_psi1 pke_rq_unit", "mu pke_field_psi1 predT"),
    ("conditioning", "alpha-sampled-from-conditioned-g", "mu pke_field_psi1 pke_rq_unit", "mu gen_g_law pke_rq_unit"),
    ("conditioning", "raw-pair-guard-tests-f", "pke_rq_unit fg.`2.", "pke_rq_unit fg.`1."),
    ("games", "NTRU-uses-accepted-pair-law", "fg<$ow_raw_fg_law;", "fg<$gen_fg_law;"),
    ("games", "NTRU-pair-components-swapped", "ow_ntru_key fg.`1 fg.`2", "ow_ntru_key fg.`2 fg.`1"),
    ("key", "raw-NTRU-ratio-keeps-extra-three", "ow_unscale3(gen_public_key f g)", "gen_public_key f g"),
    ("key", "raw-NTRU-ratio-swaps-inputs", "ow_unscale3(gen_public_key f g)", "ow_unscale3(gen_public_key g f)"),
    ("uniform", "uniform-ring-conditioned-on-unit", "dmap (dlist CycloFq.DZmodP.dunifin 768) NTRUPoly.polyL.", "dcond (dmap (dlist CycloFq.DZmodP.dunifin 768) NTRUPoly.polyL) pke_rq_unit."),
    ("uniform", "wrong-ring-dimension", "dlist CycloFq.DZmodP.dunifin 768", "dlist CycloFq.DZmodP.dunifin 767"),
    ("uniform", "uniform-bytes-replace-uniform-ring", "dmap (dlist CycloFq.DZmodP.dunifin 768) NTRUPoly.polyL", "dmap uniform1152 ow_key_poly"),
    ("uniform", "scale-three-deleted", "NTRUPoly.polyC(lift_int 3)) p.", "NTRUPoly.polyC(lift_int 1)) p."),
    ("codec", "public-codec-skips-NTT", "rrec_canonical_forward(ow_coeff_words p)", "ow_coeff_words p"),
    ("codec", "unit-test-is-unconditional", "rrec_public_inverse(decoded_poly(ow_encode a))<>None", "true"),
    ("codec", "RLWE-secret-error-swapped", "pke_ciphertext(ow_encode a)error secret", "pke_ciphertext(ow_encode a)secret error"),
    ("codec", "solver-returns-error-directly", "if answer=None then NTRUPoly.poly0 else input_poly(oget answer)", "input_poly code"),
    ("codec", "solver-subtracts-wrong-input", "rrec_linear_spec(ow_encode a)code(ow_encode b)", "rrec_linear_spec(ow_encode a)code(ow_encode a)"),
    ("games", "OW-message-randomness-correlated", "code<$pke_psi1;r<$pke_psi1;", "code<$pke_psi1;r<-code;"),
    ("games", "OW-target-is-randomness", "return answer=code;", "return answer=r;"),
    ("conditioning", "NTRU-unconditioned-denominator", "gen_f_law `*` pke_field_psi1", "pke_field_psi1 `*` pke_field_psi1"),
    ("conditioning", "NTRU-condition-g-silently", "gen_f_law `*` pke_field_psi1", "gen_f_law `*` gen_g_law"),
    ("games", "NTRU-distinguisher-omits-three", "guess(ow_scale3 h)", "guess(h)"),
    ("games", "distinguisher-skips-unit-guard", "if(ow_unit_test a){win<@OWKernel(B)", "if(true){win<@OWKernel(B)"),
    ("games", "uniform-game-resamples-real-ratio", "h<$ow_uniform_rq;", "h<$gen_f_law;"),
    ("games", "solver-skips-unit-guard", "if(ow_unit_test a){\n   code<@B.run", "if(true){\n   code<@B.run"),
    ("games", "solver-replaces-RLWE-public-input", "B.run(ow_encode a,ow_encode b)", "B.run(ow_encode(ow_scale3 a),ow_encode b)"),
    ("games", "RLWE-secret-error-correlated", "error<$pke_psi1;secret<$pke_psi1;", "error<$pke_psi1;secret<-error;"),
    ("games", "RLWE-returns-error-target", "return answer=input_poly secret;", "return answer=input_poly error;"),
    ("games", "RLWE-challenge-is-message-alone", "b<-ow_rlwe_value a secret error;", "b<-input_poly error;"),
    ("games", "hardness-challenger-uses-ROM", "h<$ow_uniform_rq;", "ROMInit.init();h<$ow_uniform_rq;"),
)
