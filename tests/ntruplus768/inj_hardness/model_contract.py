"""Integer witness, exact collision, conditioning and uniform-game boundaries."""
import policy

SOURCES = {
    "collision": policy.PROOF / "NTRUPlus768INJCollision.ec",
    "bounds": policy.PROOF / "NTRUPlus768INJBounds.ec",
    "games": policy.PROOF / "NTRUPlus768INJGames.ec",
    "existence": policy.PROOF / "NTRUPlus768INJExistence.ec",
    "base": policy.BASE / "kem_acwc2_security/NTRUPlus768SecModel.ec",
    "uniform": policy.BASE / "kem_ow_hardness/NTRUPlus768OWUniform.ec",
    "conditioning": policy.BASE / "kem_ow_hardness/NTRUPlus768OWKeyConditioning.ec",
    "ntru": policy.BASE / "kem_ow_hardness/NTRUPlus768OWGames.ec",
}


def check(texts=None):
    texts = texts or {key: path.read_text() for key, path in SOURCES.items()}
    code = {key: policy.compact(texts[key]) for key in SOURCES}
    policy.shared.ordered(code["collision"], (
        "type inj_vector = int Array768.t.", "type inj_pair = inj_vector * inj_vector.",
        "op [opaque] inj_word_difference (x y:pke_poly) : inj_vector =",
        "Array768.map2(fun a b=>coeff a-coeff b)x y.",
        "op [opaque] inj_difference_pair (z:sec_collision) : inj_pair =",
        "(inj_word_difference z.`3 z.`4,inj_word_difference z.`1 z.`2).",
        "op [opaque] inj_zero : inj_vector = Array768.init(fun _=>0).",
        "op inj_zero_pair : inj_pair = (inj_zero,inj_zero).",
        "op inj_short (v:inj_vector) = forall i,0<=i<768=> -2<=v.[i]<=2.",
        "op inj_pair_nonzero (v w:inj_vector) = v<>inj_zero \\/ w<>inj_zero.",
        "op inj_relation (h:NTRUPoly.poly) (v w:inj_vector) =",
        "eqm_global (NTRUPoly.PolyComRing.( + ) (NTRUPoly.PolyComRing.( * ) h (int_poly v)) (int_poly w)) NTRUPoly.poly0.",
        "op inj_short_win (h:NTRUPoly.poly) (z:inj_pair) =",
        "inj_short z.`1 /\\ inj_short z.`2 /\\ inj_pair_nonzero z.`1 z.`2 /\\ inj_relation h z.`1 z.`2."))
    policy.shared.ordered(code["bounds"], (
        "op inj_sqnorm(v:int Array768.t) : int =", "Bigint.BIA.bigi predT (fun i=>v.[i]*v.[i]) 0 768.",
        "op inj_pair_sqnorm(z:int Array768.t * int Array768.t) : int = inj_sqnorm z.`1+inj_sqnorm z.`2.",
        "op inj_infnorm(v:int Array768.t) : int =", "inj_maximum(map(fun i=>`|v.[i]|)(range 0 768)).",
        "op inj_pair_infnorm(z:int Array768.t * int Array768.t) : int = max (inj_infnorm z.`1) (inj_infnorm z.`2).",
        "lemma inj_short_nonzero_pair_bounds v w : inj_short v=>inj_short w=>inj_pair_nonzero v w=>",
        "0<inj_pair_sqnorm(v,w)<=6144 /\\ inj_pair_infnorm(v,w)<=2 /\\",
        "inj_sqnorm v<=3072 /\\ inj_sqnorm w<=3072."))
    policy.shared.ordered(code["base"], (
        "op sec_inj_win (pk:W8.t Array1152.t) (w:sec_collision) =",
        "pke_domain w.`1 /\\ pke_domain w.`2 /\\ pke_domain w.`3 /\\ pke_domain w.`4 /\\",
        "(w.`1,w.`3)<>(w.`2,w.`4) /\\",
        "pke_enc_spec pk w.`1 w.`3=pke_enc_spec pk w.`2 w.`4 /\\",
        "pke_enc_spec pk w.`1 w.`3<>None."))
    policy.shared.ordered(code["uniform"], (
        "op ow_rq_domain(p:NTRUPoly.poly) = NTRUPoly.deg p<=768.",
        "op ow_uniform_rq : NTRUPoly.poly distr =",
        "dmap (dlist CycloFq.DZmodP.dunifin 768) NTRUPoly.polyL."))
    uniform_body = code["uniform"].split("opow_uniform_rq", 1)[1].split("opow_scale3", 1)[0]
    for forbidden in ("dcond", "dexcepted", "pke_rq_unit", "uniform1152", "ow_unit_test"):
        policy.require(forbidden not in uniform_body, "uniform challenge distribution changed: " + forbidden)
    policy.shared.ordered(code["conditioning"], (
        "op [opaque] ow_alpha_g = mu pke_field_psi1 pke_rq_unit.",
        "op [opaque] ow_raw_fg_law = gen_f_law `*` pke_field_psi1.",
        "op ow_g_unit (fg:NTRUPoly.poly*NTRUPoly.poly) = pke_rq_unit fg.`2."))
    policy.shared.ordered(code["ntru"], (
        "module OWNTRURealGame(D:OWNTRUAdversary)", "fg<$ow_raw_fg_law;",
        "win<@D.run(ow_ntru_key fg.`1 fg.`2);", "module OWNTRUUniformGame(D:OWNTRUAdversary)",
        "h<$ow_uniform_rq;win<@D.run(h);"))
    policy.shared.ordered(code["games"], (
        "module INJKernel(B:SecINJAdversary)", "collision<@B.run(pk);return sec_inj_win pk collision;",
        "module INJFieldKernel(B:SecINJAdversary)", "win<-false;",
        "if(ow_unit_test a){win<@INJKernel(B).run(ow_encode a);}",
        "module INJNTRUReduction(B:SecINJAdversary)", "win<@INJFieldKernel(B).guess(ow_scale3 h);",
        "module INJUniformTest(B:SecINJAdversary)", "a<$ow_uniform_rq;win<@INJFieldKernel(B).guess(a);",
        "module type INJShortAdversary", "module INJShortSolver(B:SecINJAdversary)",
        "result<-inj_zero_pair;", "if(ow_unit_test a){", "pk<-ow_encode a;collision<@B.run(pk);",
        "if(sec_inj_win pk collision){result<-inj_difference_pair collision;}",
        "module INJShortRelationGame(C:INJShortAdversary)",
        "a<$ow_uniform_rq;out<@C.run(a);return inj_short_win a out;"))
    challenge = code["games"].split("moduleINJShortRelationGame", 1)[1].split("lemma", 1)[0]
    for forbidden in ("dcond", "dexcepted", "ow_unit_test", "while", "ROMInit", "ROF.get", "ROG.get", "ROH.get", "ROE.get"):
        policy.require(forbidden not in challenge, "short-relation challenger has hidden condition/oracle: " + forbidden)
    policy.shared.ordered(code["existence"], (
        "op [opaque] inj_relation_exists (a:NTRUPoly.poly) = exists (z:inj_pair),inj_short_win a z.",
        "op [opaque] inj_uniform_bad_mass = mu ow_uniform_rq inj_relation_exists.",
        "lemma inj_uniform_existence_bound (C<:INJShortAdversary) &m : Pr[INJShortRelationGame(C).run()@&m:res]<=inj_uniform_bad_mass."))


MUTATIONS = (
    ("collision", "word-array-instead-of-integer-array", "type inj_vector = int Array768.t.", "type inj_vector = W16.t Array768.t."),
    ("collision", "unsigned-lift", "coeff a-coeff b", "W16.to_uint a-W16.to_uint b"),
    ("collision", "word-subtraction-before-lifting", "coeff a-coeff b", "coeff(a-b)"),
    ("collision", "randomness-message-differences-swapped", "(inj_word_difference z.`3 z.`4,inj_word_difference z.`1 z.`2)", "(inj_word_difference z.`1 z.`2,inj_word_difference z.`3 z.`4)"),
    ("collision", "zero-vector-is-one", "Array768.init(fun _=>0).", "Array768.init(fun _=>1)."),
    ("collision", "wrong-integer-dimension", "0<=i<768=> -2<=v.[i]<=2", "0<=i<767=> -2<=v.[i]<=2"),
    ("collision", "coefficient-bound-weakened", "-2<=v.[i]<=2", "-3<=v.[i]<=3"),
    ("collision", "nonzero-witness-deleted", "v<>inj_zero \\/ w<>inj_zero", "true"),
    ("collision", "integer-nonzero-replaced-by-field-nonzero", "v<>inj_zero \\/ w<>inj_zero", "int_poly v<>NTRUPoly.poly0 \\/ int_poly w<>NTRUPoly.poly0"),
    ("collision", "requires-both-components-nonzero", "v<>inj_zero \\/ w<>inj_zero", "v<>inj_zero /\\ w<>inj_zero"),
    ("collision", "relation-omits-randomness-vector", "h (int_poly v)", "h NTRUPoly.poly0"),
    ("collision", "short-win-omits-second-bound", "inj_short z.`1 /\\ inj_short z.`2 /\\", "inj_short z.`1 /\\"),
    ("bounds", "pair-norm-takes-maximum", "inj_sqnorm z.`1+inj_sqnorm z.`2", "max (inj_sqnorm z.`1) (inj_sqnorm z.`2)"),
    ("bounds", "pair-square-bound-is-4n", "0<inj_pair_sqnorm(v,w)<=6144", "0<inj_pair_sqnorm(v,w)<=3072"),
    ("base", "base-collision-omits-domain", "pke_domain w.`1 /\\", "true /\\"),
    ("base", "base-collision-allows-identical-pairs", "(w.`1,w.`3)<>(w.`2,w.`4)", "true"),
    ("base", "base-collision-allows-two-failures", "pke_enc_spec pk w.`1 w.`3<>None", "true"),
    ("uniform", "uniform-conditioned-on-unit", "dmap (dlist CycloFq.DZmodP.dunifin 768) NTRUPoly.polyL.", "dcond (dmap (dlist CycloFq.DZmodP.dunifin 768) NTRUPoly.polyL) pke_rq_unit."),
    ("uniform", "uniform-random-bytes", "dmap (dlist CycloFq.DZmodP.dunifin 768) NTRUPoly.polyL", "dmap uniform1152 ow_key_poly"),
    ("conditioning", "alpha-from-conditioned-g", "mu pke_field_psi1 pke_rq_unit", "mu gen_g_law pke_rq_unit"),
    ("conditioning", "raw-f-unconditioned", "gen_f_law `*` pke_field_psi1", "pke_field_psi1 `*` pke_field_psi1"),
    ("conditioning", "raw-g-condition-silently-added", "gen_f_law `*` pke_field_psi1", "gen_f_law `*` gen_g_law"),
    ("ntru", "NTRU-uses-conditioned-key-law", "fg<$ow_raw_fg_law;", "fg<$gen_fg_law;"),
    ("games", "INJ-kernel-skips-collision-check", "return sec_inj_win pk collision;", "return true;"),
    ("games", "INJ-field-skips-unit-guard", "if(ow_unit_test a){win<@INJKernel", "if(true){win<@INJKernel"),
    ("games", "NTRU-distinguisher-omits-three", "guess(ow_scale3 h)", "guess(h)"),
    ("games", "solver-skips-unit-guard", "result<-inj_zero_pair;\n  if(ow_unit_test a)", "result<-inj_zero_pair;\n  if(true)"),
    ("games", "solver-skips-collision-validation", "if(sec_inj_win pk collision)", "if(true)"),
    ("games", "solver-forges-difference", "result<-inj_difference_pair collision", "result<-inj_zero_pair"),
    ("games", "uniform-experiment-uses-accepted-keys", "a<$ow_uniform_rq;out<@C.run(a)", "a<$gen_f_law;out<@C.run(a)"),
    ("games", "relation-game-omits-success-predicate", "return inj_short_win a out;", "return true;"),
    ("games", "challenger-adds-auxiliary-ROM", "a<$ow_uniform_rq;out<@C.run(a)", "ROMInit.init();a<$ow_uniform_rq;out<@C.run(a)"),
    ("existence", "existence-omits-shortness-and-nonzero", "exists (z:inj_pair),inj_short_win a z.", "exists (z:inj_pair),inj_relation a z.`1 z.`2."),
    ("existence", "existence-is-restricted-to-units", "exists (z:inj_pair),inj_short_win a z.", "ow_unit_test a /\\ exists (z:inj_pair),inj_short_win a z."),
    ("existence", "existence-mass-hardcoded-zero", "mu ow_uniform_rq inj_relation_exists", "0%r"),
    ("existence", "existence-mass-hardcoded-negligible", "mu ow_uniform_rq inj_relation_exists", "1%r/(2%r^253)"),
    ("existence", "existence-mass-conditioned-on-units", "mu ow_uniform_rq inj_relation_exists", "mu (dcond ow_uniform_rq pke_rq_unit) inj_relation_exists"),
    ("existence", "existence-mass-uses-NTRU-key-law", "mu ow_uniform_rq inj_relation_exists", "mu gen_f_law inj_relation_exists"),
    ("existence", "existence-bound-adds-losslessness", "Pr[INJShortRelationGame(C).run()@&m:res]<=inj_uniform_bad_mass.", "islossless C.run=>Pr[INJShortRelationGame(C).run()@&m:res]<=inj_uniform_bad_mass."),
)
