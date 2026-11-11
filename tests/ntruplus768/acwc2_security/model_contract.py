"""Concrete oracle, collision and recovery interfaces; not proof validity."""
import policy

SOURCES = {
    "model": policy.PROOF / "NTRUPlus768SecModel.ec",
    "games": policy.PROOF / "NTRUPlus768SecGames.ec",
    "oracles": policy.PROOF / "NTRUPlus768SecGOracles.ec",
    "extract": policy.PROOF / "NTRUPlus768SecExtractModel.ec",
}


def check(texts=None):
    texts = texts or {key: path.read_text() for key, path in SOURCES.items()}
    code = {key: policy.compact(texts[key]) for key in SOURCES}
    policy.shared.ordered(code["model"], (
        "module SecPhase(A:CCAExtendedAdversary,G:FOGPort)", "suffix<@ROF.get(pk);",
        "SimPublic.init(pk,suffix,ct);SimHistory.init();",
        "answer<@A(SimOracles(G,SimHActual),SimLookup(G)).guess(pk,ct,key);",
        "module SecRun(A:CCAExtendedAdversary,G:FOGPort)", "key<$uniform32;",
        "ignored<@SecPhase(A,G).run(pk,ct,key);", "return !((target,SimPublic.suffix) \\in SimHistory.h);",
        "op sec_inj_win", "pke_domain w.`1 /\\ pke_domain w.`2 /\\ pke_domain w.`3 /\\ pke_domain w.`4 /\\",
        "(w.`1,w.`3)<>(w.`2,w.`4) /\\",
        "pke_enc_spec pk w.`1 w.`3=pke_enc_spec pk w.`2 w.`4 /\\",
        "pke_enc_spec pk w.`1 w.`3<>None.",
        "module SecINJGame(B:SecINJAdversary)", "out<@B.run(pk);return sec_inj_win pk out;",
        "module SecOWGame(B:SecOWAdversary)", "ROMInit.init();RawXOFStreams.init();",
        "(pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();",
        "code<$pke_psi1;r<$pke_psi1;ct<-pke_ciphertext pk code r;",
        "answer<@B.run(pk,ct);return answer=code;"))
    phase = code["model"].split("moduleSecPhase(", 1)[1].split("moduletypeSecGContext", 1)[0]
    for forbidden in ("ROG.init", "ROG.m", "ROG.get", "FOGActual", "ROMInit.init", "CCADecapOracle", "FOContext"):
        policy.require(forbidden not in phase, "adaptive G port bypass or secret access: " + forbidden)
    policy.shared.ordered(code["oracles"], (
        "module SecGHistory = {", "var queries:W8.t Array1152.t list", "queries<-[];",
        "module SecGLogged(G:FOGPort)", "SecGHistory.queries<-input::SecGHistory.queries;", "y<@G.get(input);",
        "module SecGMark", "target<-x;hit<-false;",
        "module SecGMarked(G:FOGPort)", "SecGMark.hit<-SecGMark.hit || input=SecGMark.target;",
        "y<@SecGLogged(G).get(input);"))
    policy.shared.ordered(code["games"], (
        "module SecGame(A:CCAExtendedAdversary)", "target<$uniform96;other<$uniform96;bit<$dbool;",
        "r<$pke_psi1;pad<$uniform192;",
        "code<-poly_sotp_encode_spec (if bit then other else target) pad;",
        "ct<-pke_ciphertext pk code r;",
        "ROG.m<-if program then empty.[rr_G_input r<-pad] else empty;", "SecGHistory.init();",
        "guess<@SecRun(A,SecGLogged(FOGActual)).run(pk,ct,target);",
        "so_queries=SecGHistory.queries", "module SecRandomGame(A:CCAExtendedAdversary)",
        "r<$pke_psi1;code<$pke_psi1;ct<-pke_ciphertext pk code r;", "SecGHistory.init();",
        "guess<@SecRun(A,SecGLogged(FOGActual)).run(pk,ct,target);"))
    game = code["games"].split("moduleSecGame(", 1)[1].split("moduleSecRandomGame(", 1)[0]
    policy.require("SecGLogged(FOGActual).get" not in game, "challenge evaluation was added to adaptive log")
    policy.shared.ordered(code["extract"], (
        "op [opaque] sec_candidate", "let ro=mrec_decode_randomness query in", "if ro=None then None else",
        "let mo=mrec_spec pk (oget ro) ct in", "if mo=None then None else Some(oget mo,oget ro).",
        "op [opaque] sec_eligible", "sec_candidate pk ct query<>None /\\",
        "(excluded=None \\/ (oget(sec_candidate pk ct query)).`2<>oget excluded).",
        "op [opaque] sec_extract_spec", "sim_first (sec_eligible pk ct excluded)",
        "op sec_bad2", "query \\in s.`so_queries", "r<>s.`so_r.",
        "op sec_inj_output", "sec_extract_spec s.`so_pk s.`so_ct (Some s.`so_r) s.`so_queries",
        "if out=None then (s.`so_code,s.`so_code,s.`so_r,s.`so_r)",
        "op sec_ow_output", "sec_extract_spec s.`so_pk s.`so_ct None s.`so_queries"))


MUTATIONS = (
    ("model", "typed-raw-G-bypasses-port", "SimOracles(G,SimHActual)", "SimOracles(FOGActual,SimHActual)"),
    ("model", "internal-lookup-G-bypasses-port", "SimLookup(G)", "SimLookup(FOGActual)"),
    ("model", "reset-G-in-adaptive-phase", "suffix<@ROF.get(pk);", "ROG.init();suffix<@ROF.get(pk);"),
    ("model", "secret-decapsulation-substitution", "SimLookup(G)", "CCADecapOracle"),
    ("model", "collision-domain-dropped", "pke_domain w.`4 /\\", "true /\\"),
    ("model", "identical-pairs-counted-as-collision", "(w.`1,w.`3)<>(w.`2,w.`4)", "true"),
    ("model", "unequal-ciphertexts-counted-as-collision", "pke_enc_spec pk w.`1 w.`3=pke_enc_spec pk w.`2 w.`4", "true"),
    ("model", "None-None-counted-as-collision", "pke_enc_spec pk w.`1 w.`3<>None", "true"),
    ("model", "OW-message-not-psi1", "code<$pke_psi1;", "code<-witness;"),
    ("model", "OW-randomness-not-independent", "r<$pke_psi1;", "r<-code;"),
    ("model", "OW-guesses-randomness", "return answer=code;", "return answer=r;"),
    ("oracles", "duplicate-G-queries-erased", "SecGHistory.queries<-input::SecGHistory.queries;", "SecGHistory.queries<-[input];"),
    ("oracles", "marked-G-bypasses-log", "y<@SecGLogged(G).get(input);", "y<@G.get(input);"),
    ("oracles", "mark-does-not-latch", "SecGMark.hit || input=SecGMark.target", "input=SecGMark.target"),
    ("games", "honest-challenge-added-to-log", "SecGHistory.init();", "SecGHistory.init();pad<@SecGLogged(FOGActual).get(rr_G_input r);"),
    ("games", "adaptive-phase-not-logged", "SecRun(A,SecGLogged(FOGActual))", "SecRun(A,FOGActual)"),
    ("games", "unused-message-no-longer-independent", "other<$uniform96;", "other<-target;"),
    ("games", "random-game-code-not-psi1", "r<$pke_psi1;code<$pke_psi1;", "r<$pke_psi1;code<-r;"),
    ("extract", "invalid-G-payload-not-skipped", "if ro=None then None else", "if false then None else"),
    ("extract", "failed-recovery-not-skipped", "if mo=None then None else", "if false then None else"),
    ("extract", "collision-search-accepts-honest-r", "(oget(sec_candidate pk ct query)).`2<>oget excluded", "true"),
    ("extract", "collision-default-is-invented", "if out=None then (s.`so_code,s.`so_code,s.`so_r,s.`so_r)", "if out=None then witness"),
)
