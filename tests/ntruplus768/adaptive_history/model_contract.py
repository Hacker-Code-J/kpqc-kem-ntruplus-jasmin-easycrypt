"""Draft/frozen adaptive-history contracts and fresh-store source scope."""
import importlib.util
import re
import policy
import scope_controls

ALLOWED = {"AHState", "AHAdapter", "AHFreshBound", "AHCallbacks", "AHRawCallbacks", "AHCoupling",
           "AHCPAGames", "AHCPABound", "AHReduction", "AHActualReduction", "AHFinal"}
# Explicitly approved final inventory; new files require a new review.
FINAL_REQUIRED = {"AHState", "AHAdapter", "AHFreshBound", "AHCallbacks", "AHRawCallbacks", "AHCoupling",
                  "AHCPAGames", "AHCPABound", "AHReduction", "AHActualReduction", "AHFinal"}
SYNTAX_SOURCE = policy.TEST.parent / "history_refinement/executable_policy.py"
_spec = importlib.util.spec_from_file_location("history_runtime_syntax", SYNTAX_SOURCE)
_syntax = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_syntax)

ORDERED = {
    "AHState": [
        "type ah_state", "ah_rows:hist_table", "ah_pk:W8.t Array1152.t",
        "ah_suffix:W8.t Array32.t", "ah_cstar:W8.t Array1152.t option",
        "module type AHStore", "proc init", "proc snapshot():ah_state", "proc record",
        "lemma ah_record_rep", "hist_rep(ah_record_state st input hout).`ah_rows table.[input<-hout]",
    ],
    "AHAdapter": [
        "module AHPublicG(O:CCAExtendedOraclePort)", "result<@O.g(input);return result;",
        "module AHRecordH(S:AHStore,O:CCAExtendedOraclePort)",
        "hout<@O.h(input);S.record(input,hout);return hout;",
        "module AHOracles", "proc e=O.e", "proc f=O.f", "proc g=O.g", "proc h=AHRecordH(S,O).get",
        "if(0<=outlen<=raw_xof_max_output)", "match decode_typed input with",
        "None => {result<@O.raw(input,outlen);}", "E seed => {result<@O.raw(input,outlen);}",
        "F pk => {result<@O.raw(input,outlen);}", "G serialized => {result<@O.raw(input,outlen);}",
        "H payload =>", "hout<@AHRecordH(S,O).get(payload);", "result<-Some(raw_xof_output outlen hout);",
        "else{result<@O.raw(input,outlen);}", "module AHDecap", "st<@S.snapshot();",
        "result<@HistLookup(AHPublicG(O)).run(st.`ah_rows,st.`ah_pk,st.`ah_suffix,st.`ah_cstar,ct);",
        "return result.`1;", "module AHWrapper", "suffix<@O.f(pk);S.init(pk,suffix,Some ct);",
        "answer<@A(AHOracles(S,O),AHDecap(S,O)).guess(pk,ct,key);",
        "lemma ah_record_h_ll", "islossless O.h=>islossless S.record=>",
        "lemma ah_raw_zero_h_view", "view(glob S)=ah_record_state st0 input0 hout", "res=Some []",
    ],
    "AHFreshBound": [
        "op ah_fresh_full", "decode_typed input=Some(H x) /\\ x \\notin log",
        "op ah_fresh_raw", "0<=outlen<=raw_xof_max_output /\\ ah_fresh_full input log",
        "op ah_fresh_inv", "!bad=>fo_hcache_good w g None s.`4",
        "module AHFreshPhase", "SimBad.corr<-false;",
        "answer<@A(AHFreshOracles,SimLookup(FOGActual)).guess(pk,ct,key)",
        "lemma ah_fresh_h_rank", "fsize log0+b2i(x0 \\notin log0)",
        "x0 \\in log0=>SimBad.corr=b0", "lemma ah_fresh_raw_rank",
        "fsize log0+b2i(ah_fresh_raw input0 outlen0 log0)",
    ],
    "AHCPAGames": [
        "module AHCPAContext", "target<$uniform96;other<$uniform96;bit<$dbool;hout<$uniform224;",
        "enc<@SimEncrypt(G).run(out.`1.`kg_pk,if bit then other else target,hout);",
        "guess<@SecRun(A,G).run(out.`1.`kg_pk,oget enc,target);", "return guess=bit;",
        "module AHCPAKernel", "ROF.m<-s.`2;ROG.m<-acwc2_g_cache s.`3;",
        "module AHCPAJointGame", "s<@FOSetupSource.guess(witness);win<@AHCPAKernel(A).guess(s);",
        "lemma ah_cpa_actual_mu", "Pr[CPAGame(CPAReduction(A)).run()@&m:res]",
    ],
    "AHReduction": [
        "module AH_DI", "INJNTRUReduction(SecINJAuxAdapter(SecINJReducer(AHWrapper(S,A))))",
        "module AH_DO", "OWNTRUReduction(SecOWAuxAdapter(SecOWReducer(AHWrapper(S,A))))",
        "module AH_CO", "OWRLWESolver(SecOWAuxAdapter(SecOWReducer(AHWrapper(S,A))))",
        "lemma ah_wrapper_lossless", "islossless S.init=>islossless S.snapshot=>islossless S.record=>",
        "islossless D0.decap=>islossless A(H,D0).guess", "lemma ah_cpa_hardness",
    ],
    "AHCallbacks": [
        "op [opaque] ah_view_rep", "hist_rep st.`ah_rows log /\\ ah_context st=(pk,suffix,star)",
        "lemma ah_h_coupling", "islossless S.record =>",
        "view(glob S)=ah_record_state st x y", "lemma ah_decap_coupling",
        "pke_key_relation w=>islossless S.snapshot=>",
        "res=st /\\ view(glob S)=st", "fo_hcache_good w g None SimHistory.h{1}",
        "acwc2_cache_matches g ROG.m{1}",
    ],
    "AHRawCallbacks": [
        "lemma ah_raw_non_h_forward", "!(0<=n0<=raw_xof_max_output) \\/ forall x,decode_typed input0<>Some(H x)",
        "equiv[AHOracles(S,O).raw ~ O.raw", "lemma ah_raw_coupling",
        "islossless S.record=>", "view(glob S)=ah_record_state st x y",
        "equiv[AHFreshOracles.raw ~ AHOracles(S,AHFreshOracles).raw",
        "acwc2_cache_matches g ROG.m{1}", "ah_fresh_inv w g",
    ],
    "AHCoupling": [
        "lemma ah_adversary_coupling", "pke_key_relation w=>islossless S.snapshot=>islossless S.record=>",
        "res=st /\\ view(glob S)=st", "view(glob S)=ah_record_state st x y",
        "islossless D.decap=>islossless A(H,D).guess",
        "equiv[A(AHFreshOracles,SimLookup(FOGActual)).guess ~ A(AHOracles(S,AHFreshOracles),AHDecap(S,AHFreshOracles)).guess",
        "!SimBad.corr{1}", "!SimBad.corr{1}=> ={res,glob A}",
        "lemma ah_phase_coupling", "pke_key_relation w=>islossless S.init=>islossless S.snapshot=>islossless S.record=>",
        "view(glob S)=ah_initial pk suffix star", "ROH.m{1}=empty /\\ acwc2_cache_matches g ROG.m{1}",
    ],
    "AHCPABound": [
        "lemma ah_cpa_setup_facts", "fo_setup_valid s=>", "module AHCPAMonitoredKernel",
        "lemma ah_cpa_monitored_bad", "lemma ah_cpa_monitored_coupling", "lemma ah_cpa_distance",
        "islossless S.init=>islossless S.snapshot=>islossless S.record=>",
        "view(glob S)=ah_initial pk suffix star", "res=st /\\ view(glob S)=st",
        "view(glob S)=ah_record_state st x y", "islossless D.decap=>islossless A(H,D).guess",
        "0<=qC=>hoare[CPAPhase(A).run:true ==>fsize SimHistory.h<=qC]=>",
        "Pr[CPAGame(CPAReduction(A)).run()@&m:res]", "Pr[CPAGame(CPAReduction(AHWrapper(S,A))).run()@&m:res]",
        "<=qC%r/(2%r^353)", "fo_setup_law_support", "sim_setup_distance_average",
    ],
    "AHActualReduction": [
        "module AHActualOracles", "proc h=ROH.get", "proc raw=FOGRaw(G).get",
        "module AHRejectD", "return None;", "module AHActualPhase",
        "AHWrapper(S,A,AHActualOracles(G),AHRejectD).guess(pk,ct,key)",
        "module AHActualTranscript", "SecGHistory.init();key<$uniform32;",
        "AHActualPhase(S,A,SecGLogged(FOGActual)).run(pk,ct,key)", "return SecGHistory.queries;",
        "module AHActualINJReducer", "queries<@AHActualTranscript(S,A).run(pk,ct);",
        "out<@SecExtract.run(pk,ct,Some r,queries);", "module AHActualOWReducer",
        "queries<@AHActualTranscript(S,A).run(pk,ct);out<@SecExtract.run(pk,ct,None,queries);",
        "module AHActual_DI", "INJNTRUReduction(SecINJAuxAdapter(AHActualINJReducer(S,A)))",
        "module AHActual_DO", "OWNTRUReduction(SecOWAuxAdapter(AHActualOWReducer(S,A)))",
        "module AHActual_CO", "OWRLWESolver(SecOWAuxAdapter(AHActualOWReducer(S,A)))",
        "lemma ah_actual_transcript_projection", "lemma ah_actual_cpa_hardness",
    ],
    "AHFinal": [
        "section.", "declare module A <: CCAExtendedAdversary", "local module AHPrivateStore : AHStore = {",
        "var st:ah_state", "st<-{|ah_rows=[];ah_pk=pk;ah_suffix=suffix;ah_cstar=cstar|};",
        "proc snapshot():ah_state = {return st;}", "updated<@HistTable.put(input,hout,st.`ah_rows);",
        "st<-{|ah_rows=updated.`1;ah_pk=st.`ah_pk;ah_suffix=st.`ah_suffix;ah_cstar=st.`ah_cstar|};",
        "local lemma ah_private_init_ll", "local lemma ah_private_snapshot_ll", "local lemma ah_private_record_ll",
        "local lemma ah_private_init", "local lemma ah_private_snapshot", "local lemma ah_private_record",
        "local lemma ah_private_frame",
    ],
}

MUTATIONS = [
    ("AHAdapter", "internal-G-bypasses-supplied-port", "result<@O.g(input)", "result<@ROG.get(input)"),
    ("AHAdapter", "full-H-record-removed", "S.record(input,hout);", ""),
    ("AHAdapter", "zero-length-H-not-recorded", "if(0<=outlen<=raw_xof_max_output)", "if(0<outlen<=raw_xof_max_output)"),
    ("AHAdapter", "H-prefix-before-full-record", "hout<@AHRecordH(S,O).get(payload);", "hout<@O.h(payload);"),
    ("AHAdapter", "invalid-raw-not-forwarded", "else{result<@O.raw(input,outlen);}", "else{result<-None;}"),
    ("AHAdapter", "D-uses-legacy-map-scan", "result<@HistLookup(AHPublicG(O)).run", "result<@SimLookup(AHPublicG(O)).run"),
    ("AHAdapter", "challenge-state-init-lost", "S.init(pk,suffix,Some ct);", "S.init(pk,suffix,None);"),
    ("AHFreshBound", "repeated-H-counted-fresh", "b2i(x0 \\notin log0)", "1"),
    ("AHFreshBound", "invalid-output-admitted-fresh", "0<=outlen<=raw_xof_max_output /\\ ah_fresh_full input log", "ah_fresh_full input log"),
    ("AHActualReduction", "actual-H-reintroduces-old-record", "proc h=ROH.get", "proc h=SimLoggedH(SimHActual).get"),
    ("AHActualReduction", "actual-raw-reintroduces-old-record", "proc raw=FOGRaw(G).get", "proc raw=SimRaw(G,SimHActual).get"),
    ("AHActualReduction", "actual-transcript-not-list-adversary", "AHActualPhase(S,A,SecGLogged(FOGActual)).run(pk,ct,key)", "SecPhase(A,SecGLogged(FOGActual)).run(pk,ct,key)"),
    ("AHCallbacks", "state-view-context-lost", "hist_rep st.`ah_rows log /\\ ah_context st=(pk,suffix,star)", "hist_rep st.`ah_rows log"),
    ("AHCallbacks", "snapshot-frame-lost", "res=st /\\ view(glob S)=st", "res=st"),
    ("AHRawCallbacks", "raw-domain-guard-lost", "!(0<=n0<=raw_xof_max_output) \\/ forall x,decode_typed input0<>Some(H x)", "true"),
    ("AHCoupling", "adaptive-robust-losslessness-lost", "islossless D.decap=>islossless A(H,D).guess", "islossless A(H,D).guess"),
    ("AHCoupling", "coupling-good-branch-unconditional", "!SimBad.corr{1}=> ={res,glob A}", "true=> ={res,glob A}"),
    ("AHCPABound", "distinct-H-budget-premise-lost", "0<=qC=>hoare[CPAPhase(A).run:true ==>fsize SimHistory.h<=qC]=>", "0<=qC=>"),
    ("AHFinal", "fresh-store-is-global", "local module AHPrivateStore : AHStore = {", "module AHPrivateStore : AHStore = {"),
    ("AHFinal", "fresh-store-does-not-call-concrete-put", "updated<@HistTable.put(input,hout,st.`ah_rows);", "updated<-(hist_put input hout st.`ah_rows,0,0);"),
    ("AHFinal", "wrong-final-actual-witness", "exists (AHActual_DI(AHPrivateStore,A))", "exists (AH_DI(AHPrivateStore,A))"),
    ("AHFinal", "witnesses-chosen-after-memory", "exists(DI<:OWNTRUAdversary)(DO<:OWNTRUAdversary)(CO<:OWRLWEAdversary),", "forall &n, exists(DI<:OWNTRUAdversary)(DO<:OWNTRUAdversary)(CO<:OWRLWEAdversary),"),
    ("AHFinal", "adaptive-loss-scaled-by-key-acceptance", "+2%r*(qC%r/(2%r^353)).", "+2%r*(qC%r/(2%r^353))/ow_alpha_g."),
]


def current_sources():
    return {p.stem.removeprefix("NTRUPlus768"): p.read_text() for p in policy.PROOF.glob("*.ec")}


def final_scope(text):
    clean = policy.without_comments(text)
    declarations = list(re.finditer(r"\bdeclare\s+module\s+A\s*<:\s*CCAExtendedAdversary\s*(\{[^}]*\})\s*\.", clean))
    stores = list(re.finditer(r"\blocal\s+module\s+AHPrivateStore\s*:\s*AHStore\s*=\s*\{", clean))
    policy.require(len(declarations) == len(stores) == 1, "final needs one original A and one concrete local store")
    policy.require(policy.compact(declarations[0].group(1)) == scope_controls.original_adversary_restriction(),
                   "final original A restrictions changed")
    policy.require(declarations[0].end() < stores[0].start(), "private store is not fresh after A declaration")
    policy.require(not re.search(r"\bAHPrivateStore\b", clean[:declarations[0].start()]), "store exists before original A")
    final = re.search(r"\blemma\s+" + scope_controls.FINAL_THEOREM + r"\s*:(.*?)\bproof\.(.*?)\bqed\.", clean, re.S)
    if final:
        policy.require(policy.compact(final.group(1)) == policy.compact(scope_controls.expected_final_goal()),
                       "final changed original premises, witness quantifiers or numerical transfer")
        choices = "exists" + "".join("(" + value + ")" for value in scope_controls.FINAL_WITNESSES) + "."
        policy.require(policy.compact(choices) in policy.compact(final.group(2)), "final did not choose the three actual fresh-store attackers")


def check(sources=None, *, require_complete=True):
    sources = current_sources() if sources is None else sources
    policy.require(sources and set(sources) <= ALLOWED, "unreviewed adaptive-history inventory")
    if require_complete:
        policy.require(FINAL_REQUIRED is not None, "final adaptive-history inventory is not approved")
        policy.require(set(sources) == FINAL_REQUIRED, "required adaptive-history mains are missing")
        policy.require(set(ORDERED) >= FINAL_REQUIRED, "semantic contracts await final review")
    checked = []
    for name, text in sources.items():
        policy.check_proof_text(text)
        policy.require(re.search(r"\blemma\s+\w+", policy.without_comments(text)), "adaptive source has no theorem")
        if name in ORDERED:
            policy.shared.ordered(policy.compact(text), ORDERED[name])
        if name == "AHFinal":
            final_scope(text)
        if name in {"AHCallbacks", "AHRawCallbacks", "AHCoupling"}:
            for declaration in re.findall(r"\blemma\s+\w+\b(.*?)\bproof\.", policy.without_comments(text), re.S):
                policy.require("SimPublic.count" not in policy.compact(declaration) and
                               "SecGHistory.queries" not in policy.compact(declaration),
                               "old-map/list coupling claims equal internal counters or G transcripts")
        if name in {"AHAdapter", "AHActualReduction"}:
            for module, body in _syntax.modules(text):
                policy.require(not re.search(r"\b(?:SimLookup|SimHistory|SimPublic)\b", body),
                               "actual list attacker executes or accesses legacy map state: " + module)
                checked.append({"source": name, "module": module, "scope": "actual-list-path"})
    return checked
