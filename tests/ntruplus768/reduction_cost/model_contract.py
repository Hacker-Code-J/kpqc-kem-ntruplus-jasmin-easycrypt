"""Source regressions for call-count scope; not substitutes for EC proofs."""
import re
import policy

REQUIRED = {"CostExtract", "CostLookup", "CostRaw", "CostBounds", "CostProjection", "CostFinal"}
OPTIONAL = set()

PROJECTION_THEOREMS = (
    "cost_adversary_projection", "cost_sec_phase_projection", "cost_sec_transcript_projection",
    "cost_inj_reducer_projection", "cost_ow_reducer_projection",
    "cost_inj_aux_projection", "cost_ow_aux_projection",
)
ADVERSARY_BINDER = "(A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SimPublic,-SimHistory,-SecGHistory,-SecGMark})"
PHYSICAL_RESULT = "={res,glob A,ROE.m,ROF.m,ROG.m,ROH.m,glob RawXOFStreams,glob SimPublic,SimHistory.h,SecGHistory.queries}"
FINAL_PROJECTION_THEOREMS = (
    "cost_inj_ntru_real_probability", "cost_inj_ntru_uniform_probability",
    "cost_ow_ntru_real_probability", "cost_ow_ntru_uniform_probability", "cost_rlwe_probability",
)
REDUCER_REPLACEMENTS = (
    ("INJNTRUReduction(SecINJAuxAdapter(SecINJReducer(A)))", "CostINJNTRU(A)"),
    ("OWNTRUReduction(SecOWAuxAdapter(SecOWReducer(A)))", "CostOWNTRU(A)"),
    ("OWRLWESolver(SecOWAuxAdapter(SecOWReducer(A)))", "CostRLWE(A)"),
)

ORDERED = {
    "CostExtract": [
        "module CostExtract =", "todo<-queries;answer<-None;visited<-0;",
        "while(todo<>[] /\\ answer=None)", "candidate<@SecCandidate.run(pk,ct,query);",
        "visited<-visited+1;", "return (answer,visited);",
        "lemma cost_extract_projection", "res{1}.`1=res{2}",
        "lemma cost_extract_visits", "res.`2=cost_first_visits",
        "lemma cost_extract_correct", "0<=res.`2<=size queries0",
    ],
    "CostLookup": [
        "module CostLookup(G:FOGPort)", "SimPublic.count<-SimPublic.count+1;",
        "star<-SimPublic.cstar;", "visited<-0;encrypted<-0;",
        "if(star<>Some ct)", "log<-SimHistory.h;", "todo<-elems(fdom log);",
        "while(todo<>[] /\\ answer=None)", "visited<-visited+1;",
        "if(input.`2=suffix)", "candidate<@SimEncrypt(G).run(pk,input.`1,hout);",
        "encrypted<-encrypted+1;", "return(answer,visited,encrypted);",
        "lemma cost_lookup_projection", "res{1}.`1=res{2}",
        "lemma cost_lookup_bounds", "0<=res.`3", "res.`3<=res.`2",
        "res.`2<=size(elems(fdom log0))", "lemma cost_lookup_lossless",
        "islossless G.get=>islossless CostLookup(G).decap",
        "lemma cost_lookup_g_calls", "size SecGHistory.queries=n0+res.`3",
    ],
    "CostBounds": [
        "op cost_scan_valid", "0<=s.`cs_encryptions",
        "s.`cs_encryptions<=s.`cs_visits", "s.`cs_visits<=s.`cs_history",
        "op cost_trace_valid", "cost_scan_valid s /\\ s.`cs_history<=h",
        "lemma cost_trace_call_bound", "0<=h=>size xs<=d=>cost_trace_valid h xs=>",
        "cost_visits xs<=d*h", "lemma cost_trace_extraction_bound",
        "0<=h=>0<=g=>size xs<=d=>cost_trace_valid h xs=>",
        "0<=e<=g+cost_encryptions xs=>", "e<=g+d*h",
        "cost_visits xs+e<=g+2*d*h", "lemma cost_trace_weighted_calls",
        "0<=h=>0<=g=>0<=cenc=>0<=cext=>size xs<=d=>",
        "lemma cost_lookup_measurement", "hoare[CostLookup(G).decap:SimHistory.h=log0 ==>",
        "cost_scan_valid {|cs_history=size(elems(fdom log0));cs_visits=res.`2;cs_encryptions=res.`3|}",
        "lemma cost_extract_trace_budget", "0<=h=>0<=g=>size xs<=d=>cost_trace_valid h xs=>",
        "size qs=g+cost_encryptions xs=>", "hoare[CostExtract.run:",
        "pk=pk0 /\\ ct=ct0 /\\ excluded=excluded0 /\\ queries=qs ==>",
        "res.`2<=g+d*h /\\ cost_visits xs+res.`2<=g+2*d*h",
        "conseq(cost_extract_bounds pk0 ct0 excluded0 qs)",
    ],
    "CostRaw": [
        "op cost_raw_input_bytes", "if 0<=outlen<=raw_xof_max_output then size input else 0",
        "module CostRawRunner(R:RawXOFPort)",
        "input_bytes<-cost_raw_input_bytes input outlen;",
        "answer<@R.get(input,outlen);",
        "output_bytes<-cost_raw_output_bytes answer;", "return(answer,input_bytes,output_bytes);",
        "module CostRaw(G:FOGPort,H:SimHPort) = CostRawRunner(SimRaw(G,H))",
        "lemma cost_raw_ll", "islossless G.get=>islossless H.get=>islossless CostRaw(G,H).get",
        "lemma cost_raw_runner_projection", "={input,outlen,glob R} ==>res{1}.`1=res{2} /\\ ={glob R}",
        "lemma cost_raw_projection", "res{1}.`1=res{2}",
        "lemma cost_raw_bytes_exact", "res.`3=(if 0<=outlen0<=raw_xof_max_output then outlen0 else 0)",
        "lemma cost_raw_zero", "res=(Some [],size input0,0)",
        "lemma cost_raw_one_call_exceeds", "nseq (B+1) W8.zero,0",
        "res.`1=Some [] /\\ B<res.`2 /\\ res.`3=0",
        "lemma cost_raw_zero_h_record", "(H<:SimHPort {-SimHistory})",
        "input=raw_query(H x0) /\\ outlen=0", "SimHistory.h=log0.[x0<-hout]",
    ],
    "CostProjection": [
        "module CostExtractPort", "out<@CostExtract.run(pk,ct,excluded,queries);return out.`1;",
        "module CostRawReply(G:FOGPort,H:SimHPort)",
        "out<@CostRaw(G,H).get(input,outlen);return out.`1;",
        "module CostOracles(G:FOGPort,H:SimHPort)",
        "proc e=SharedCCAOracles.e", "proc f=SharedCCAOracles.f",
        "proc g=SimOracles(G,H).g", "proc h=SimLoggedH(H).get", "proc raw=CostRawReply(G,H).get",
        "module CostSecPhase", "suffix<@ROF.get(pk);SimPublic.init(pk,suffix,ct);SimHistory.init();",
        "A(CostOracles(G,SimHActual),CostLookupReply(G)).guess(pk,ct,key)",
        "module CostSecTranscript", "SecGHistory.init();key<$uniform32;",
        "CostSecPhase(A,SecGLogged(FOGActual)).run(pk,ct,key)", "return SecGHistory.queries;",
        "module CostINJReducer", "code<$pke_psi1;r<$pke_psi1;ct<-pke_ciphertext pk code r;",
        "queries<@CostSecTranscript(A).run(pk,ct);", "out<@CostExtractPort.run(pk,ct,Some r,queries);",
        "return if out=None then (code,code,r,r) else (code,(oget out).`1,r,(oget out).`2);",
        "module CostOWReducer", "queries<@CostSecTranscript(A).run(pk,ct);",
        "out<@CostExtractPort.run(pk,ct,None,queries);", "return if out=None then sec_zero else (oget out).`1;",
        "module CostINJNTRU(A:CCAExtendedAdversary) = INJNTRUReduction(SecINJAuxAdapter(CostINJReducer(A)))",
        "module CostOWNTRU(A:CCAExtendedAdversary) = OWNTRUReduction(SecOWAuxAdapter(CostOWReducer(A)))",
        "module CostRLWE(A:CCAExtendedAdversary) = OWRLWESolver(SecOWAuxAdapter(CostOWReducer(A)))",
    ],
    "CostFinal": [
        "lemma cost_original_numerical", "CostINJNTRU(A)", "CostOWNTRU(A)", "CostRLWE(A)",
        "have previous:=sr_original_numerical A &m qE q0 qH qC",
        "cost_inj_ntru_real_probability A &m", "cost_inj_ntru_uniform_probability A &m",
        "cost_ow_ntru_real_probability A &m", "cost_ow_ntru_uniform_probability A &m",
        "cost_rlwe_probability A &m", "exact previous",
    ],
}

MUTATIONS = [
    ("CostExtract", "candidate-call-dropped", "candidate<@SecCandidate.run(pk,ct,query);", "candidate<-None;"),
    ("CostExtract", "extract-counter-skips-visits", "visited<-visited+1;", "visited<-visited;"),
    ("CostExtract", "extract-input-overwritten", "todo<-queries;", "todo<-[];"),
    ("CostLookup", "challenge-block-removed", "if(star<>Some ct)", "if(true)"),
    ("CostLookup", "history-snapshot-removed", "log<-SimHistory.h;", "log<-empty;"),
    ("CostLookup", "lookup-real-call-removed", "candidate<@SimEncrypt(G).run(pk,input.`1,hout);", "candidate<-None;"),
    ("CostLookup", "lookup-counter-skip", "encrypted<-encrypted+1;", "encrypted<-encrypted;"),
    ("CostLookup", "backend-losslessness-premise-removed", "islossless G.get=>islossless CostLookup(G).decap", "islossless CostLookup(G).decap"),
    ("CostBounds", "trace-precondition-removed", "0<=h=>size xs<=d=>cost_trace_valid h xs=>", "0<=h=>size xs<=d=>"),
    ("CostBounds", "extract-query-bound-removed", "0<=e<=g+cost_encryptions xs=>", "0<=e=>"),
    ("CostBounds", "combined-call-factor-lost", "cost_visits xs+e<=g+2*d*h", "cost_visits xs+e<=g+d*h"),
    ("CostBounds", "actual-lookup-profile-not-measured", "cs_visits=res.`2;cs_encryptions=res.`3", "cs_visits=0;cs_encryptions=0"),
    ("CostBounds", "actual-extract-transcript-link-lost", "size qs=g+cost_encryptions xs=>", "0<=size qs=>"),
    ("CostBounds", "actual-extract-source-call-bridge-lost", "conseq(cost_extract_bounds pk0 ct0 excluded0 qs)", "skip"),
    ("CostProjection", "cost-extract-port-dropped", "out<@CostExtract.run(pk,ct,excluded,queries);return out.`1;", "return None;"),
    ("CostProjection", "cost-raw-port-dropped", "out<@CostRaw(G,H).get(input,outlen);return out.`1;", "return None;"),
    ("CostProjection", "cost-lookup-callback-replaced", "CostLookupReply(G)).guess(pk,ct,key)", "SimLookup(G)).guess(pk,ct,key)"),
    ("CostProjection", "inj-excluded-randomness-lost", "CostExtractPort.run(pk,ct,Some r,queries)", "CostExtractPort.run(pk,ct,None,queries)"),
    ("CostProjection", "ow-default-result-replaced", "return if out=None then sec_zero else (oget out).`1;", "return sec_zero;"),
    ("CostProjection", "adversary-private-history-access", ADVERSARY_BINDER, ADVERSARY_BINDER.replace(",-SimHistory", "")),
    ("CostProjection", "adversary-state-observation-lost", PHYSICAL_RESULT, PHYSICAL_RESULT.replace(",glob A", "")),
    ("CostRaw", "zero-output-dispatch-skipped", "answer<@R.get(input,outlen);", "answer<-Some [];"),
    ("CostRaw", "raw-actual-backend-alias-lost", "CostRawRunner(SimRaw(G,H))", "CostRawRunner(G)"),
    ("CostRaw", "raw-input-size-artificially-capped", "then size input else 0", "then min 224 (size input) else 0"),
    ("CostRaw", "zero-output-input-cost-removed", "res=(Some [],size input0,0)", "res=(Some [],0,0)"),
    ("CostRaw", "raw-backend-losslessness-lost", "islossless G.get=>islossless H.get=>islossless CostRaw(G,H).get", "islossless CostRaw(G,H).get"),
    ("CostRaw", "H-history-frame-premise-lost", "(H<:SimHPort {-SimHistory})", "(H<:SimHPort)"),
    ("CostFinal", "final-uninstrumented-inj-algorithm", "CostINJNTRU(A)", "INJNTRUReduction(SecINJAuxAdapter(SecINJReducer(A)))"),
    ("CostFinal", "final-robust-losslessness-premise-lost", "islossless D.decap=>islossless A(H,D).guess", "islossless A(H,D).guess"),
    ("CostFinal", "final-conditioning-denominator-lost", "/ow_alpha_g", "/1%r"),
    ("CostFinal", "final-original-game-replaced", "Pr[CCAOriginalGame(A).run()@&m:res]", "Pr[FOFreshReencryptGame(A).run()@&m:res]"),
    ("CostFinal", "final-unsupported-numerical-strengthening", "(1%r/(2%r^244))", "(1%r/(2%r^245))"),
]


def current_sources():
    return {p.stem.removeprefix("NTRUPlus768"): p.read_text()
            for p in policy.PROOF.glob("*.ec")}


def check(sources=None, *, require_complete=True):
    sources = current_sources() if sources is None else sources
    policy.require(sources and set(sources) <= REQUIRED | OPTIONAL, "unreviewed cost proof inventory")
    if require_complete:
        policy.require(REQUIRED <= set(sources), "required cost mains are missing")
    for name, text in sources.items():
        policy.check_proof_text(text)
        code = policy.compact(text)
        policy.require(re.search(r"\blemma\s+\w+", policy.without_comments(text)), "cost source has no theorem")
        for marker in ORDERED.get(name, []):
            policy.require(policy.compact(marker) in code, "cost contract missing in " + name + ": " + marker)
        if name in ORDERED:
            policy.shared.ordered(code, ORDERED[name])
        if name == "CostProjection":
            clean = policy.without_comments(text)
            for target in PROJECTION_THEOREMS:
                matches = re.findall(r"\blemma\s+" + target + r"\b(.*?)\bproof\.", clean, re.S)
                policy.require(len(matches) == 1, "missing or duplicate projection: " + target)
                statement = policy.compact(matches[0])
                policy.require(policy.compact(ADVERSARY_BINDER) in statement,
                               "adversary state restriction changed: " + target)
                policy.require("==>" + policy.compact(PHYSICAL_RESULT) in statement,
                               "physical/adversary result frame changed: " + target)
            if require_complete:
                for target in FINAL_PROJECTION_THEOREMS:
                    policy.require(re.search(r"\blemma\s+" + target + r"\b", clean),
                                   "final probability projection is missing: " + target)
        if name == "CostFinal":
            previous = (policy.BASE / "kem_short_relation_bound/NTRUPlus768SRFinal.ec").read_text()
            def declaration(source, target):
                matches = re.findall(r"\blemma\s+" + target + r"\b(.*?)\bproof\.",
                                     policy.without_comments(source), re.S)
                policy.require(len(matches) == 1, "final theorem is missing or ambiguous: " + target)
                return policy.compact(matches[0])
            expected = declaration(previous, "sr_original_numerical")
            for old, new in REDUCER_REPLACEMENTS:
                policy.require(policy.compact(old) in expected, "original reducer expression changed")
                expected = expected.replace(policy.compact(old), policy.compact(new))
            policy.require(declaration(text, "cost_original_numerical") == expected,
                           "cost final changed original premises, game or numerical expression")

