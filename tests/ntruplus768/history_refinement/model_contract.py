"""Source regressions and executable/specification boundaries, not proof results."""
import re
import policy
import executable_policy

REQUIRED = {"HistKey", "HistModel", "HistTable", "HistLookup", "HistOrder", "HistBuild", "HistBound", "HistCosts", "HistAverage"}

ORDERED = {
    "HistKey": [
        "module HistKey", "proc equal(x y:fo_h_input):bool*int",
        "same<-true;comparisons<-0;", "while(comparisons<128)",
        "if(comparisons<96)", "left_byte<-x.`1.[comparisons];right_byte<-y.`1.[comparisons];",
        "left_byte<-x.`2.[comparisons-96];right_byte<-y.`2.[comparisons-96];",
        "byte_equal<-(left_byte=right_byte);", "same<-same /\\ byte_equal;",
        "comparisons<-comparisons+1;", "return(same,comparisons);",
        "proc suffix(x y:W8.t Array32.t):bool*int", "while(comparisons<32)",
        "left_byte<-x.[comparisons];right_byte<-y.[comparisons];",
        "byte_equal<-(left_byte=right_byte);", "proc cipher(x y:W8.t Array1152.t):bool*int",
        "while(comparisons<1152)", "left_byte<-x.[comparisons];right_byte<-y.[comparisons];",
        "byte_equal<-(left_byte=right_byte);",
        "lemma hist_key_spec", "res.`1=(x0=y0) /\\ res.`2=128",
        "lemma hist_key_correct", "res.`1=(x0=y0) /\\ res.`2=128]=1%r",
        "lemma hist_key_indexed_read_count", "2*res.`2=256",
        "lemma hist_suffix_correct", "res.`1=(x0=y0) /\\ res.`2=32]=1%r",
        "lemma hist_cipher_correct", "res.`1=(x0=y0) /\\ res.`2=1152]=1%r",
    ],
    "HistModel": [
        "type hist_entry = fo_h_input * W8.t Array224.t", "type hist_table = hist_entry list",
        "op [opaque] hist_rep", "hist_unique xs /\\ ofassoc xs=m",
        "op [opaque] hist_put", "(x,y)::hist_keep x xs",
        "lemma hist_put_get", "if k=x then Some y else hist_get k xs",
        "lemma hist_rep_put", "hist_rep(hist_put x y xs)m.[x<-y]",
        "lemma hist_rep_size", "size xs=fsize m", "lemma hist_rep_empty",
    ],
    "HistLookup": [
        "module HistCipherOption", "match candidate with", "None => {}",
        "Some value => {(same,compared)<@HistKey.cipher(value,ct);}", "return(same,compared);",
        "module HistLookup(G:FOGPort)", "(matched,n)<@HistKey.suffix(entry.`1.`2,suffix)",
        "candidate<@SimEncrypt(G).run(pk,entry.`1.`1,entry.`2);encrypted<-1;",
        "(matched,n)<@HistCipherOption.equal(candidate,ct)",
        "answer<-Some(payload_shared_key entry.`2)",
        "proc run(xs:hist_table,pk:W8.t Array1152.t,suffix:W8.t Array32.t,",
        "(blocked,n)<@HistCipherOption.equal(cstar,ct)", "if(!blocked)", "todo<-xs;",
        "while(todo<>[] /\\ answer=None)", "entry<-head hist_lookup_default todo;todo<-behead todo;visited<-visited+1;",
        "(answer,e,b)<@check(entry,pk,suffix,ct)", "encrypted<-encrypted+e;compared<-compared+b;",
        "return(answer,visited,encrypted,compared);",
    ],
    "HistTable": [
        "module HistKeep", "todo<-xs;kept<-[];visits<-0;comparisons<-0;", "while(todo<>[])",
        "entry<-head (x,hist_zero_value) todo;todo<-behead todo;", "cmp<@HistKey.equal(entry.`1,x);",
        "visits<-visits+1;comparisons<-comparisons+cmp.`2;", "if(!cmp.`1){kept<-entry::kept;}",
        "module HistReverse", "while(todo<>[])", "output<-entry::output;visits<-visits+1;",
        "module HistTable", "proc get", "while(todo<>[] /\\ answer=None)",
        "cmp<@HistKey.equal(entry.`1,x);", "if(cmp.`1){answer<-Some entry.`2;}",
        "proc put", "kept<@HistKeep.run(x,xs);", "ordered<@HistReverse.run((x,y),kept.`1);",
        "output<-(x,y)::ordered.`1;visits<-kept.`2+ordered.`2;", "return(output,visits,kept.`3);",
        "lemma hist_table_put_spec", "res.`2=size xs0+size(hist_keep x0 xs0) /\\ res.`3=128*size xs0",
        "lemma hist_table_get_refinement", "hist_rep xs0 m0=>",
        "lemma hist_table_put_refinement", "hist_rep xs0 m0=>",
        "hist_rep res.`1 m0.[x0<-y0]", "0<=res.`2<=2*size xs0 /\\ res.`3=128*size xs0",
    ],
    "HistOrder": [
        "op [opaque] hist_bad_entries", "Some e.`1<>ex /\\ fo_base_bad w g e.`1.`1 e.`2",
        "lemma hist_lookup_result_order", "pke_key_relation w=>hist_rep xs log=>sim_matching_good w g log ct=>",
        "lemma hist_lookup_order_good", "pke_key_relation w=>hist_rep xs log=>fo_hcache_good w g None log=>",
        "lemma hist_lookup_order_challenge", "pke_key_relation w=>hist_rep xs log=>sim_log_included log table=>",
        "fo_hcache_good w g ex log=>fo_challenge_invariant w g ex hs cs table=>",
        "lemma hist_lookup_disagreement", "hist_bad_entries w g ex xs",
    ],
    "HistBuild": [
        "module HistBuild", "hout<@ROH.get(input);", "updated<@HistTable.put(input,hout,rows);",
        "rows<-updated.`1;", "bad<-bad \\/ fo_base_bad w g input.`1 hout;", "return(rows,bad);",
        "ROH.init();todo<-qs;rows<-[];bad<-false;", "while(todo<>[])",
        "out<@step(w,g,rows,bad,input);", "rows<-out.`1;bad<-out.`2;",
    ],
    "HistBound": [
        "module HistProofMonitor", "bad<-false;n<-0;ROH.init();",
        "hout<@ROH.get(input);", "bad<-bad \\/ fo_base_bad w g input.`1 hout;", "n<-n+1;",
        "module HistProofExperiment", "HistProofMonitor.init(w0,g0);todo<-qs;",
        "hout<@HistProofMonitor.get(input)", "lemma hist_proof_get_ll",
        "lemma hist_proof_get_bad", "!HistProofMonitor.bad /\\ fo_hcache_good w0 g0 None ROH.m",
        "HistProofMonitor.bad]<=(fo_error w0 g0)",
        "lemma hist_build_bad_bound", "Pr[HistBuild.run(w0,g0,qs0)@&m:res.`2] <= (size qs0)%r*fo_error w0 g0",
        "module HistLookupAfterBuild", "ROG.m<-gm;", "built<@HistBuild.run(w,g,qs);",
        "SimHistory.h<-ROH.m;", "if(which)",
        "out<@HistLookup(FOGActual).run(built.`1,w.`kg_pk,complete_sk_suffix w.`kg_sk,None,ct);",
        "reply<@SimLookup(FOGActual).decap(ct);", "return(reply,built.`2);",
    ],
    "HistCosts": [
        "op hist_build_visit_bound (q:int) = q*(q-1)", "op hist_build_byte_bound (q:int) = 64*q*(q-1)",
        "module HistBuildPublic", "proc run(queries:fo_h_input list):hist_table*int*int*int",
        "ROH.init();todo<-queries;rows<-[];", "visits<-0;comparisons<-0;requests<-0;",
        "while(todo<>[])", "input<-head hist_public_zero_input todo;todo<-behead todo;",
        "hout<@ROH.get(input);", "updated<@HistTable.put(input,hout,rows);", "rows<-updated.`1;",
        "visits<-visits+updated.`2;", "comparisons<-comparisons+updated.`3;", "requests<-requests+1;",
        "return(rows,visits,comparisons,requests);",
        "lemma hist_public_build_correct", "0<=res.`2<=hist_build_visit_bound(size qs0)",
        "0<=res.`3<=hist_build_byte_bound(size qs0)", "res.`4=size qs0]=1%r",
        "lemma hist_public_build_projection", "equiv[HistBuildPublic.run ~ HistBuild.run:",
        "queries{1}=qs{2} ==>res{1}.`1=res{2}.`1 /\\ ={ROH.m}",
        "op hist_public_comparison_bound q = hist_build_byte_bound q+1184*q+1152",
        "module HistPublicLookup", "proc run(pk:W8.t Array1152.t,suffix:W8.t Array32.t,qs:fo_h_input list,ct:W8.t Array1152.t)",
        "built<@HistBuildPublic.run(qs);", "out<@HistLookup(FOGActual).run(built.`1,pk,suffix,None,ct);",
        "return(out.`1,built.`2+out.`2,built.`3+out.`4,built.`4,out.`3);",
        "lemma hist_public_lookup_bounds", "0<=res.`2<=size qs0*size qs0",
        "0<=res.`3<=hist_public_comparison_bound(size qs0)", "res.`4=size qs0 /\\ 0<=res.`5<=size qs0",
        "lemma hist_public_lookup_projection", "equiv[HistPublicLookup.run ~ HistLookupAfterBuild.run:",
        "ROG.m{1}=gm{2} /\\ which{2} ==>res{1}.`1=res{2}.`1 /\\ ={ROG.m,ROH.m}",
    ],
    "HistAverage": [
        "module HistAverageKernel", "out<@HistLookupAfterBuild.run(input.`1.`1.`1,acwc2_gfun input.`1.`3,",
        "acwc2_g_cache input.`1.`3,input.`2,input.`3,input.`4);", "return input.`5 out.`1;",
        "lemma hist_average_kernel_distance", "fo_setup_valid s=>",
        "hist_lookup_after_build_distance s.`1.`1 (acwc2_gfun s.`3)",
        "lemma hist_lookup_setup_average", "(size qs)%r/(2%r^353)",
        "fo_setup_law_support &m witness s hs", "sim_setup_distance_average &m K0 K1",
        "module HistAverageExperiment", "s<@FOSetupSource.guess(witness);",
        "win<@HistAverageKernel.guess((s,qs,ct,which,event));",
        "module HistAveragePublicKernel", "ROG.m<-acwc2_g_cache input.`1.`3;",
        "out<@HistPublicLookup.run(input.`1.`1.`1.`kg_pk,complete_sk_suffix input.`1.`1.`1.`kg_sk,input.`2,input.`3);",
        "return input.`4 out.`1;", "module HistAveragePublicExperiment", "s<@FOSetupSource.guess(witness);",
        "win<@HistAveragePublicKernel.guess((s,qs,ct,event));",
        "lemma hist_public_lookup_setup_distance", "hist_average_public_experiment_projection",
        "hist_lookup_setup_experiment_distance qs ct event &m",
    ],
}

AVERAGE_DECLARATION = '''qs ct event &m :
 `|mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness)@&m:res=s]))
    (fun s=>mk(fun b=>Pr[HistAverageKernel.guess((s,qs,ct,true,event))@&m:res=b])))true-
   mu1(dlet(mk(fun s=>Pr[FOSetupSource.guess(witness)@&m:res=s]))
    (fun s=>mk(fun b=>Pr[HistAverageKernel.guess((s,qs,ct,false,event))@&m:res=b])))true|
 <=(size qs)%r/(2%r^353).'''
PUBLIC_AVERAGE_DECLARATION = '''qs ct event &m :
 `|Pr[HistAveragePublicExperiment.run(qs,ct,event)@&m:res]-
   Pr[HistAverageExperiment.run(qs,ct,false,event)@&m:res]|
 <=(size qs)%r/(2%r^353).'''

MUTATIONS = [
    ("HistKey", "short-key-comparison", "while(comparisons<128)", "while(comparisons<96)"),
    ("HistKey", "early-stop-after-mismatch", "while(comparisons<128)", "while(comparisons<128 /\\ same)"),
    ("HistKey", "whole-key-equality-hidden", "byte_equal<-(left_byte=right_byte);", "byte_equal<-(x=y);"),
    ("HistKey", "key-comparison-counter-omitted", "comparisons<-comparisons+1;", "comparisons<-comparisons;"),
    ("HistKey", "wrong-suffix-offset", "x.`2.[comparisons-96]", "x.`2.[comparisons]"),
    ("HistKey", "short-suffix-comparison", "while(comparisons<32)", "while(comparisons<31)"),
    ("HistKey", "short-ciphertext-comparison", "while(comparisons<1152)", "while(comparisons<1151)"),
    ("HistModel", "representation-loses-uniqueness", "hist_unique xs /\\ ofassoc xs=m", "ofassoc xs=m"),
    ("HistModel", "put-keeps-obsolete-key", "(x,y)::hist_keep x xs", "(x,y)::xs"),
    ("HistModel", "size-not-tied-to-map", "size xs=fsize m", "0<=size xs"),
    ("HistTable", "put-keeps-equal-old-entries", "if(!cmp.`1){kept<-entry::kept;}", "if(cmp.`1){kept<-entry::kept;}"),
    ("HistTable", "table-abstract-key-comparison", "cmp<@HistKey.equal(entry.`1,x);", "cmp<-(entry.`1=x,1);"),
    ("HistTable", "put-omits-order-restoration", "ordered<@HistReverse.run((x,y),kept.`1);", "ordered<-(kept.`1,0);"),
    ("HistTable", "put-reverse-visits-not-counted", "visits<-kept.`2+ordered.`2;", "visits<-kept.`2;"),
    ("HistLookup", "whole-cipher-comparison-substitution", "(same,compared)<@HistKey.cipher(value,ct);", "same<-(value=ct);compared<-1;"),
    ("HistLookup", "real-reencryption-removed", "candidate<@SimEncrypt(G).run(pk,entry.`1.`1,entry.`2);", "candidate<-None;"),
    ("HistLookup", "challenge-comparison-removed", "(blocked,n)<@HistCipherOption.equal(cstar,ct);", "blocked<-false;n<-0;"),
    ("HistLookup", "lookup-input-map-enumeration", "todo<-xs;", "todo<-elems(fdom m);"),
    ("HistLookup", "lookup-call-count-lost", "encrypted<-encrypted+e;", "encrypted<-encrypted;"),
    ("HistOrder", "unconditional-order-independence", "pke_key_relation w=>hist_rep xs log=>sim_matching_good w g log ct=>", "pke_key_relation w=>hist_rep xs log=>"),
    ("HistOrder", "challenge-invariant-lost", "fo_hcache_good w g ex log=>fo_challenge_invariant w g ex hs cs table=>", "fo_hcache_good w g ex log=>"),
    ("HistBuild", "builder-bypasses-actual-ROH", "hout<@ROH.get(input);", "hout<$uniform224;"),
    ("HistBuild", "builder-bypasses-concrete-put", "updated<@HistTable.put(input,hout,rows);", "updated<-(hist_put input hout rows,0,0);"),
    ("HistBuild", "monitor-not-sticky", "bad<-bad \\/ fo_base_bad w g input.`1 hout;", "bad<-fo_base_bad w g input.`1 hout;"),
    ("HistBound", "cached-good-precondition-lost", "!HistProofMonitor.bad /\\ fo_hcache_good w0 g0 None ROH.m", "!HistProofMonitor.bad"),
    ("HistCosts", "public-counter-omitted", "requests<-requests+1;", "requests<-requests;"),
    ("HistCosts", "public-builder-replaced-by-monitor", "hout<@ROH.get(input);", "hout<@HistProofMonitor.get(input);"),
    ("HistCosts", "public-byte-count-not-returned", "return(rows,visits,comparisons,requests);", "return(rows,visits,0,requests);"),
    ("HistCosts", "public-lookup-concrete-call-lost", "out<@HistLookup(FOGActual).run(built.`1,pk,suffix,None,ct);", "out<-(None,0,0,0);"),
    ("HistCosts", "public-total-comparisons-use-wrong-field", "built.`3+out.`4", "built.`3+out.`3"),
    ("HistCosts", "prepared-cache-projection-premise-lost", "ROG.m{1}=gm{2} /\\ which{2} ==>", "which{2} ==>"),
    ("HistCosts", "public-hidden-G-map-installation", "built<@HistBuildPublic.run(qs);", "ROG.m<-gm;built<@HistBuildPublic.run(qs);"),
    ("HistAverage", "average-actual-call-removed", "out<@HistLookupAfterBuild.run", "out<@FakeKernel.run"),
    ("HistAverage", "pointwise-valid-setup-premise-lost", "fo_setup_valid s=>", "true=>"),
    ("HistAverage", "average-unsupported-strengthening", "(size qs)%r/(2%r^353)", "(size qs)%r/(2%r^354)"),
    ("HistAverage", "average-extra-bound-premise", "lemma hist_lookup_setup_average qs ct event &m :", "lemma hist_lookup_setup_average qs ct event &m : false=>"),
    ("HistAverage", "public-average-actual-lookup-call-lost", "out<@HistPublicLookup.run", "out<@FakeLookup.run"),
    ("HistAverage", "public-average-no-actual-setup", "s<@FOSetupSource.guess(witness);", "s<-witness;"),
    ("HistAverage", "public-average-extra-distance-premise", "lemma hist_public_lookup_setup_distance qs ct event &m :", "lemma hist_public_lookup_setup_distance qs ct event &m : false=>"),
]


def current_sources():
    return {p.stem.removeprefix("NTRUPlus768"): p.read_text() for p in policy.PROOF.glob("*.ec")}


def check(sources=None, *, require_complete=True):
    sources = current_sources() if sources is None else sources
    policy.require(sources and set(sources) <= REQUIRED, "unreviewed history proof inventory")
    if require_complete:
        policy.require(set(sources) == REQUIRED, "required history mains are missing")
        policy.require(set(ORDERED) == REQUIRED, "per-file semantic contracts await review")
    for name, text in sources.items():
        policy.check_proof_text(text)
        policy.require(re.search(r"\blemma\s+\w+", policy.without_comments(text)), "history source has no theorem")
        if name in ORDERED:
            policy.shared.ordered(policy.compact(text), ORDERED[name])
        if name == "HistAverage":
            for target, expected in (("hist_lookup_setup_average", AVERAGE_DECLARATION),
                                     ("hist_public_lookup_setup_distance", PUBLIC_AVERAGE_DECLARATION)):
                statements = re.findall(r"\blemma\s+" + target + r"\b(.*?)\bproof\.",
                                        policy.without_comments(text), re.S)
                policy.require(len(statements) == 1 and policy.compact(statements[0]) == policy.compact(expected),
                               "average changes actual setup/kernel law or adds a premise: " + target)
    return executable_policy.check(sources)
