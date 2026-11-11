#!/usr/bin/env python3
"""Trust, semantic EOF, negative-diagnostic and reduction-interface controls."""
import json
import policy
import model_contract
import executable_policy


def main():
    controls = []

    def rejects(label, action):
        try:
            action()
        except (ValueError, AssertionError, IndexError):
            controls.append({"label": label, "result": "EXPECTED_REJECTION"})
            return
        raise AssertionError("accepted negative control: " + label)

    sources = model_contract.current_sources()
    model_contract.check(sources, require_complete=False)
    for missing in ("HistKey", "HistLookup"):
        absent = {name: text for name, text in sources.items() if name != missing}
        rejects("required-main-missing-" + missing,
                lambda absent=absent: model_contract.check(absent))
    rejects("unreviewed-main", lambda: model_contract.check({**sources, "HistExtra": "lemma x : true. proof. trivial. qed."}, require_complete=False))
    for key, label, old, new in model_contract.MUTATIONS:
        if key not in sources:
            continue
        compact = policy.compact(sources[key])
        old, new = policy.compact(old), policy.compact(new)
        policy.require(old in compact, "mutation target absent: " + label)
        altered = {**sources, key: compact.replace(old, new, 1)}
        rejects(label, lambda altered=altered: model_contract.check(altered, require_complete=False))
    executable = '''module HistFixture = {
 proc test(x y:fo_h_input):bool = {
  var a,b:W8.t;var same:bool;
  a<-W8.zero;b<-W8.zero;same<-(a=b);return same;
 }
}.'''
    executable_policy.check({"HistKey": executable})
    # Mathematical map operations and full-key equality remain permitted in specs/proofs.
    executable_policy.check({"HistModel": "op spec xs = ofassoc(filter predT (rev xs)).\nlemma spec_eq (x y:fo_h_input):x=y=>x=y. proof. trivial. qed."})
    for label, expression in (
        ("FMap-lookup", "same<-(m.[x]=None);"),
        ("fdom-enumeration", "same<-(elems(fdom m)=[]);"),
        ("choice", "same<-choice predT;"),
        ("hidden-filter", "same<-(filter predT xs=[]);"),
        ("hidden-reverse", "same<-(rev xs=[]);"),
        ("whole-key-equality", "same<-(x=y);"),
        ("ideal-table-read", "same<-(ROH.m.[x]=None);"),
        ("spec-get-call", "same<-(hist_get x xs=None);"),
        ("hidden-membership", "same<-(x \\in xs);"),
        ("public-correctness-monitor", "same<-fo_base_bad w g msg hout;"),
    ):
        altered = executable.replace("same<-(a=b);", expression)
        rejects("executable-" + label, lambda altered=altered: executable_policy.check({"HistKey": altered}))
    alias = "op hidden x y = x=y.\n" + executable.replace("same<-(a=b);", "same<-hidden x y;")
    rejects("executable-local-spec-alias", lambda: executable_policy.check({"HistKey": alias}))
    stateful = executable.replace("module HistFixture = {", "module HistFixture = { var secret:int;")
    rejects("executable-new-global", lambda: executable_policy.check({"HistKey": stateful}))
    monitor = "module HistProofMonitor = { var w:keygen_witness var g:acwc2_g_function var bad:bool var n:int proc mark():unit={bad<-fo_base_bad w g msg hout;} }."
    executable_policy.check({"HistBound": monitor})
    rejects("proof-monitor-wrong-file", lambda: executable_policy.check({"HistKey": monitor}))
    rejects("proof-monitor-arbitrary-name", lambda: executable_policy.check({"HistBound": monitor.replace("HistProofMonitor", "HistOther")}))
    rejects("proof-monitor-extra-global", lambda: executable_policy.check({"HistBound": monitor.replace("var n:int", "var n:int var extra:int")}))
    comparison = "module HistLookupAfterBuild = { proc run():unit={ROG.m<-gm;SimHistory.h<-ROH.m;} }."
    executable_policy.check({"HistBound": comparison})
    rejects("proof-comparison-wrong-file", lambda: executable_policy.check({"HistLookup": comparison}))
    for label, text in (
        ("admit", "lemma forged : false. proof. admit. qed."),
        ("new-native-proof", 'lemma native : true. proof. coq check "hidden" (). qed.'),
        ("axiom", "axiom game_distance : true."),
        ("checkoff", "pragma -check."),
        ("abstract-distance-law", "op distance : real."),
        ("abstract-type", "type hidden_setup."),
        ("abort", "lemma forged : false. proof. abort."),
        ("unclosed-comment", "(* hides the final proof"),
    ):
        rejects(label, lambda text=text: policy.check_proof_text(text))
    own = "/isolated/Main.ec"
    valid = "[critical] [" + own + ": line 18] cannot process [axiom] inside a proof script"
    policy.check_negative_diagnostic(valid, own)
    rejects("negative-wrong-main", lambda: policy.check_negative_diagnostic(valid, "/isolated/Other.ec"))
    rejects("negative-import-error", lambda: policy.check_negative_diagnostic(valid + " in external theory Imported", own))
    rejects("negative-unrelated-error", lambda: policy.check_negative_diagnostic(valid.replace("cannot process [axiom] inside a proof script", "unknown identifier"), own))
    source = "lemma final (A<:Port) : islossless A.run. proof. proc; auto. qed."
    sentinel = "\nlemma __history_refinement_eof (A<:Port) : islossless A.run. proof. exact(final A). qed.\n"

    def validates(text):
        policy.check_sentinel("fixture", text, "final", ["A"], source_text=source)

    validates(sentinel)
    rejects("eof-forged-target", lambda: validates(sentinel.replace("exact(final", "exact(final_other")))
    rejects("eof-implicit-module-binder", lambda: validates(sentinel.replace("A<:Port", "A:Port")))
    rejects("eof-weakened-statement", lambda: validates(sentinel.replace("islossless A.run", "true")))
    rejects("eof-unfinished-sentinel", lambda: validates(sentinel.replace("qed.", "")))
    rejects("eof-changed-statement", lambda: validates(sentinel.replace("A.run.", "A.other.")))
    tail = "\nmodule Tail = {}.\n(* outer (* qed. *) qed. *)\n"
    original = source + tail
    policy.require(policy.completed_proof_text(original, sentinel) == source + sentinel + tail, "positive dropped trailing declarations")
    policy.require(policy.unfinished_proof_text(original, sentinel) == source.replace("qed.", sentinel) + tail, "negative dropped trailing declarations")
    rejects("negative-comment-closer", lambda: policy.unfinished_proof_text("(* qed. *)", sentinel))
    print(json.dumps({"status": "PASS", "count": len(controls), "controls": controls,
        "scope": "Source/interface regressions; these do not replace EasyCrypt proof checking."}))


if __name__ == "__main__":
    main()
