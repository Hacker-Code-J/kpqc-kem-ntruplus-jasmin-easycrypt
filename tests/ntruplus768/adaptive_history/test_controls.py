#!/usr/bin/env python3
"""Trust, semantic EOF, negative-diagnostic and reduction-interface controls."""
import json
import policy
import model_contract
import scope_controls


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
    rejects("unreviewed-main", lambda: model_contract.check({**sources, "AHExtra": "lemma x : true. proof. trivial. qed."}, require_complete=False))
    for key, label, old, new in model_contract.MUTATIONS:
        if key not in sources:
            continue
        compact = policy.compact(sources[key])
        old, new = policy.compact(old), policy.compact(new)
        policy.require(old in compact, "mutation target absent: " + label)
        altered = {**sources, key: compact.replace(old, new, 1)}
        rejects(label, lambda altered=altered: model_contract.check(altered, require_complete=False))
    fixtures = scope_controls.fixture_manifest()
    policy.require(len(fixtures) == 11, "scope source inventory")
    item = {"error_line": 7, "diagnostic": "The module A can write Fresh.x"}
    own_scope = "/fresh/Scope.ec"
    diagnostic = "[critical] [" + own_scope + ": line 7 (2-8)] " + item["diagnostic"]
    scope_controls.own_scope_failure(diagnostic, own_scope, item)
    rejects("scope-negative-wrong-file", lambda: scope_controls.own_scope_failure(diagnostic, "/fresh/Other.ec", item))
    rejects("scope-negative-wrong-line", lambda: scope_controls.own_scope_failure(diagnostic.replace("line 7", "line 8"), own_scope, item))
    rejects("scope-negative-wrong-cause", lambda: scope_controls.own_scope_failure(diagnostic.replace(item["diagnostic"], "parse error"), own_scope, item))
    original = scope_controls.original_adversary_restriction()
    export_type = ("forall (A <: CCAExtendedAdversary " + original + "), "
                   "exists (DI<:Port)(DO<:Port)(CO<:Port), forall &m qE q0 qH qC, "
                   "Pr[CCAOriginalGame(A).run()@&m:res] <= 1%r.")
    scope_controls.validate_export_type(export_type)
    for label, altered in (
        ("export-private-restriction", export_type.replace(original, original[:-1] + ",-AHPrivateStore}")),
        ("export-memory-before-witness", export_type.replace("exists (DI", "forall &n, exists (DI")),
        ("export-budget-before-witness", export_type.replace("exists (DI", "forall qE, exists (DI")),
        ("export-only-two-witnesses", export_type.replace("(CO<:Port)", "")),
        ("export-extra-store-parameter", export_type.replace("exists (DI", "forall (S<:AHStore), exists (DI")),
    ):
        rejects(label, lambda altered=altered: scope_controls.validate_export_type(altered))
    for label, text in (
        ("admit", "lemma forged : false. proof. admit. qed."),
        ("new-native-proof", 'lemma native : true. proof. coq check "hidden" (). qed.'),
        ("axiom", "axiom game_distance : true."),
        ("checkoff", "pragma -check."),
        ("abstract-distance-law", "op distance : real."),
        ("abstract-type", "type hidden_setup."),
        ("abort", "lemma forged : false. proof. abort."),
        ("unclosed-comment", "(* hides the final proof"),
        ("unclosed-section", "section.\nlemma x : true. proof. trivial. qed."),
        ("unmatched-section-close", "end section."),
        ("section-hides-axiom", "section.\naxiom forged : false.\nend section."),
        ("section-hides-abstract-op", "section.\nop distance : real.\nend section."),
    ):
        rejects(label, lambda text=text: policy.check_proof_text(text))
    own = "/isolated/Main.ec"
    valid = "[critical] [" + own + ": line 18] cannot process [axiom] inside a proof script"
    policy.check_negative_diagnostic(valid, own)
    rejects("negative-wrong-main", lambda: policy.check_negative_diagnostic(valid, "/isolated/Other.ec"))
    rejects("negative-import-error", lambda: policy.check_negative_diagnostic(valid + " in external theory Imported", own))
    rejects("negative-unrelated-error", lambda: policy.check_negative_diagnostic(valid.replace("cannot process [axiom] inside a proof script", "unknown identifier"), own))
    source = "lemma final (A<:Port) : islossless A.run. proof. proc; auto. qed."
    sentinel = "\nlemma __adaptive_history_eof (A<:Port) : islossless A.run. proof. exact(final A). qed.\n"

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
