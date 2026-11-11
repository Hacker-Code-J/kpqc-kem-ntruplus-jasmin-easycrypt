#!/usr/bin/env python3
"""Trust, semantic EOF, negative-diagnostic and reduction-interface controls."""
import json
import policy
import model_contract


def main():
    controls = []

    def rejects(label, action):
        try:
            action()
        except (ValueError, AssertionError, IndexError):
            controls.append({"label": label, "result": "EXPECTED_REJECTION"})
            return
        raise AssertionError("accepted negative control: " + label)

    sources = {key: path.read_text() for key, path in model_contract.SOURCES.items()}
    model_contract.check(sources)
    for key, label, old, new in model_contract.MUTATIONS:
        compact = policy.compact(sources[key])
        old, new = policy.compact(old), policy.compact(new)
        policy.require(old in compact, "mutation target absent: " + label)
        altered = {**sources, key: compact.replace(old, new, 1)}
        rejects(label, lambda altered=altered: model_contract.check(altered))
    for label, text in (
        ("admit", "lemma forged : false. proof. admit. qed."),
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
    sentinel = "\nlemma __acwc2_security_eof (A<:Port) : islossless A.run. proof. exact(final A). qed.\n"

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
