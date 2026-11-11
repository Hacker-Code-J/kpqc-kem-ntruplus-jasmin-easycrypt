"""Fresh-state compiler controls and a literal exported-theorem type guard."""
from pathlib import Path
import json
import re
import policy


def fixture_manifest():
    data = json.loads((policy.TEST / "scope-fixtures.json").read_text())
    policy.require(data.get("schema") == 1, "unknown scope fixture schema")
    fixtures = data.get("fixtures", [])
    policy.require(len(fixtures) == 11, "scope fixture inventory changed")
    paths = set()
    for item in fixtures:
        path = policy.TEST / item["source"]
        policy.require(path.parent == policy.TEST / "scope-fixtures" and path.suffix == ".ec",
                       "scope fixture outside reviewed directory")
        policy.require(path.is_file() and not path.is_symlink(), "missing/indirect scope fixture")
        policy.require(policy.sha(path.read_bytes()) == item["sha256"], "scope fixture changed")
        policy.check_proof_text(path.read_text())
        policy.require(path not in paths, "duplicate scope fixture")
        paths.add(path)
        if item["expected_failure"]:
            policy.require(item.get("diagnostic") and item.get("error_line", 0) > 0,
                           "scope rejection has no specific diagnostic")
    policy.require(paths == set((policy.TEST / "scope-fixtures").glob("*.ec")), "unreviewed scope fixture")
    policy.require(sum(item["expected_failure"] for item in fixtures) == 6, "scope outcome inventory changed")
    return fixtures


def own_scope_failure(text, path, item):
    policy.require("external theory" not in text.lower(), "scope negative failed in imported theory")
    match = re.search(r"\[critical\]\s*\[" + re.escape(str(path)) + r":\s*(?:line\s+)?" +
                      str(item["error_line"]) + r"\b[^\r\n]+", text)
    policy.require(match and item["diagnostic"] in match.group(), "scope negative failed at another site or cause")
    return match.group()


def printed_theorem(text, name):
    policy.require(re.fullmatch(r"[A-Za-z_]\w*", name), "invalid printed theorem name")
    clean = text.replace("\r", "\n")
    matches = re.findall(r"(?ms)^lemma\s+" + re.escape(name) + r"\s*:.*?(?=\n\s*\n)", clean)
    policy.require(len(matches) == 1, "missing or ambiguous exported theorem print")
    return matches[0].strip()


def original_adversary_restriction():
    source = (policy.BASE / "kem_short_relation_bound/NTRUPlus768SRFinal.ec").read_text()
    declaration = re.search(r"\blemma\s+sr_original_numerical\b(.*?)\bproof\.", policy.without_comments(source), re.S)
    policy.require(declaration, "original SR final declaration missing")
    matched = re.search(r"CCAExtendedAdversary\s*(\{[^}]*\})", declaration.group(1))
    policy.require(matched, "original A restriction absent")
    return policy.compact(matched.group(1))


FINAL_THEOREM = "ah_original_adaptive_history"
FINAL_WITNESSES = ["AHActual_DI(AHPrivateStore,A)", "AHActual_DO(AHPrivateStore,A)", "AHActual_CO(AHPrivateStore,A)"]


def expected_final_goal():
    source = (policy.BASE / "kem_short_relation_bound/NTRUPlus768SRFinal.ec").read_text()
    declaration = re.search(r"\blemma\s+sr_original_numerical\b(.*?)\bproof\.", policy.without_comments(source), re.S).group(1)
    tail = re.split(r"&m\s+qE\s+q0\s+qH\s+qC\s*:", declaration)
    policy.require(len(tail) == 2 and tail[1].strip().endswith("."), "original numerical declaration changed")
    goal = tail[1].strip()[:-1]
    substitutions = (
        ("INJNTRUReduction(SecINJAuxAdapter(SecINJReducer(A)))", "DI"),
        ("OWNTRUReduction(SecOWAuxAdapter(SecOWReducer(A)))", "DO"),
        ("OWRLWESolver(SecOWAuxAdapter(SecOWReducer(A)))", "CO"),
    )
    # Preserve lexical whitespace in generated EasyCrypt source.
    for old, new in substitutions:
        policy.require(old in goal, "original reduction expression changed")
        goal = goal.replace(old, new)
    return ("exists(DI<:OWNTRUAdversary)(DO<:OWNTRUAdversary)(CO<:OWRLWEAdversary),\n"
            "forall &m qE q0 qH qC,\n" + goal + "+2%r*(qC%r/(2%r^353)).")


def expected_export_type():
    return "forall (A <: CCAExtendedAdversary " + original_adversary_restriction() + "),\n" + expected_final_goal()


def validate_export_type(expected_type):
    code = policy.without_comments(expected_type).strip()
    policy.require(code.endswith("."), "exported type has no terminator")
    policy.require(not re.search(r"\b(?:lemma|proof|qed|section|module|axiom|pragma|admit)\b", code),
                   "exported type contains a command")
    policy.require(not re.search(r"\b(?:AHPrivateStore|AHFreshStore)\b", code), "private state escaped in exported type")
    restriction = re.search(r"CCAExtendedAdversary\s*(\{[^}]*\})", code)
    def restriction_items(value):
        items = [item.strip() for item in value.strip()[1:-1].split(",")]
        policy.require(all(re.fullmatch(r"-[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*", item) for item in items),
                       "invalid printed module restriction")
        policy.require(len(items) == len(set(items)), "duplicate printed module restriction")
        return set(items)
    policy.require(restriction and restriction_items(restriction.group(1)) ==
                   restriction_items(original_adversary_restriction()),
                   "exported A has different state restrictions from original SR final")
    policy.require(re.match(r"\s*forall\s*\(\s*A\b", code), "exported theorem must first quantify original A")
    existential = re.search(r"\bexists\b", code)
    memory = re.search(r"\bforall\s*&\w+", code)
    policy.require(existential and memory and existential.start() < memory.start(),
                   "reduction witnesses are not before all memories and budgets")
    policy.require(code[:existential.start()].count("<:") == 1,
                   "extra module parameter before reduction witnesses")
    groups = re.findall(r"\(\s*([A-Za-z_]\w*(?:\s+[A-Za-z_]\w*)*)\s*<:", code[existential.end():memory.start()])
    witnesses = [name for group in groups for name in group.split()]
    policy.require(len(witnesses) == 3 and len(set(witnesses)) == 3,
                   "exported theorem must choose exactly three module witnesses")
    policy.require(not re.search(r"\b(?:qE|q0|qH|qC)\b", code[:existential.start()]),
                   "budget quantified before reduction witnesses")
    policy.require("CCAOriginalGame(A)" in policy.compact(code), "original CCA game absent from exported theorem")
    return witnesses


def validate_export_spec(data):
    item = data.get("export_audit")
    policy.require(isinstance(item, dict), "actual exported-type audit awaits review")
    policy.require(item.get("source") in {x["source"] for x in data["mains"]}, "export audit source is not a main")
    policy.require(re.fullmatch(r"[A-Za-z_]\w*", item.get("theorem", "")), "invalid export theorem")
    policy.require(item["theorem"] == FINAL_THEOREM, "unexpected final export target")
    validate_export_type(item["expected_type"])
    policy.require(policy.compact(item["expected_type"]) == policy.compact(expected_export_type()),
                   "typed export differs from original premises and reviewed numerical transfer")
    policy.require(item.get("expected_printed_type"), "printed final type awaits actual export review")
    validate_export_type(item["expected_printed_type"])
    policy.require(item.get("preamble", "").strip(), "missing typed-probe import preamble")
    policy.check_proof_text(item["preamble"])
    policy.require(re.fullmatch(r"[\s\w.]+", item["preamble"]), "unexpected command syntax in export imports")
    policy.require(all(x.strip().startswith(("require import ", "import ", "from "))
                       for x in item["preamble"].split(".") if x.strip()), "export preamble is not imports only")
    policy.require(Path(item["source"]).stem in item["preamble"], "export probe does not import its actual main")
    source = policy.without_comments((policy.BASE / item["source"]).read_text())
    policy.require(re.search(r"(?m)^\s*lemma\s+" + re.escape(item["theorem"]) + r"\b", source),
                   "export theorem is not a public source declaration")
    witnesses = item.get("witness_terms", [])
    policy.require([policy.compact(x) for x in witnesses] == [policy.compact(x) for x in FINAL_WITNESSES],
                   "actual fresh-store witness list changed")
    for witness in witnesses:
        policy.require("AHPrivateStore" in witness and policy.compact(witness) in policy.compact(source),
                       "final concrete fresh-store witness missing")
    return item


def replay_fixtures(run, output, command):
    records = []
    for item in fixture_manifest():
        source = policy.TEST / item["source"]
        copied = Path(output) / "scope-inputs" / source.name
        copied.parent.mkdir(parents=True, exist_ok=True)
        copied.write_bytes(source.read_bytes())
        log = run("scope-" + source.stem, [*command, copied], item["expected_failure"], copied.parent)
        policy.require(policy.sha(copied.read_bytes()) == item["sha256"], "scope checked copy changed")
        record = {"source": str(source.relative_to(policy.ROOT)), "source_sha256": item["sha256"],
                  "checked_copy": str(copied), "checked_copy_sha256": item["sha256"], "log": str(log),
                  "result": "EXPECTED_REJECTION" if item["expected_failure"] else "PASS"}
        if item["expected_failure"]:
            record["diagnostic"] = own_scope_failure(Path(log).read_text(), copied, item)
        if item.get("printed_theorem"):
            observed = printed_theorem(Path(log).read_text(), item["printed_theorem"])
            policy.require(policy.compact(observed) == policy.compact(item["printed_statement"]),
                           "generic existential export changed")
            record["exported_type"] = observed
        records.append(record)
    return records


def replay_export(run, output, command, data):
    item = validate_export_spec(data)
    qualified = Path(item["source"]).stem + "." + item["theorem"]
    text = (item["preamble"].rstrip() + "\nprint " + qualified + ".\n" +
            "lemma __adaptive_history_exported_type\n" +
            " (A <: CCAExtendedAdversary " + original_adversary_restriction() + ") :\n" +
            expected_final_goal() + "\nproof. exact (" + qualified + " A). qed.\n")
    copied = Path(output) / "export-inputs" / "AdaptiveHistoryExport.ec"
    copied.parent.mkdir(parents=True)
    copied.write_text(text)
    expected_hash = policy.sha(copied.read_bytes())
    log = run("actual-exported-type", [*command, copied], cwd=copied.parent)
    observed = printed_theorem(Path(log).read_text(), item["theorem"])
    expected = "lemma " + item["theorem"] + ": " + item["expected_printed_type"]
    policy.require(policy.compact(observed) == policy.compact(expected), "actual exported theorem type drift")
    policy.require(policy.sha(copied.read_bytes()) == expected_hash, "export probe changed during check")
    return {"source": item["source"], "theorem": item["theorem"], "checked_copy": str(copied),
            "checked_copy_sha256": expected_hash, "printed_type": observed, "log": str(log), "result": "PASS"}
