"""Pinned fresh-local fixtures and reviewed exported theorem checks."""
from pathlib import Path
import json,re
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


def validate_export_type(expected_type, witness_count=3):
    code=policy.without_comments(expected_type).strip()
    policy.require(code.endswith('.'),'export type has no terminator')
    policy.require(not re.search(r'\b(?:lemma|proof|qed|section|module|axiom|pragma|admit)\b',code),'command in export type')
    policy.require(not re.search(r'\b(?:RTPrivateStore|RTFreshStore)\b',code),'private runtime state escaped in export')
    restriction=re.search(r'CCAExtendedAdversary\s*(\{[^}]*\})',code)
    def items(raw):
        values=[x.strip() for x in raw[1:-1].split(',')]
        policy.require(len(values)==len(set(values)) and all(re.fullmatch(r'-[\w.]+',x) for x in values),'invalid A exclusion set')
        return set(values)
    policy.require(restriction and items(restriction.group(1))==items(original_adversary_restriction()),'export changes original A restrictions')
    policy.require(re.match(r'\s*forall\s*\(\s*A\b',code),'original A must be first')
    ex=re.search(r'\bexists\b',code);mem=re.search(r'\bforall\s*&\w+',code)
    policy.require(ex and mem and ex.start()<mem.start(),'witnesses must precede memories/budgets')
    policy.require(code[:ex.start()].count('<:')==1,'extra module argument before fresh witnesses')
    policy.require(len(re.findall(r'\bforall\b',code[:ex.start()]))==1,'budget or memory quantified before witnesses')
    groups=re.findall(r'\(\s*([A-Za-z_]\w*(?:\s+[A-Za-z_]\w*)*)\s*<:',code[ex.end():mem.start()])
    names=[x for group in groups for x in group.split()]
    policy.require(len(names)==witness_count and len(set(names))==len(names),'wrong witness count')
    policy.require('CCAOriginalGame(A)' in policy.compact(code),'original CCA target absent')
    return names


def export_probe(item):
    preamble=item.get('preamble','').strip()
    policy.require(preamble and Path(item['source']).stem in preamble,'export probe must import its actual main')
    token=r'[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*'
    statement=re.compile(r'\s*(?:(?:from\s+'+token+r'\s+)?require\s+import|import)\s+'+token+r'(?:\s+'+token+r')*\s*\.')
    cursor=0
    while cursor<len(preamble):
        m=statement.match(preamble,cursor);policy.require(m,'export preamble contains a non-import command');cursor=m.end()
    outer=re.fullmatch(r'\s*forall\s*\(\s*A\s*<:\s*CCAExtendedAdversary\s*(\{[^}]*\})\s*\)\s*,(.*)',item['expected_type'],re.S)
    policy.require(outer,'unsupported reviewed outer A quantifier')
    qualified=Path(item['source']).stem+'.'+item['theorem']
    return (preamble+'\nprint '+qualified+'.\nlemma __runtime_bound_exported_type\n'
            +' (A <: CCAExtendedAdversary '+outer.group(1)+') :\n'+outer.group(2).strip()
            +'\nproof. exact ('+qualified+' A). qed.\n')


def validate_export_spec(data):
    item=data.get('export_audit')
    policy.require(isinstance(item,dict),'reviewed runtime final export is pending')
    policy.require(item.get('source') in {x['source'] for x in data['mains']},'export source not a checked main')
    policy.require(re.fullmatch(r'rt_[A-Za-z_]\w*',item.get('theorem','')),'invalid runtime export theorem')
    validate_export_type(item['expected_type'],item.get('module_witness_count',3))
    validate_export_type(item['expected_printed_type'],item.get('module_witness_count',3))
    policy.require(item.get('reviewed_statement_sha256')==policy.sha(policy.compact(item['expected_type']).encode()),'final literal statement lacks review digest')
    probe=export_probe(item);policy.check_proof_text(probe)
    source=policy.without_comments((policy.BASE/item['source']).read_text())
    policy.require(re.search(r'(?m)^\s*lemma\s+'+re.escape(item['theorem'])+r'\b',source),'export target is not a public source theorem')
    for private in re.findall(r'\blocal\s+module\s+(\w+)',source):
        policy.require(not re.search(r'\b'+re.escape(private)+r'\b',item['expected_printed_type']),'local module escaped exported type')
    return item


def replay_export(run,output,command,data):
    item=validate_export_spec(data)
    copied=Path(output)/'export-inputs/RuntimeBoundExport.ec';copied.parent.mkdir(parents=True)
    copied.write_text(export_probe(item));expected=policy.sha(copied.read_bytes())
    log=run('actual-exported-type',[*command,copied],cwd=copied.parent)
    observed=printed_theorem(Path(log).read_text(),item['theorem'])
    policy.require(policy.compact(observed)==policy.compact('lemma '+item['theorem']+': '+item['expected_printed_type']),'printed final theorem drift')
    policy.require(policy.sha(copied.read_bytes())==expected,'export probe changed during check')
    return {'source':item['source'],'theorem':item['theorem'],'checked_copy':str(copied),
            'checked_copy_sha256':expected,'printed_type':observed,'log':str(log),'result':'PASS'}
