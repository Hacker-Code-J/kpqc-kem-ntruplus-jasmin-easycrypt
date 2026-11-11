"""Conservative syntax gate for the reviewed executable fragment.

Specifications and proofs may use mathematical maps and extensional equality.
Concrete module bodies may not conceal these operations. This gate supplements
exact source pins and EasyCrypt checking; it is not a general EC parser.
"""
import re
import policy

PROOF_MONITORS = {("HistBuild", "HistBuild"), ("HistBound", "HistProofMonitor")}
GLOBAL_MONITORS = {("HistBound", "HistProofMonitor")}
PROOF_WRAPPERS = {("HistBound", "HistProofExperiment"), ("HistBound", "HistLookupAfterBuild"),
                  ("HistBound", "HistBuildBad"),
                  ("HistAverage", "HistAverageKernel"), ("HistAverage", "HistAverageExperiment"),
                  ("HistAverage", "HistAverageReified"), ("HistAverage", "HistAveragePublicKernel"),
                  ("HistAverage", "HistAveragePublicExperiment")}
IDEAL_STATE_WRAPPERS = {("HistBound", "HistLookupAfterBuild"), ("HistAverage", "HistAveragePublicKernel")}
LITERAL_CONSTANTS = {
    "hist_zero_value": "op [opaque] hist_zero_value : W8.t Array224.t = Array224.init(fun _=>W8.zero).",
    "hist_lookup_default": "op [opaque] hist_lookup_default : hist_entry = ((Array96.init(fun _=>W8.zero),Array32.init(fun _=>W8.zero)),hist_zero_value).",
    "hist_public_zero_input": "op [opaque] hist_public_zero_input : fo_h_input = (Array96.init(fun _=>W8.zero),Array32.init(fun _=>W8.zero)).",
}
FORBIDDEN = re.compile(r"\b(?:FMap|fmap|fdom|fsize|elems|choiceb?|ofassoc|assoc|filter|rev|find|has|uniq|mem)\b|\\(?:notin|in)\b")
SPEC_NAMES = re.compile(r"\b(?:hist_(?:get|put|keep|rep|unique|keys)|fo_base_bad|acwc2_g_cache|acwc2_gfun)\b")


def balanced_end(code, start):
    policy.require(code[start] == "{", "module/procedure body has no opening brace")
    depth = 0
    for index in range(start, len(code)):
        if code[index] == "{":
            depth += 1
        elif code[index] == "}":
            depth -= 1
            if depth == 0:
                return index + 1
    raise ValueError("unclosed executable body")


def modules(text):
    code = policy.without_comments(text)
    result = []
    starts = list(re.finditer(r"\bmodule\s+(?!type\b)(\w+)\b", code))
    for index, match in enumerate(starts):
        limit = starts[index + 1].start() if index + 1 < len(starts) else len(code)
        # A new lemma/declaration ends an alias header; never search into proof text.
        next_decl = re.search(r"(?m)^\s*(?:lemma|op|type|theory|require|import)\b", code[match.end():limit])
        if next_decl:
            limit = match.end() + next_decl.start()
        opening = re.search(r"=\s*\{", code[match.end():limit])
        if opening is None:
            continue  # Module aliases contain no executable expressions.
        start = match.end() + opening.end() - 1
        end = balanced_end(code, start)
        result.append((match.group(1), code[start + 1:end - 1]))
    return result


def procedures(module_body):
    result = []
    offset = 0
    while True:
        match = re.search(r"\bproc\s+(\w+)\b", module_body[offset:])
        if match is None:
            break
        begin = offset + match.start()
        after = offset + match.end()
        next_proc = re.search(r"\bproc\s+\w+\b", module_body[after:])
        limit = after + next_proc.start() if next_proc else len(module_body)
        opening = re.search(r"=\s*\{", module_body[after:limit])
        if opening is None:
            offset = limit
            continue
        start = after + opening.end() - 1
        end = balanced_end(module_body, start)
        result.append((match.group(1), module_body[begin:start], module_body[start + 1:end - 1], begin, end))
        offset = end
    return result


def local_ops(sources):
    return {m.group(1) for text in sources.values() for m in re.finditer(
        r"(?m)^\s*op\s+(?:\[[^]]*\]\s*)?(\w+)\b", policy.without_comments(text))}


def scalar_names(header, body):
    names = set()
    for match in re.finditer(r"\b([A-Za-z_]\w*(?:\s*[, ]\s*[A-Za-z_]\w*)*)\s*:\s*(bool|int|W8\.t)\b", header + "\n" + body):
        # A byte-array type is not a scalar byte declaration.
        if match.group(2) == "W8.t" and re.match(r"\s*Array\d+\.t", (header + "\n" + body)[match.end():]):
            continue
        names.update(re.findall(r"\b\w+\b", match.group(1)))
    return names - {"var", "proc"}


def check_equalities(header, body):
    scalars = scalar_names(header, body)
    literal = {"None", "[]", "true", "false"}
    atom = r"(?:[A-Za-z_]\w*(?:\.`\d+)?|\[\]|-?\d+)"
    for comparison in re.finditer(r"<>|(?<![<>=!])=(?![=>])", body):
        left = re.search("(" + atom + r")\s*$", body[:comparison.start()])
        right = re.match(r"\s*(" + atom + ")", body[comparison.end():])
        policy.require(left and right, "non-scalar equality in executable expression")
        a, b = left.group(1), right.group(1)
        # Empty-list and option-None guards are constructor tests, not key equality.
        if a in {"None", "[]"} or b in {"None", "[]"}:
            continue
        scalar = lambda x: x in scalars or x in literal or bool(re.fullmatch(r"-?\d+", x))
        policy.require(scalar(a) and scalar(b), "whole key/cipher or unclassified equality: " + a + comparison.group() + b)


def check(sources):
    operations = local_ops(sources)
    code = policy.compact("\n".join(sources.values()))
    for name, definition in LITERAL_CONSTANTS.items():
        if name in operations:
            policy.require(policy.compact(definition) in code, "literal default constant changed: " + name)
    checked = []
    for source, text in sources.items():
        for module, block in modules(text):
            procs = procedures(block)
            remaining = block
            for _name, _header, _body, begin, end in reversed(procs):
                remaining = remaining[:begin] + remaining[end:]
            if (source, module) not in GLOBAL_MONITORS:
                policy.require(not re.search(r"\bvar\b", remaining), "new executable global outside proof monitor: " + module)
            else:
                expected = "var w:keygen_witness var g:acwc2_g_function var bad:bool var n:int"
                policy.require(policy.compact(remaining) == policy.compact(expected),
                               "proof-monitor global inventory changed")
            monitor = (source, module) in PROOF_MONITORS
            proof_context = monitor or (source, module) in PROOF_WRAPPERS
            for name, header, body, _begin, _end in procs:
                policy.require(not FORBIDDEN.search(body), "abstract map/list-spec operation in executable " + module + "." + name)
                if (source, module) not in IDEAL_STATE_WRAPPERS:
                    policy.require(not re.search(r"\b(?:ROE|ROF|ROG|ROH)\.m\b", body), "direct ideal table access in executable")
                for operation in operations:
                    if operation not in LITERAL_CONSTANTS:
                        policy.require(not re.search(r"\b" + re.escape(operation) + r"\b", body),
                                       "local specification helper used by executable: " + operation)
                forbidden_spec = SPEC_NAMES.pattern if not proof_context else r"\bhist_(?:get|put|keep|rep|unique|keys)\b"
                policy.require(not re.search(forbidden_spec, body), "hidden specification computation in executable")
                if not proof_context:
                    policy.require(not re.search(r"\b(?:keygen_witness|kg_sk|FOContext|HistProofMonitor)\b", header + body),
                                   "secret/proof-monitor dependency in public executable")
                if not monitor:
                    check_equalities(header, body)
                # Array reads are exposed only inside the fixed-byte comparator.
                if re.search(r"\.\s*\[", body):
                    policy.require(source == module == "HistKey" and name in {"equal", "suffix", "cipher"},
                                   "unclassified indexed lookup in executable")
                    dense = policy.compact(body)
                    reads = r"\b[xy]\.\`[12]\.\[comparisons(?:-96)?\]" if name == "equal" else r"\b[xy]\.\[comparisons\]"
                    remaining_reads = re.sub(reads, "BYTE_READ", dense)
                    policy.require(".[" not in remaining_reads, "indexed access is not a reviewed byte read")
                checked.append({"source": source, "module": module, "procedure": name,
                                "scope": "proof-only-monitor" if proof_context else "executable"})
    return checked
