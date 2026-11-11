#!/usr/bin/env python3
"""Hash-bind the conservative import closure and check the public-history FO simulation trust boundaries."""
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
TEST = Path(__file__).resolve().parent
ROOT = TEST.parents[2]
BASE = ROOT / 'ntruplus/proof/768/ref'
GROUPS = ('kem_fo_simulation',)
SCRIPT = ROOT / 'scripts/verify-ntruplus768-fo-simulation.sh'
ENTRY = ROOT / 'tests/test_ntruplus768_fo_simulation.py'

# Final inventory is reviewed with the proof owners before source pins are made.
MAINS = ('kem_fo_simulation/NTRUPlus768SimAverage.ec',
 'kem_fo_simulation/NTRUPlus768SimCandidate.ec',
 'kem_fo_simulation/NTRUPlus768SimFreshHash.ec',
 'kem_fo_simulation/NTRUPlus768SimModel.ec',
 'kem_fo_simulation/NTRUPlus768SimSequentialDistance.ec',
 'kem_fo_simulation/NTRUPlus768SimHybrid.ec',
 'kem_fo_simulation/NTRUPlus768SimLookup.ec',
 'kem_fo_simulation/NTRUPlus768SimSampling.ec',
 'kem_fo_simulation/NTRUPlus768SimAnswer.ec',
 'kem_fo_simulation/NTRUPlus768SimKnownAlgebra.ec',
 'kem_fo_simulation/NTRUPlus768SimOracles.ec',
 'kem_fo_simulation/NTRUPlus768SimPrefix.ec',
 'kem_fo_simulation/NTRUPlus768SimPublicError.ec',
 'kem_fo_simulation/NTRUPlus768SimSpreadHash.ec',
 'kem_fo_simulation/NTRUPlus768SimAnswerErasure.ec',
 'kem_fo_simulation/NTRUPlus768SimGErasure.ec',
 'kem_fo_simulation/NTRUPlus768SimKnown.ec',
 'kem_fo_simulation/NTRUPlus768SimPorts.ec',
 'kem_fo_simulation/NTRUPlus768SimPublicBound.ec',
 'kem_fo_simulation/NTRUPlus768SimChallengeAnswer.ec',
 'kem_fo_simulation/NTRUPlus768SimGames.ec',
 'kem_fo_simulation/NTRUPlus768SimPortContracts.ec',
 'kem_fo_simulation/NTRUPlus768SimPublicCapRemoval.ec',
 'kem_fo_simulation/NTRUPlus768SimPublicGames.ec',
 'kem_fo_simulation/NTRUPlus768SimPublicInstances.ec',
 'kem_fo_simulation/NTRUPlus768SimRealBridge.ec',
 'kem_fo_simulation/NTRUPlus768SimSelected.ec',
 'kem_fo_simulation/NTRUPlus768SimSetupBridge.ec',
 'kem_fo_simulation/NTRUPlus768SimKnownCoupling.ec',
 'kem_fo_simulation/NTRUPlus768SimLookupGameBridge.ec',
 'kem_fo_simulation/NTRUPlus768SimPhaseState.ec',
 'kem_fo_simulation/NTRUPlus768SimRealGameBridge.ec',
 'kem_fo_simulation/NTRUPlus768SimSelectedCoupling.ec',
 'kem_fo_simulation/NTRUPlus768SimSelectedInvariant.ec',
 'kem_fo_simulation/NTRUPlus768SimKnownBridge.ec',
 'kem_fo_simulation/NTRUPlus768SimSelectedBound.ec',
 'kem_fo_simulation/NTRUPlus768SimPhaseBound.ec',
 'kem_fo_simulation/NTRUPlus768SimKernelBound.ec',
 'kem_fo_simulation/NTRUPlus768SimFinal.ec')



def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def without_comments(text):
    depth, parts = 0, []
    for token in re.split(r'(\(\*|\*\))', text):
        if token == '(*':
            depth += 1
            parts.append(' ')
        elif token == '*)':
            require(depth > 0, 'unmatched EasyCrypt comment terminator')
            depth -= 1
        elif not depth:
            parts.append(token)
    require(depth == 0, 'unclosed EasyCrypt comment')
    return ''.join(parts)


# These are typed clone parameters, never assumptions about a game or bound.
CLONE_PARAMETERS = {
    'kem_fo_simulation/NTRUPlus768SimHybrid.ec': (
        'SimHybridBudget', ('type leak_input', 'type leak_output', 'op budget : int'),
        'abstract theory SimHybridBudget. type leak_input. type leak_output. op budget : int. '
        'clone import Hybrid as HB with type input <- sim_request, type output <- W8.t Array32.t option, '
        'type inleaks <- leak_input, type outleaks <- leak_output, type outputA <- bool, '
        'op q <- max 0 budget proof q_ge0 by smt() proof *.'),
    'kem_fo_simulation/NTRUPlus768SimSelected.ec': (
        'SimSelectedBudget', ('op budget : int',),
        'theory SimSelectedBudget. op budget : int. clone import SimHybridBudget as SH with '
        'type leak_input <- sim_leak_input, type leak_output <- sim_leak_output, op budget <- budget.'),
}


def check_proof_text(text, source_name=None):
    code = without_comments(text)
    require(not re.search(r'\b(admit|admitted|abort|assume|axiom|sorry|pragma)\b', code),
            'local proof escape, axiom or checker pragma')
    require(not re.search(r'\baxiomatized\s+by\b', code), 'opaque proof assumption')
    require(not re.search(r'(?m)^\s*print\s+(?:goal|all)\b', code), 'debug proof command')
    allowed = CLONE_PARAMETERS.get(source_name)
    remaining = set()
    if allowed:
        scope, declarations, binding = allowed
        headers = re.findall(r'(?m)^\s*(abstract\s+)?theory\s+' + re.escape(scope) + r'\s*\.', code)
        require(len(headers) == 1 and bool(headers[0]) == (scope == 'SimHybridBudget'),
                'reviewed abstract/concrete theory kind changed')
        require(compact(binding) in compact(code), 'reviewed clone-parameter binding changed')
        remaining = {compact(declaration) for declaration in declarations}
    scopes = []
    for statement in re.split(r'\.(?=\s|$)', code):
        opened = re.fullmatch(r'\s*(?:abstract\s+)?theory\s+(\w+)\s*', statement)
        closed = re.fullmatch(r'\s*end\s+(\w+)\s*', statement)
        if opened:
            scopes.append(opened.group(1))
        elif closed:
            require(scopes and scopes.pop() == closed.group(1), 'theory scope mismatch')
        elif re.match(r'\s*(?:local\s+)?(?:op|type)\b', statement):
            if '=' not in statement:
                declaration = compact(statement)
                require(allowed and scopes == [allowed[0]] and declaration in remaining,
                        'abstract project declaration outside reviewed clone parameters')
                remaining.remove(declaration)
            else:
                require('{' not in statement.partition('=')[0], 'constrained project declaration')
    require(not scopes, 'unclosed theory scope')
    require(not remaining, 'reviewed clone parameter not declared in its exact scope')


def compact(text):
    return re.sub(r'\s+', '', without_comments(text))


def ordered(text, tokens):
    position = 0
    for token in tokens:
        token = compact(token)
        offset = text.find(token, position)
        require(offset >= 0, 'missing or reordered operation: ' + token)
        position = offset + len(token)


def include_arguments(group):
    project = BASE / group / 'easycrypt.project'
    args, directories, seen = [], [], set()
    for raw in project.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith(('#', '[')):
            continue
        key, separator, value = line.partition('=')
        key, value = key.strip(), value.strip()
        require(separator and key in ('rdirs', 'idirs', 'timeout'), 'unsupported project setting')
        if key == 'timeout':
            continue
        namespace, colon, relative = value.partition(':')
        if not colon:
            namespace, relative = '', value
        path = (project.parent / relative).resolve()
        require(path.is_dir() and path.is_relative_to(ROOT), 'include directory outside checkout')
        flag = '-R' if key == 'rdirs' else '-I'
        value = namespace + ':' + str(path) if colon else str(path)
        if (flag, value) not in seen:
            seen.add((flag, value))
            args += [flag, value]
            directories.append(path)
    return args, directories


def source_paths():
    # Imported old and standard project theories are pinned, not replayed as mains.
    paths = set()
    for group in GROUPS:
        _, directories = include_arguments(group)
        for directory in directories:
            paths.update(directory.rglob('*.ec'))
            for name in ('Makefile', 'easycrypt.project'):
                path = directory / name
                if path.is_file():
                    paths.add(path)
        paths.update(BASE / group / name for name in ('Makefile', 'easycrypt.project'))
    paths.update(BASE / name for name in MAINS)
    require(all(p.is_file() and not p.is_symlink() for p in paths), 'missing or symlink source')
    return paths


def snapshot():
    paths = source_paths() | {SCRIPT, ENTRY}
    paths.update(p for p in TEST.iterdir() if p.is_file() and p.suffix in ('.py', '.json'))
    return {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in sorted(paths)}


def check_structure(sources=None):
    sources = sources or {}
    def read(relative):
        return compact(sources.get(relative, (ROOT / relative).read_text()))
    from model_contract import check_model
    check_model(read, ordered, require)


def check():
    require((TEST / 'source-pins.json').is_file(), 'source pins are pending the reviewed proof freeze')
    pins = json.loads((TEST / 'source-pins.json').read_text())
    actual = {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in sorted(source_paths())}
    require(set(actual) == set(pins), 'source/import inventory drift')
    for name, value in actual.items():
        require(value == pins[name], 'source/import pin drift: ' + name)
    inventory = {str(p.relative_to(BASE)) for group in GROUPS for p in (BASE / group).glob('*.ec')}
    require(inventory == set(MAINS), 'new proof inventory drift')
    for name in MAINS:
        check_proof_text((BASE / name).read_text(), name)
    check_structure()
    return actual


if __name__ == '__main__':
    print(json.dumps({'status': 'PASS', 'pinned_sources': len(check()), 'new_mains': len(MAINS)}))
