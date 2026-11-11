"""Source checks supplement, and never replace, Coq kernel replay.

Generated EasyCrypt context declarations are compared with a fresh export;
these checks apply only to authored helpers and inserted proof bodies.
Section hypotheses are allowed only because their final statements must also
pass a separate, theorem-specific Print Assumptions check.
"""
import re


def code_only(text):
    out, index, depth, quoted = [], 0, 0, False
    while index < len(text):
        pair = text[index:index + 2]
        char = text[index]
        if depth:
            if pair == '(*':
                depth += 1
                index += 2
            elif pair == '*)':
                depth -= 1
                index += 2
                if not depth:
                    out.append(' ')
            else:
                index += 1
            continue
        if quoted:
            if pair == '""':
                index += 2
            elif char == '"':
                quoted = False
                index += 1
                out.append(' ')
            else:
                index += 1
            continue
        if pair == '(*':
            depth = 1
            index += 2
        elif pair == '*)':
            raise ValueError('unmatched comment closer')
        elif char == '"':
            quoted = True
            index += 1
        else:
            out.append(char)
            index += 1
    if depth or quoted:
        raise ValueError('unclosed comment or string')
    return ''.join(out)


def check_authored(text, *, proof_body=False):
    code = code_only(text)
    forbidden = r'\b(?:Admitted|admit|Abort|Axioms?|Parameters?|Conjectures?|exact_no_check|vm_cast_no_check|native_cast_no_check)\b'
    if re.search(forbidden, code, re.I):
        raise ValueError('unproved declaration or unchecked proof escape')
    if re.search(r'\bUnset\s+(?:Guard|Positivity|Universe)\s+Checking\b', code, re.I):
        raise ValueError('disabled kernel check')
    if re.search(r'\b(?:Load|Declare\s+ML\s+Module)\b', code, re.I):
        raise ValueError('untracked source or plugin load')
    if re.search(r'\b(?:Reset|Back|BackTo|Undo|Restart|Drop|Cd)\b', code, re.I):
        raise ValueError('proof context reset or directory mutation')
    if re.search(r'\b(?:Add|Remove)\s+(?:Rec\s+)?(?:LoadPath|ML\s+Path)\b', code, re.I):
        raise ValueError('untracked search-path mutation')
    if re.search(r'\b(?:sr_fresh_exported_goal|sr_checked_goal)\b', code):
        raise ValueError('reserved semantic-gate identifier in authored source')
    sections = []
    for command in re.split(r'\.(?=\s|$)', code):
        command = command.strip()
        opened = re.match(r'^Section\s+(\w+)\s*$', command)
        closed = re.match(r'^End\s+(\w+)\s*$', command)
        if opened:
            if proof_body:
                raise ValueError('section in native proof body')
            sections.append(opened.group(1))
        elif closed and sections and closed.group(1) == sections[-1]:
            sections.pop()
        elif re.match(r'^(?:Local\s+|Global\s+)?(?:Variables?|Hypotheses|Hypothesis|Context)\b', command):
            if proof_body or not sections:
                raise ValueError('ungeneralized authored assumption')
    if sections:
        raise ValueError('unclosed section')


def require_closed_assumptions(text):
    if text.strip() != 'Closed under the global context':
        raise ValueError('theorem has unapproved global assumptions or ambiguous output')


def controls():
    accepted = [
        'Lemma identity (P:Prop) : P -> P. Proof. exact (fun p => p). Qed.',
        'Section S. Variable P : Prop. Hypothesis h : P. Lemma local_p : P. Proof. exact h. Qed. End S.',
        '(* outer (* Admitted. *) comment *) Lemma good : True. Proof. exact I. Qed.',
    ]
    rejected = [
        'Lemma hole : False. Admitted.', 'Axiom hole : False.',
        'Parameter hole : False.', 'Variable hole : False.',
        'Hypothesis hole : False.', 'Context (hole:False).',
        'Lemma hole : False. Proof. admit. Qed.', 'Lemma hole : False. Abort.',
        'Lemma hole : False. Proof. exact_no_check I. Qed.',
        'Unset Guard Checking.', 'Unset Positivity Checking.', 'Unset Universe Checking.',
        'Load "untracked.v".', 'Declare ML Module "untracked".',
        'Check True. Load "untracked.v".', 'Time Load "untracked.v".',
        'Timeout 10 Load "untracked.v".', 'Redirect "out" Load "untracked.v".',
        'Check True. Declare ML Module "untracked".',
        'Check True. Reset Initial.', 'BackTo 1.', 'Undo.', 'Cd "elsewhere".',
        'Add LoadPath "elsewhere".', 'Add Rec LoadPath "elsewhere" as X.',
        'Add ML Path "elsewhere".',
        'Definition sr_fresh_exported_goal := True.',
        'Definition sr_checked_goal := I.',
        'Section S. Variable hole : False.', '(* unclosed', '*)', '"unclosed',
        '(* one (* two *) *) Axiom hidden : False.',
    ]
    results = []
    for index, text in enumerate(accepted):
        check_authored(text)
        results.append({'case': 'accepted-' + str(index), 'result': 'PASS'})
    for index, text in enumerate(rejected):
        try:
            check_authored(text)
        except ValueError:
            results.append({'case': 'rejected-' + str(index), 'result': 'EXPECTED_REJECTION'})
        else:
            raise AssertionError('unsafe Coq input accepted: ' + text)
    require_closed_assumptions('Closed under the global context\n')
    for text in ['Axioms:\nhole : False\nClosed under the global context',
                 'Closed under the global context\nClosed under the global context']:
        try:
            require_closed_assumptions(text)
        except ValueError:
            results.append({'case': 'ambiguous-assumptions', 'result': 'EXPECTED_REJECTION'})
        else:
            raise AssertionError('ambiguous assumption output accepted')
    return results


if __name__ == '__main__':
    import json
    print(json.dumps({'status': 'PASS', 'scope': 'source and assumption-output controls only',
                      'controls': controls()}, indent=2))
