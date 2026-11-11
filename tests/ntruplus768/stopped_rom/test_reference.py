#!/usr/bin/env python3
"""Exact toy diagnostics; these are not NTRU+ cryptographic proof replays."""
from fractions import Fraction as Q
from itertools import product
import json


def reach_probability(transitions, start, targets):
    """Least reachability solution; closed nonreturning classes have mass zero."""
    reachable=set(targets)
    while True:
        previous=set(reachable)
        reachable.update(s for s,edges in transitions.items()
                         if any(p>0 and t in reachable for t,p in edges.items()))
        if previous==reachable:
            break
    if start not in reachable:
        return Q(0)
    if start in targets:
        return Q(1)
    states=sorted(reachable-set(targets))
    matrix=[]
    for state in states:
        row=[Q(state==other)-transitions[state].get(other,Q(0)) for other in states]
        row.append(sum((p for t,p in transitions[state].items() if t in targets),Q(0)))
        matrix.append(row)
    for column in range(len(states)):
        pivot=next(i for i in range(column,len(states)) if matrix[i][column])
        matrix[column],matrix[pivot]=matrix[pivot],matrix[column]
        scale=matrix[column][column]
        matrix[column]=[x/scale for x in matrix[column]]
        for i in range(len(states)):
            if i!=column:
                scale=matrix[i][column]
                matrix[i]=[x-scale*y for x,y in zip(matrix[i],matrix[column])]
    return matrix[states.index(start)][-1]


def main():
    checks = []
    def check(label, condition):
        if not condition:
            raise AssertionError(label)
        checks.append(label)

    # Enumerate a finite seed space, retaining the prior table throughout.
    n = 4
    for prior_size in range(n+1):
        for q in range(5):
            prior = set(range(prior_size))
            bad = 0
            for seeds in product(range(n), repeat=q):
                known = set(prior)
                collision = False
                for seed in seeds:
                    collision |= seed in known
                    known.add(seed)
                bad += collision
            exact = Q(bad, n**q)
            delta = Q(prior_size*q, n) + Q(q*(q-1), 2*n)
            check(f'birthday-prior-{prior_size}-draws-{q}', exact <= delta)
    check('prior-size-term-is-necessary', Q(1,4) > Q(1*(1-1),2*4))
    check('triangle-off-by-one-is-detected', Q(1,4) > Q(2*(2-2),2*4))
    # A fresh draw is a joint buffer, not a vector of post-conditioned iid coefficients.
    buffers = tuple(product(range(2), repeat=2))
    accepted = [b for b in buffers if b[0] == b[1]]
    p = Q(len(accepted), len(buffers))
    joint = Q(sum(b == (1,1) for b in accepted),len(accepted))
    marginal = Q(sum(b[0] == 1 for b in accepted),len(accepted))
    check('whole-buffer-conditioning-retains-correlation', joint == Q(1,2) and joint != marginal*marginal)
    for q in range(5):
        rejects = sum(all(b not in accepted for b in draws) for draws in product(buffers, repeat=q))
        check(f'finite-tail-{q}', Q(rejects,len(buffers)**q) == (1-p)**q)
    for qf,qg in product(range(4),repeat=2):
        success=(1-(1-p)**qf)*(1-(1-p)**qg)
        check(f'two-phase-tail-{qf}-{qg}', 1-success <= (1-p)**qf+(1-p)**qg)
    check('zero-budget-has-unit-exhaustion', (1-p)**0 == 1)
    # One seed with a cached reject loops forever in real ROM. Fresh independent
    # Bernoulli buffers eventually accept. A bad flag observed only on returning
    # executions therefore has mass zero in real ROM despite distance one.
    real_chain={'query': {'query': Q(1)}}
    fresh_chain={'query': {'query': Q(1,2), 'return': Q(1,2)}}
    real_return_mass=reach_probability(real_chain,'query',{'return'})
    returned_bad_mass=reach_probability(real_chain,'query',{'returned_bad'})
    fresh_return_mass=reach_probability(fresh_chain,'query',{'return'})
    check('finite-state-fresh-return-is-one', fresh_return_mass == 1)
    check('finite-state-cached-reject-never-returns', real_return_mass == 0)
    check('completed-run-bad-cannot-bound-post-bad-divergence',
          abs(fresh_return_mass-real_return_mass) > returned_bad_mass)
    # Good can correlate with outputs through adaptive stopping: an output 0
    # stops at one query; output 1 draws again and risks a seed collision.
    outcomes=tuple(product(range(2),repeat=3))
    good_zero=Q(sum(bit==0 for bit,seed1,seed2 in outcomes),len(outcomes))
    good_one=Q(sum(bit==1 and seed1!=seed2 for bit,seed1,seed2 in outcomes),len(outcomes))
    check('good-normalization-is-not-original-fresh-law', good_one/(good_zero+good_one) != Q(1,2))
    # Exhaust all two-output subdistributions on a quarter-mass grid. A real
    # stopped subdistribution embeds in the possibly diverging real execution;
    # fresh stopped embeds in a total ideal execution. This tests the transfer
    # without treating real nonreturning mass as a completed bad observation.
    transfer_cases=0
    def event_distance(left,right):
        return max(abs(left[0]-right[0]),abs(left[1]-right[1]),abs(sum(left)-sum(right)))
    for r0 in range(5):
        for r1 in range(5-r0):
            real=(Q(r0,4),Q(r1,4))
            for s0 in range(r0+1):
                for s1 in range(r1+1):
                    stopped=(Q(s0,4),Q(s1,4))
                    for i0 in range(5):
                        ideal=(Q(i0,4),Q(4-i0,4))
                        for t0 in range(i0+1):
                            for t1 in range(5-i0):
                                fresh_stopped=(Q(t0,4),Q(t1,4))
                                delta=event_distance(stopped,fresh_stopped)
                                tau=1-sum(fresh_stopped)
                                if event_distance(real,ideal)>delta+tau or 1-sum(real)>delta+tau:
                                    raise AssertionError('invalid delta+tau subdistribution transfer')
                                transfer_cases+=1
    check('delta-plus-tail-transfer-without-real-losslessness',transfer_cases>0)
    check('transfer-cannot-omit-tail',event_distance((Q(0),Q(1)),(Q(1),Q(0)))>
          event_distance((Q(0),Q(0)),(Q(0),Q(0))))
    check('transfer-cannot-omit-switch-distance',event_distance((Q(1),Q(0)),(Q(0),Q(1)))>Q(0))
    print(json.dumps({'status':'PASS','count':len(checks),'scope':'exact finite-domain diagnostics only; not a cryptographic proof',
                      'checks':checks,'subdistribution_transfer_cases':transfer_cases,'divergence_witness':{'real_return_mass':str(real_return_mass),'fresh_return_mass':str(fresh_return_mass),'real_returned_bad_mass':str(returned_bad_mass)}}))


if __name__ == '__main__':
    main()
