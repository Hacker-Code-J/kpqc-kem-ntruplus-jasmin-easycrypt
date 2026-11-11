"""Reviewed semantic structure, checked independently from whole-file digests."""
MODEL = 'ntruplus/proof/768/ref/kem_failure_bound/NTRUPlus768KEMFailureModel.ec'


def check_new_model(read, ordered, require):
    text = read(MODEL)
    formula = 'op[opaque]kem_failure(er:encap_result)(dr:decap_result)=er.`3<>W32.zero\\/dr.`2<>W32.zero\\/er.`2<>dr.`1.'
    require(formula in text, 'failure includes both nonzero statuses and key mismatch')
    modules = ('EncapRandomInstrumented', 'KEMCorrectness', 'KEMCorrectnessInstrumented',
               'KeygenRNGPort', 'EncapRNGPort')
    require(text.count('module') == len(modules) + 1, 'new model module inventory')
    for name in modules:
        require(text.count('module' + name + '(') == 1, 'one declaration per module')
    instrumented = text.split('moduleEncapRandomInstrumented(', 1)[1].split('moduleKEMCorrectness(', 1)[0]
    public = text.split('moduleKEMCorrectness(', 1)[1].split('moduleKEMCorrectnessInstrumented(', 1)[0]
    private = text.split('moduleKEMCorrectnessInstrumented(', 1)[1].split('moduletypeKEMRNG', 1)[0]
    require('moduletypeKEMRNG={procseed32():W8.tArray32.tproccoins96():W8.tArray96.t}.' in text,
            'common RNG has exact 32-byte and 96-byte procedures')
    for name, size, draw in (('KeygenRNGPort', '32', 'seed32'), ('EncapRNGPort', '96', 'coins96')):
        body = 'module' + name + '(B:KEMRNG)={procsample():W8.tArray' + size + '.t={varx;x<@B.' + draw + '();returnx;}}.'
        require(body in text, 'common-state RNG port must forward one matching draw')
    for body, calls in ((instrumented, 3), (public, 3), (private, 3)):
        require(body.count('<@') == calls and body.count('return') == 1, 'exact call and return counts')
        require('var' not in body.split('proc', 1)[0], 'no instrumentation global state')
        require(all(token not in body for token in ('if(', 'while(', '<$')), 'no replacement sampling or branch')
    ordered(instrumented, ('coins <@ Q.sample();', 'original <- coins;',
                          '(ct,ss,status,workspace) <@ EncapDerand(F,G,H).run(pk,coins,workspace);',
                          'coins <@ NTRUPlus768EncapClearCoins.M.jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins(coins);',
                          'return((ct,ss,status,workspace,coins),original);'))
    require('procrun():bool={' in public, 'public experiment returns only the failure bit')
    ordered(public, ('(pk,sk) <@ Keygen(R,E,F).run();',
                     'er <@ EncapRandom(F,G,H,Q).run(pk,witness);',
                     'dr <@ CompleteDecaps(G,H).run(er.`1,sk,witness);', 'return kem_failure er dr;'))
    require('procrun():bool*bool={' in private, 'private observation returns exactly failure/bad bits')
    ordered(private, ('(w,cleared) <@ KeygenInstrumented(R,E,F).run(witness);',
                      '(er,coins) <@ EncapRandomInstrumented(F,G,H,Q).run(w.`kg_pk,witness);',
                      'dr <@ CompleteDecaps(G,H).run(er.`1,w.`kg_sk,witness);',
                      'return(kem_failure er dr,!keygen_coins_no_wrap w coins);'))
