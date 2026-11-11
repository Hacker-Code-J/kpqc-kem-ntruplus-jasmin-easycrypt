"""Public recovery and actual arithmetic seams; source controls are not proofs."""
BASE='ntruplus/proof/768/ref/acwc2_contracts/'
WORDS=BASE+'NTRUPlus768RRecWordChecks.ec'
INVERSE=BASE+'NTRUPlus768RRecPublicInverse.ec'
PROCEDURES=BASE+'NTRUPlus768RRecProcedures.ec'
RULES=(
 (WORDS,'center residues modulo q at the correct inclusive boundary',r'op rrec_center (x:int) = let z=x %% 3457 in if 1728<z then z-3457 else z.'),
 (WORDS,'normalization visits every coefficient',r'while(i<768){ output.[i] <- W16.of_int(rrec_center(coeff ap.[i])); i <- i+1; }'),
 (WORDS,'trit validity accumulates across all coefficients',r'valid <- true; i <- 0; while(i<768){ valid <- valid /\ is_trit(coeff ap.[i]); i <- i+1; } return valid;'),
 (INVERSE,'public inverse is computed and canonically serialized without a secret input',r'module RRecPublicInverse = { proc run(hp:W16.t Array768.t) : W16.t Array768.t option = { var raw,canonical:W16.t Array768.t; var status:W64.t; var decoded_status:W32.t; var bytes:W8.t Array1152.t; var result:W16.t Array768.t option; result<-None; (raw,status)<@NTRUPlus768PolyBaseInv.M.__poly_baseinv_core(witness,hp); if(status=W64.zero){ bytes<@NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,raw); (canonical,decoded_status)<@NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,bytes); if(decoded_status=W32.zero){result<-Some canonical;} } return result; } }.'),
 (PROCEDURES,'internal core preserves actual r2 and inverse-NTT calls',r'rhat <@ NTRUPlus768DecapR2Comp.M.jade_ntruplus_ntruplus768_amd64_ref_decap_r2(witness,cp,m,inverse); raw <@ NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt(witness,rhat); return raw;'),
 (PROCEDURES,'candidate is normalized and checked before acceptance',r'result <- None; raw <@ RRecCore.run(cp,m,inverse); candidate <@ RRecNormalize.run(raw); valid <@ RRecTrit.check(candidate); if(valid){ result <- Some candidate; } return result;'),
 (PROCEDURES,'public consistency helper re-encrypts before returning a candidate',r'module RRecVerify = { proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t, candidate:W16.t Array768.t option) : W16.t Array768.t option = { var result:W16.t Array768.t option; var checked:W8.t Array1152.t option; result <- None; if(candidate<>None){ checked <@ PKEEnc.run(pk,m,oget candidate); if(checked=Some ct){result<-candidate;} } return result; } }.'),
 (PROCEDURES,'public RR takes exactly pk/message/ciphertext and derives its inverse internally',r'module RRec = { proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t) : W16.t Array768.t option = { var hp:W16.t Array768.t; var status:W32.t; var inverse,result:W16.t Array768.t option; result <- None; (hp,status) <@ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,pk); if(status=W32.zero){ inverse <@ RRecPublicInverse.run(hp); if(inverse<>None){ result <@ RRecUsingInverse.run(pk,m,ct,oget inverse); } } return result; } }.'),
 (PROCEDURES,'ciphertext and message checks precede recovery and re-encryption',r'(cp,status) <@ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,ct); if(status=W32.zero){ valid_message <@ RRecTrit.check(m); if(valid_message){ result <@ RRecFinish.run(cp,m,inverse); result <@ RRecVerify.run(pk,m,ct,result); } } return result;'),
)
MUTATIONS=(
 ('normalization-moves-positive-midpoint-to-negative-side',WORDS,'if 1728<z then z-3457 else z','if 1728<=z then z-3457 else z'),
 ('normalization-skips-final-coefficient',WORDS,'while(i<768){ output.[i]','while(i<767){ output.[i]'),
 ('trit-check-forgets-an-earlier-invalid-coefficient',WORDS,r'valid <- valid /\ is_trit(coeff ap.[i]);',r'valid <- is_trit(coeff ap.[i]);'),
 ('public-inverse-is-supplied-instead-of-computed',INVERSE,'(raw,status)<@NTRUPlus768PolyBaseInv.M.__poly_baseinv_core(witness,hp);','raw<-witness; status<-W64.zero;'),
 ('public-inverse-skips-serialization-normalization',INVERSE,'result<-Some canonical;','result<-Some raw;'),
 ('public-inverse-ignores-failure-status',INVERSE,'if(status=W64.zero)','if(true)'),
 ('public-inverse-uses-unchecked-decoder',INVERSE,'NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,bytes)','NTRUPlus768PolyFromBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,bytes)'),
 ('RR-core-skips-actual-r2-kernel',PROCEDURES,'rhat <@ NTRUPlus768DecapR2Comp.M.jade_ntruplus_ntruplus768_amd64_ref_decap_r2(witness,cp,m,inverse);','rhat<-cp;'),
 ('RR-core-skips-inverse-NTT',PROCEDURES,'raw <@ NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt(witness,rhat);','raw<-rhat;'),
 ('RR-accepts-unchecked-candidate-domain',PROCEDURES,'valid <@ RRecTrit.check(candidate);','valid <- true;'),
 ('RR-soundness-guard-skips-actual-re-encryption',PROCEDURES,'checked <@ PKEEnc.run(pk,m,oget candidate);','checked <- Some ct;'),
 ('RR-soundness-guard-does-not-compare-ciphertext',PROCEDURES,'if(checked=Some ct)','if(checked<>None)'),
 ('RR-public-interface-adds-secret-key-argument',PROCEDURES,'module RRec = { proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t)','module RRec = { proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t,sk:W8.t Array2336.t)'),
 ('RR-public-interface-adds-supplied-inverse',PROCEDURES,'module RRec = { proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t)','module RRec = { proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t,hinv:W16.t Array768.t)'),
 ('RR-reads-secret-global-in-place-of-public-inversion',PROCEDURES,'inverse <@ RRecPublicInverse.run(hp);','inverse <- Some Secret.hinv;'),
 ('RR-rejects-neither-noncanonical-ciphertext-nor-invalid-decoder-status',PROCEDURES,'poly_frombytes(witness,ct); if(status=W32.zero)','poly_frombytes(witness,ct); if(true)'),
 ('RR-forwards-invalid-message',PROCEDURES,'valid_message <@ RRecTrit.check(m);','valid_message <- true;'),
)


from recovery_contract import RULES as RECOVERY_RULES, MUTATIONS as RECOVERY_MUTATIONS
from sotp_contract import RULES as SOTP_RULES, MUTATIONS as SOTP_MUTATIONS
from hash_contract import RULES as HASH_RULES, MUTATIONS as HASH_MUTATIONS
RULES += HASH_RULES
MUTATIONS += HASH_MUTATIONS
RULES += SOTP_RULES
MUTATIONS += SOTP_MUTATIONS
RULES += RECOVERY_RULES
MUTATIONS += RECOVERY_MUTATIONS

def check_model(read, ordered, require):
 from check_acwc2_contracts import compact
 for relative,label,expected in RULES:
  require(compact(expected).replace('op[opaque]','op') in read(relative).replace('op[opaque]','op'),label)
