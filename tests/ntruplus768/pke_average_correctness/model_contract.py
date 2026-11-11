"""Actual PKE arithmetic and decoder boundaries; structural tests are not proofs."""
BASE='ntruplus/proof/768/ref/pke_average_correctness/'
PROCEDURES=BASE+'NTRUPlus768PKEProcedures.ec'
RULES=(
 (PROCEDURES,'actual encryption arithmetic and serialization order',r'module PKEEncBody = { proc run(hp:W16.t Array768.t,m:W16.t Array768.t,r:W16.t Array768.t) : W8.t Array1152.t = { var rhat,mhat,product,cipher:W16.t Array768.t; var ct:W8.t Array1152.t; rhat <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r); mhat <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,m); product <@ NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(witness,hp,rhat); cipher <@ NTRUPlus768PolyCenteredAdd.M.jade_ntruplus_ntruplus768_amd64_ref_poly_centered_add(witness,product,mhat); ct <@ NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,cipher); return ct; } }.'),
 (PROCEDURES,'checked public key before actual encryption',r'module PKEEnc = { proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,r:W16.t Array768.t) : W8.t Array1152.t option = { var hp:W16.t Array768.t; var status:W32.t; var ct:W8.t Array1152.t; var result:W8.t Array1152.t option; result <- None; (hp,status) <@ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,pk); if(status=W32.zero){ ct <@ PKEEncBody.run(hp,m,r); result <- Some ct; } return result; } }.'),
 (PROCEDURES,'decryption checks ct and secret then returns actual recovered polynomial',r'module PKEDec = { proc run(ct:W8.t Array1152.t,fbytes:W8.t Array1152.t) : W16.t Array768.t option = { var cp,fp,recovered:W16.t Array768.t; var status:W32.t; var result:W16.t Array768.t option; result <- None; (cp,status) <@ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,ct); if(status=W32.zero){ (fp,status) <@ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,fbytes); if(status=W32.zero){ recovered <@ NTRUPlus768DecapCandidate.M.jade_ntruplus_ntruplus768_amd64_ref_decap_candidate(witness,cp,fp); result <- Some recovered; } } return result; } }.'),
)
MUTATIONS=(
 ('Enc-message-NTT-substitutes-randomness',PROCEDURES,'mhat <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,m);','mhat <@ NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt(witness,r);'),
 ('Enc-basemul-omitted',PROCEDURES,'product <@ NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul(witness,hp,rhat);','product <- witness;'),
 ('Enc-adds-wrong-message-domain',PROCEDURES,'poly_centered_add(witness,product,mhat);','poly_centered_add(witness,product,m);'),
 ('Enc-serialization-substituted',PROCEDURES,'ct <@ NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes(witness,cipher);','ct <- witness;'),
 ('Enc-public-key-decoder-unchecked',PROCEDURES,'(hp,status) <@ NTRUPlus768PolyFromBytesChecked.M.','(hp,status) <@ NTRUPlus768PolyFromBytes.M.'),
 ('Enc-reuses-message-as-randomness',PROCEDURES,'PKEEncBody.run(hp,m,r)','PKEEncBody.run(hp,m,m)'),
 ('Dec-ciphertext-decoder-unchecked',PROCEDURES,'(cp,status) <@ NTRUPlus768PolyFromBytesChecked.M.','(cp,status) <@ NTRUPlus768PolyFromBytes.M.'),
 ('Dec-secret-decoder-unchecked',PROCEDURES,'(fp,status) <@ NTRUPlus768PolyFromBytesChecked.M.','(fp,status) <@ NTRUPlus768PolyFromBytes.M.'),
 ('Dec-canonical-ciphertext-check-bypassed',PROCEDURES,'poly_frombytes(witness,ct); if(status=W32.zero)','poly_frombytes(witness,ct); if(true)'),
 ('Dec-canonical-secret-check-bypassed',PROCEDURES,'poly_frombytes(witness,fbytes); if(status=W32.zero)','poly_frombytes(witness,fbytes); if(true)'),
 ('Dec-candidate-kernel-substituted',PROCEDURES,'recovered <@ NTRUPlus768DecapCandidate.M.jade_ntruplus_ntruplus768_amd64_ref_decap_candidate(witness,cp,fp);','recovered <- witness;'),
 ('Dec-returns-input-ciphertext-polynomial',PROCEDURES,'result <- Some recovered;','result <- Some cp;'),
)


from distribution_contract import RULES as DISTRIBUTION_RULES, MUTATIONS as DISTRIBUTION_MUTATIONS
from average_contract import RULES as AVERAGE_RULES, MUTATIONS as AVERAGE_MUTATIONS
RULES += AVERAGE_RULES
MUTATIONS += AVERAGE_MUTATIONS
RULES += DISTRIBUTION_RULES
MUTATIONS += DISTRIBUTION_MUTATIONS

def check_model(read, ordered, require):
 from check_pke_average_correctness import compact
 for relative,label,expected in RULES:
  require(compact(expected).replace('op[opaque]','op') in read(relative).replace('op[opaque]','op'),label)
