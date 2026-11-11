"""Composed calls and the single-entry base envelope remain distinct."""
BASE='ntruplus/proof/768/ref/acwc2_correctness/'
MODEL=BASE+'NTRUPlus768ACWC2Model.ec'
PROCEDURES=BASE+'NTRUPlus768ACWC2Procedures.ec'
ENVELOPE=BASE+'NTRUPlus768ACWC2BaseModel.ec'
NUMERICAL=BASE+'NTRUPlus768ACWC2Numerical.ec'
RULES=(
 (PROCEDURES,'a fixed full G is queried without resampling or reinitializing',r'module ACWC2FullG = { var table:acwc2_g_map proc init(g:acwc2_g_map) : unit = {table<-g;} proc run(r:pke_poly) : W8.t Array192.t = {return table r;} }.'),
 (PROCEDURES,'actual transformed Enc queries G then SOTP and PKE',r'module ACWC2Enc(G:ACWC2GPort) = { proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t,r:pke_poly) : W8.t Array1152.t option = { var pad:W8.t Array192.t; var code:pke_poly; var ct:W8.t Array1152.t option; pad <@ G.run(r); code <@ SOTPEncode.run(msg,pad); ct <@ PKEEnc.run(pk,code,r); return ct; } }.'),
 (PROCEDURES,'actual transformed Dec has no original message or randomness input',r'module ACWC2Dec(G:ACWC2GPort) = { proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t,ct:W8.t Array1152.t) : W8.t Array96.t option = { var code,recovered:pke_poly option; var pad:W8.t Array192.t; var msg:W8.t Array96.t option; code <@ PKEDec.run(ct,acwc2_secret_bytes sk); msg <- None; if(code<>None){ recovered <@ RRec.run(pk,oget code,ct); if(recovered<>None){ pad <@ G.run(oget recovered); msg <@ SOTPDecode.run(oget code,pad); } } return msg; } }.'),
 (PROCEDURES,'actual roundtrip counts every rejection and message mismatch',r'ct <@ ACWC2Enc(G).run(pk,msg,r); failed <- true; if(ct<>None){ decoded <@ ACWC2Dec(G).run(pk,sk,oget ct); failed <- decoded<>Some msg; } return failed;'),
 (MODEL,'transformed Dec specification queries the recovered randomness',r'op acwc2_dec_spec (g:acwc2_g_map) (pk:W8.t Array1152.t) (sk:W8.t Array2336.t) (ct:W8.t Array1152.t) : W8.t Array96.t option = let code=pke_dec_spec ct (acwc2_secret_bytes sk) in if code=None then None else let recovered=rrec_spec pk (oget code) ct in if recovered=None then None else sotp_decode_option (oget code) (g (oget recovered)).'),
 (ENVELOPE,'base failure includes rejected encryption and rejected base decoding',r'op acwc2_base_failure (w:keygen_witness) (code r:pke_poly) : bool = let ct=pke_enc_spec w.`kg_pk code r in ct=None \/ pke_dec_spec(oget ct)(pke_secret_bytes w)<>Some code.'),
 (ENVELOPE,'independent summand is a function of only the pad at its own r',r'op acwc2_pad_bad (w:keygen_witness) (msg:W8.t Array96.t) (r:pke_poly) (pad:W8.t Array192.t) : bool = acwc2_base_failure w (poly_sotp_encode_spec msg pad) r.'),
 (ENVELOPE,'base mean is conditional on its key and averages independent CBD r/code',r'op acwc2_base_mean (w:keygen_witness) : real = mu (pke_psi1 `*` pke_psi1) (fun (rc:pke_poly*pke_poly)=>acwc2_base_failure w rc.`2 rc.`1).'),
 (NUMERICAL,'actual CBD collision exponent is retained',r'op acwc2_collision_mass = (3%r/8%r)^768.'),
 (NUMERICAL,'strictly positive deviation threshold has the reviewed exponent',r'op acwc2_epsilon = (1%r/2%r)^356.'),
 (NUMERICAL,'union and eighth-moment powers retain the reviewed factors',r'op acwc2_union_tail = 2%r^768 * 65536%r * acwc2_collision_mass^4 / acwc2_epsilon^8.'),
)
MUTATIONS=(
 ('G-hit-resampled-instead-of-cached',PROCEDURES,'proc run(r:pke_poly) : W8.t Array192.t = {return table r;}','proc run(r:pke_poly) : W8.t Array192.t = {var pad;pad <$ uniform192;return pad;}'),
 ('transformed-Enc-substitutes-pure-SOTP-spec',PROCEDURES,'code <@ SOTPEncode.run(msg,pad);','code <- poly_sotp_encode_spec msg pad;'),
 ('transformed-Enc-skips-actual-PKE',PROCEDURES,'ct <@ PKEEnc.run(pk,code,r);','ct <- pke_enc_spec pk code r;'),
 ('transformed-Dec-adds-original-message-input',PROCEDURES,'proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t,ct:W8.t Array1152.t) : W8.t Array96.t option','proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t,ct:W8.t Array1152.t,original:W8.t Array96.t) : W8.t Array96.t option'),
 ('transformed-Dec-skips-actual-PKE-recovery',PROCEDURES,'code <@ PKEDec.run(ct,acwc2_secret_bytes sk);','code <- Some witness;'),
 ('transformed-Dec-skips-checked-RR',PROCEDURES,'recovered <@ RRec.run(pk,oget code,ct);','recovered <- Some witness;'),
 ('transformed-Dec-queries-original-instead-of-recovered-randomness',PROCEDURES,'pad <@ G.run(oget recovered);','pad <@ G.run(witness);'),
 ('transformed-Dec-skips-actual-checked-SOTP',PROCEDURES,'msg <@ SOTPDecode.run(oget code,pad);','msg <- Some witness;'),
 ('roundtrip-Enc-rejection-counted-as-success',PROCEDURES,'failed <- true;','failed <- false;'),
 ('roundtrip-loses-decoder-None-case',PROCEDURES,'failed <- decoded<>Some msg;','failed <- oget decoded<>msg;'),
 ('base-envelope-omits-encryption-rejection',ENVELOPE,r'ct=None \/ pke_dec_spec(oget ct)(pke_secret_bytes w)<>Some code.',r'pke_dec_spec(oget ct)(pke_secret_bytes w)<>Some code.'),
 ('base-envelope-forgets-decoder-rejection',ENVELOPE,'pke_dec_spec(oget ct)(pke_secret_bytes w)<>Some code','oget(pke_dec_spec(oget ct)(pke_secret_bytes w))<>code'),
 ('independent-envelope-substitutes-transformed-Dec-failure',ENVELOPE,'acwc2_base_failure w (poly_sotp_encode_spec msg pad) r.','acwc2_failure (fun _=>pad) w.`kg_pk w.`kg_sk msg r.'),
 ('base-mean-reuses-r-as-message-code',ENVELOPE,'acwc2_base_failure w rc.`2 rc.`1','acwc2_base_failure w rc.`1 rc.`1'),
 ('CBD-collision-falsely-uniform-on-trits',NUMERICAL,'(3%r/8%r)^768','(1%r/3%r)^768'),
 ('CBD-collision-falsely-equal-to-raw-buffer-collision',NUMERICAL,'(3%r/8%r)^768','(1%r/2%r)^1536'),
 ('eighth-moment-uses-eighth-power-of-collision',NUMERICAL,'acwc2_collision_mass^4','acwc2_collision_mass^8'),
 ('message-union-count-forgets-bits-per-byte',NUMERICAL,'2%r^768 * 65536%r','2%r^96 * 65536%r'),
 ('moment-bound-drops-combinatorial-constant',NUMERICAL,'2%r^768 * 65536%r','2%r^768'),
)


from probability_contract import RULES as PROBABILITY_RULES, MUTATIONS as PROBABILITY_MUTATIONS
from mean_contract import RULES as MEAN_RULES, MUTATIONS as MEAN_MUTATIONS
from integration_contract import RULES as INTEGRATION_RULES, MUTATIONS as INTEGRATION_MUTATIONS
RULES += INTEGRATION_RULES
MUTATIONS += INTEGRATION_MUTATIONS
RULES += MEAN_RULES
MUTATIONS += MEAN_MUTATIONS
RULES += PROBABILITY_RULES
MUTATIONS += PROBABILITY_MUTATIONS

def check_model(read, ordered, require):
 from check_acwc2_correctness import compact
 for relative,label,expected in RULES:
  require(compact(expected).replace('op[opaque]','op') in read(relative).replace('op[opaque]','op'),label)
