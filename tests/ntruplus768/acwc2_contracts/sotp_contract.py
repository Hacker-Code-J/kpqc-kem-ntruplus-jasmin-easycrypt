"""SOTP properties refer to the actual checked kernels and explicit wrapper guard."""
BASE='ntruplus/proof/768/ref/acwc2_contracts/'
CONTRACTS=BASE+'NTRUPlus768SOTPContracts.ec'
RIGIDITY=BASE+'NTRUPlus768SOTPRigidity.ec'
RULES=(
 (CONTRACTS,'actual SOTP encoder call',r'module SOTPEncode = { proc run(msg:W8.t Array96.t,pad:W8.t Array192.t) : W16.t Array768.t = { var code:W16.t Array768.t; code <@ NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(witness,msg,pad); return code; } }.'),
 (CONTRACTS,'decoder performs the explicit trit guard and uses actual status',r'module SOTPDecode = { proc run(code:W16.t Array768.t,pad:W8.t Array192.t) : W8.t Array96.t option = { var valid:bool; var msg:W8.t Array96.t; var status:W32.t; var output:W8.t Array96.t option; valid <@ RRecTrit.check(code); output <- None; if(valid){ (msg,status) <@ NTRUPlus768PolySOTPDecodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode(witness,code,pad); if(status=W32.zero){output <- Some msg;} } return output; } }.'),
 (CONTRACTS,'option specification preserves both domain and successful decode',r'op sotp_decode_option (code:W16.t Array768.t) (pad:W8.t Array192.t) = if pke_domain code /\ !poly_sotp_decode_fail_spec code pad then Some(poly_sotp_decode_msg_spec code pad) else None.'),
 (CONTRACTS,'re-encoding executes the actual encoder on the decoded message',r'rebuilt <@ SOTPEncode.run(oget msg,pad); output <- Some rebuilt;'),
 (CONTRACTS,'hiding samples one independent pad for the fixed input message',r'module SOTPUniformEncode = { proc run(msg:W8.t Array96.t) : W16.t Array768.t = { var pad:W8.t Array192.t; var code:W16.t Array768.t; pad <$ uniform192; code <@ SOTPEncode.run(msg,pad); return code; } }.'),
 (CONTRACTS,'roundtrip is a probability-one contract of the two actual calls',r'lemma sotp_roundtrip_correct msg0 pad0 : phoare[SOTPRoundTrip.run:msg=msg0 /\ pad=pad0 ==> res=Some msg0]=1%r.'),
 (CONTRACTS,'hiding endpoint is the actual uniform-pad encoder law',r'lemma sotp_uniform_encode_law &m msg0 event : Pr[SOTPUniformEncode.run(msg0) @ &m:event res]=mu pke_psi1 event.'),
 (RIGIDITY,'reverse encoding equality requires decode success',r'lemma sotp_decode_encode_rigidity a pad : !poly_sotp_decode_fail_spec a pad => poly_sotp_encode_spec (poly_sotp_decode_msg_spec a pad) pad = a.'),
)
MUTATIONS=(
 ('SOTP-encoder-substitutes-pure-value-spec',CONTRACTS,'code <@ NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(witness,msg,pad);','code <- poly_sotp_encode_spec msg pad;'),
 ('SOTP-wrapper-omits-trit-check',CONTRACTS,'valid <@ RRecTrit.check(code);','valid <- true;'),
 ('SOTP-wrapper-ignores-actual-decoder-status',CONTRACTS,'if(status=W32.zero)','if(true)'),
 ('SOTP-wrapper-treats-zero-message-as-failure',CONTRACTS,'if(status=W32.zero)','if(msg<>witness)'),
 ('SOTP-wrapper-substitutes-raw-message-spec',CONTRACTS,'(msg,status) <@ NTRUPlus768PolySOTPDecodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode(witness,code,pad);','msg <- poly_sotp_decode_msg_spec code pad; status<-W32.zero;'),
 ('SOTP-option-spec-forgets-decode-failure',CONTRACTS,r'if pke_domain code /\ !poly_sotp_decode_fail_spec code pad then',r'if pke_domain code then'),
 ('SOTP-reencoder-returns-input-instead-of-calling-encoder',CONTRACTS,'rebuilt <@ SOTPEncode.run(oget msg,pad);','rebuilt <- code;'),
 ('SOTP-pad-not-uniform',CONTRACTS,'pad <$ uniform192;','pad <- witness;'),
 ('SOTP-message-chosen-after-observing-pad',CONTRACTS,'pad <$ uniform192; code <@ SOTPEncode.run(msg,pad);','pad <$ uniform192; msg<-pad_head pad; code <@ SOTPEncode.run(msg,pad);'),
 ('SOTP-rigidity-omits-success-premise',RIGIDITY,'lemma sotp_decode_encode_rigidity a pad : !poly_sotp_decode_fail_spec a pad =>','lemma sotp_decode_encode_rigidity a pad :'),
 ('SOTP-hiding-claims-uniform-ternary-instead-of-CBD',CONTRACTS,'Pr[SOTPUniformEncode.run(msg0) @ &m:event res]=mu pke_psi1 event.','Pr[SOTPUniformEncode.run(msg0) @ &m:event res]=mu uniform_ternary event.'),
)
