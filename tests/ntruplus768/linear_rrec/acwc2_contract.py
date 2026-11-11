"""Replacing checked RRec retains the actual ACWC2 experiment and its fixed G table."""
BRIDGE='ntruplus/proof/768/ref/linear_rrec/NTRUPlus768RRecACWC2Bridge.ec'
RULES=(
 (BRIDGE,'linear ACWC2 decoder retains actual PKE recovery, recovered-r G lookup, and SOTP decode',r'module LinearACWC2Dec(G:ACWC2GPort) = { proc run(pk:W8.t Array1152.t,sk:W8.t Array2336.t,ct:W8.t Array1152.t) : W8.t Array96.t option = { var code,recovered:pke_poly option; var pad:W8.t Array192.t; var msg:W8.t Array96.t option; code <@ PKEDec.run(ct,acwc2_secret_bytes sk); msg <- None; if(code<>None){ recovered <@ LinearRRec.run(pk,oget code,ct); if(recovered<>None){ pad <@ G.run(oget recovered); msg <@ SOTPDecode.run(oget code,pad); } } return msg; } }.'),
 (BRIDGE,'partial G calls preserve their complete abstract state in the decoder equivalence',r'lemma linear_acwc2_dec_equiv (G<:ACWC2GPort) : equiv[LinearACWC2Dec(G).run ~ ACWC2Dec(G).run: ={pk,sk,ct,glob G} ==> ={res,glob G}].'),
 (BRIDGE,'fixed oracle trial installs its supplied pads without redrawing G',r'module LinearACWC2FixedOracleTrial = { proc run(pads:W8.t Array192.t list,pk:W8.t Array1152.t,sk:W8.t Array2336.t,msg:W8.t Array96.t) : bool = { var failed:bool; ROG.init(); ACWC2EagerOracle.prepare(pads); failed <@ LinearACWC2RandomTrial.run(pk,sk,msg); return failed; } }.'),
 (BRIDGE,'unchanged unconditional expected-worst bound names actual linear trials under the same key and oracle laws',r'lemma linear_acwc2_fresh_worst_actual_calls &m : E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z])) (fun (out:keygen_output)=>E acwc2_gpads_law (fun (pads:W8.t Array192.t list)=>acwc2_finite_max acwc2_message_enum (fun (msg:W8.t Array96.t)=> Pr[LinearACWC2FixedOracleTrial.run(pads,out.`1.`kg_pk,out.`1.`kg_sk,msg) @ &m:res]))) <1%r/(2%r^353).'),
)
MUTATIONS=(
 ('linear-ACWC2-silently-retains-checked-RRec',BRIDGE,'recovered <@ LinearRRec.run(pk,oget code,ct);','recovered <@ RRec.run(pk,oget code,ct);'),
 ('linear-ACWC2-decoder-equivalence-drops-G-state',BRIDGE,'equiv[LinearACWC2Dec(G).run ~ ACWC2Dec(G).run: ={pk,sk,ct,glob G} ==> ={res,glob G}].','equiv[LinearACWC2Dec(G).run ~ ACWC2Dec(G).run: ={pk,sk,ct,glob G} ==> ={res}].'),
 ('linear-ACWC2-trial-redraws-the-fixed-G-table',BRIDGE,'ROG.init(); ACWC2EagerOracle.prepare(pads);','ROG.init(); pads <$ acwc2_gpads_law; ACWC2EagerOracle.prepare(pads);'),
 ('linear-ACWC2-final-bound-assumes-a-zero-error-key',BRIDGE,'lemma linear_acwc2_fresh_worst_actual_calls &m :','lemma linear_acwc2_fresh_worst_actual_calls &m : (forall w,acwc2_base_mean w=0%r) =>'),
)
