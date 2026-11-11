require import AllCore List Distr FMap FSet.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array768 Array1152.
require import NTRUPlus768SimModel NTRUPlus768FOModel NTRUPlus768FOAlgebra NTRUPlus768FOProcedures.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768FONativeBridge.
require import NTRUPlus768PKEModel NTRUPlus768PKEProcedures NTRUPlus768PKECallProof.
require import NTRUPlus768ACWC2Model NTRUPlus768ACWC2Oracle NTRUPlus768SOTPContracts.
require import NTRUPlus768PolyCBD1Checked NTRUPlus768PolyCBD1CheckedProof NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768ROMOracles NTRUPlus768KEMPayloadSpec NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768CCAStatusAdapter NTRUPlus768CCADecapOracle.

(* This first-match operator fixes the same finite-list order as the actual
   scan. Order independence needs the separate good-entry uniqueness law. *)
op [opaque] sim_first ['a 'b] (p:'a->bool) (value:'a->'b) (xs:'a list) : 'b option =
 foldr (fun x rest=>if p x then Some(value x) else rest) None xs.
op [opaque] sim_entry_matches pk suffix g (log:(fo_h_input,W8.t Array224.t)fmap) ct (input:fo_h_input) =
 input.`2=suffix /\ sim_candidate pk g input (oget log.[input])=Some ct.
op [opaque] sim_lookup_result pk suffix g (log:(fo_h_input,W8.t Array224.t)fmap) ct =
 sim_first (sim_entry_matches pk suffix g log ct)
   (fun input=>payload_shared_key(oget log.[input])) (elems(fdom log)).
op [opaque] sim_lookup_spec pk suffix cstar g (log:(fo_h_input,W8.t Array224.t)fmap) ct =
 if cstar=Some ct then None else sim_lookup_result pk suffix g log ct.

module SimEncrypt(G:FOGPort) = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t,hout:W8.t Array224.t) : W8.t Array1152.t option = {
  var r,code:pke_poly;var pad:W8.t Array192.t;var ct:W8.t Array1152.t option;
  r <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(witness,complete_hash_tail hout);
  pad <@ FOHashG(FOGHash(G)).run(r);
  code <@ SOTPEncode.run(msg,pad);
  ct <@ PKEEnc.run(pk,code,r);
  return ct;
 }
}.

(* Public data only: no secret key, FOContext or physical H table is read.
   A local history snapshot also makes scan termination independent of any
   changes a generic G implementation might make outside its return value. *)
module SimLookup(G:FOGPort) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t) : cca_reply = {
  var answer:cca_reply;var star:W8.t Array1152.t option;
  var pk:W8.t Array1152.t;var suffix:W8.t Array32.t;
  var log:(fo_h_input,W8.t Array224.t)fmap;var todo:fo_h_input list;
  var input:fo_h_input;var hout:W8.t Array224.t;var candidate:W8.t Array1152.t option;
  answer<-None;
  SimPublic.count<-SimPublic.count+1;
  star<-SimPublic.cstar;
  if(star<>Some ct){
   pk<-SimPublic.pk;suffix<-SimPublic.suffix;log<-SimHistory.h;
   todo<-elems(fdom log);
   while(todo<>[] /\ answer=None){
    input<-head witness todo;todo<-behead todo;
    if(input.`2=suffix){
     hout<-oget log.[input];
     candidate<@SimEncrypt(G).run(pk,input.`1,hout);
     if(candidate=Some ct){answer<-Some(payload_shared_key hout);}
    }
   }
  }
  return answer;
 }
}.

lemma sim_first_nil ['a 'b] (p:'a->bool) (value:'a->'b) : sim_first p value []=None.
proof. by rewrite /sim_first. qed.
lemma sim_first_cons ['a 'b] (p:'a->bool) (value:'a->'b) x xs :
 sim_first p value (x::xs)=if p x then Some(value x) else sim_first p value xs.
proof. by rewrite /sim_first /=. qed.
lemma sim_first_step ['a 'b] (p:'a->bool) (value:'a->'b) xs : xs<>[]=>
 sim_first p value xs=if p(head witness xs) then Some(value(head witness xs)) else sim_first p value(behead xs).
proof. by case xs=> // x xs _; rewrite sim_first_cons. qed.
lemma sim_first_find ['a 'b] (p:'a->bool) (value:'a->'b) xs :
 sim_first p value xs=
 if has p xs then Some(value(nth witness xs (find p xs))) else None.
proof.
 elim:xs=>[|x xs ih]; first by rewrite sim_first_nil.
 rewrite sim_first_cons /=; case(p x)=>hp; first done.
 rewrite ih.
 have hn:=find_ge0 p xs.
 case(has p xs)=>hh; rewrite /=; smt().
qed.

lemma sim_g_hash_lossless (G<:FOGPort) : islossless G.get=>islossless FOGHash(G).shake.
proof. move=>h; proc;call h;auto. qed.
lemma sim_encrypt_lossless (G<:FOGPort) : islossless G.get=>islossless SimEncrypt(G).run.
proof.
 move=>h;proc;call pke_enc_lossless;call sotp_encode_lossless;
 call(fo_hash_g_lossless (FOGHash(G)) (sim_g_hash_lossless G h));call poly_cbd1_lossless;auto.
qed.
lemma sim_hash_g_actual :
 equiv[FOHashG(FOGHash(FOGActual)).run ~ FOHashG(SHAKEGROM).run:
 ={r,ROG.m} ==> ={res,ROG.m}].
proof. proc;call fo_g_hash_actual;call(_:true);first by sim. auto. qed.
lemma sim_hash_g_prepared r0 g gm0 : pke_domain r0=>acwc2_cache_matches g gm0=>
 hoare[FOHashG(FOGHash(FOGActual)).run:r=r0 /\ ROG.m=gm0 ==>res=g r0 /\ ROG.m=gm0].
proof.
 move=>hr hg;conseq sim_hash_g_actual (fo_hash_g_prepared r0 g gm0 hr hg);smt().
qed.
lemma sim_candidate_codeE pk g (input:fo_h_input) hout :
 pke_enc_spec pk (acwc2_code g input.`1 (fo_randomness hout)) (fo_randomness hout)=sim_candidate pk g input hout.
proof. by rewrite /sim_candidate /acwc2_code. qed.
lemma sim_encrypt_prepared pk0 (input0:fo_h_input) hout0 g gm0 : acwc2_cache_matches g gm0=>
 hoare[SimEncrypt(FOGActual).run:
 pk=pk0 /\ msg=input0.`1 /\ hout=hout0 /\ ROG.m=gm0 ==>
 res=sim_candidate pk0 g input0 hout0 /\ ROG.m=gm0].
proof.
 move=>hg;proc.
 call(pke_enc_functional pk0 (acwc2_code g input0.`1 (fo_randomness hout0)) (fo_randomness hout0)
   (acwc2_code_domain _ _ _) (fo_randomness_domain hout0)).
 call(sotp_encode_functional input0.`1 (g(fo_randomness hout0))).
 call(sim_hash_g_prepared (fo_randomness hout0) g gm0 (fo_randomness_domain hout0) hg).
 call(poly_cbd1_functional witness (complete_hash_tail hout0)).
 skip;rewrite fo_randomnessE fo_codeE (sim_candidate_codeE pk0 g input0 hout0);auto.
qed.

lemma sim_behead_decreases ['a] (xs:'a list) : xs<>[]=>0<=size(behead xs)<size xs.
proof. case xs=> // x xs _ /=; smt(size_ge0). qed.

lemma sim_lookup_lossless (G<:FOGPort) : islossless G.get=>islossless SimLookup(G).decap.
proof.
 move=>h;proc;sp 3;if;last by auto.
 while true (size todo).
 + move=>z;sp 2;if.
   - wp;call(sim_encrypt_lossless G h);auto=> />;smt(sim_behead_decreases).
   auto=> />;smt(sim_behead_decreases).
 auto=> />;smt(size_ge0).
qed.

lemma sim_lookup_frame (G<:FOGPort {-SimPublic,-SimHistory}) pk0 suffix0 star0 log0 n0 :
 hoare[SimLookup(G).decap:
 SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\
 SimPublic.count=n0 /\ SimHistory.h=log0 ==>
 SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\
 SimPublic.count=n0+1 /\ SimHistory.h=log0].
proof.
 proc;sp 3;if;last by auto.
 while(SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\
   SimPublic.count=n0+1 /\ SimHistory.h=log0).
 + sp 2;if;last by auto.
   wp;call(_:true ==>true);first by trivial.
   auto.
 auto.
qed.

lemma sim_lookup_challenge (G<:FOGPort) ct0 n0 gm0 log0 :
 phoare[SimLookup(G).decap:
 ct=ct0 /\ SimPublic.cstar=Some ct0 /\ SimPublic.count=n0 /\ ROG.m=gm0 /\ SimHistory.h=log0 ==>
 res=None /\ SimPublic.count=n0+1 /\ ROG.m=gm0 /\ SimHistory.h=log0]=1%r.
proof. proc;rcondf 4;auto. qed.

lemma sim_lookup_step pk suffix g log ct todo : todo<>[]=>
 sim_first (sim_entry_matches pk suffix g log ct)
  (fun input=>payload_shared_key(oget log.[input])) todo=
 if (head witness todo).`2=suffix /\
    sim_candidate pk g (head witness todo) (oget log.[head witness todo])=Some ct
 then Some(payload_shared_key(oget log.[head witness todo]))
 else sim_first (sim_entry_matches pk suffix g log ct)
  (fun input=>payload_shared_key(oget log.[input])) (behead todo).
proof.
 move=>hn;rewrite(sim_first_step _ _ todo hn);by rewrite /sim_entry_matches.
qed.
lemma sim_first_stop ['a 'b] (p:'a->bool) (value:'a->'b) xs (answer:'b option) :
 !(xs<>[] /\ answer=None)=>
 (if answer=None then sim_first p value xs else answer)=answer.
proof.
 move=>hs;case(answer=None)=>ha;last done.
 have hx:xs=[] by smt().
 by rewrite ha hx sim_first_nil.
qed.

lemma sim_lookup_value pk0 suffix0 star0 log0 ct0 g gm0 : acwc2_cache_matches g gm0=>
 hoare[SimLookup(FOGActual).decap:
 ct=ct0 /\ SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\
 SimHistory.h=log0 /\ ROG.m=gm0 ==>
 res=sim_lookup_spec pk0 suffix0 star0 g log0 ct0 /\ ROG.m=gm0].
proof.
 move=>hg;case(star0=Some ct0)=>hb;proc.
 + rcondf 4;first by auto.
   auto=> />;by rewrite /sim_lookup_spec hb.
 rcondt 4;first by auto.
 while(pk=pk0 /\ suffix=suffix0 /\ log=log0 /\ ct=ct0 /\ ROG.m=gm0 /\
   (if answer=None then
     sim_first (sim_entry_matches pk0 suffix0 g log0 ct0)
       (fun input=>payload_shared_key(oget log0.[input])) todo
    else answer)=sim_lookup_result pk0 suffix0 g log0 ct0).
 + sp 2;if.
   - wp;ecall(sim_encrypt_prepared pk0 input (oget log0.[input]) g gm0 hg).
     auto=> />.
     move=> &hr todo0 hct hgm hi hn.
     move:hi;rewrite(sim_lookup_step pk{hr} (head witness todo0).`2 g log{hr} ct{hr} todo0 hn) /=.
     by case(sim_candidate pk{hr} g (head witness todo0) (oget log{hr}.[head witness todo0])=Some ct{hr});auto.
   auto=> />.
   move=> &hr todo0 hct hgm hi hn hs.
   by move:hi;rewrite(sim_lookup_step pk{hr} suffix{hr} g log{hr} ct{hr} todo0 hn) hs /=.
 auto=> />.
 clear hg;rewrite /sim_lookup_spec hb /sim_lookup_result; smt(sim_first_stop).
qed.

lemma sim_first_none ['a 'b] (p:'a->bool) (value:'a->'b) xs :
 sim_first p value xs=None <=> !has p xs.
proof. rewrite sim_first_find;by case(has p xs). qed.

lemma sim_first_some ['a 'b] (p:'a->bool) (value:'a->'b) xs key :
 sim_first p value xs=Some key=>exists x,List.mem xs x /\ p x /\ value x=key.
proof.
 elim:xs=>[|x xs ih];first by rewrite sim_first_nil.
 rewrite sim_first_cons;case(p x)=>hp.
 + move=>/someI he;exists x;by rewrite hp he.
 move=>/ih [y [hy [hpy hv]]];exists y;by rewrite hy hpy hv orbT.
qed.

lemma sim_lookup_result_none pk suffix g log ct :
 sim_lookup_result pk suffix g log ct=None <=>
 forall input,input \in log=>!sim_entry_matches pk suffix g log ct input.
proof.
 rewrite /sim_lookup_result sim_first_none List.hasPn.
 have hm:forall input,List.mem (elems(fdom log)) input <=> input \in log
  by move=>input;rewrite -FSet.memE mem_fdom.
 by smt().
qed.

lemma sim_lookup_result_found pk suffix g log ct key :
 sim_lookup_result pk suffix g log ct=Some key=>
 exists input hout,log.[input]=Some hout /\ input.`2=suffix /\
 sim_candidate pk g input hout=Some ct /\ key=payload_shared_key hout.
proof.
 rewrite /sim_lookup_result;move=>/sim_first_some [input [hm [hp hv]]].
 have hd:input \in log by move:hm;rewrite -FSet.memE mem_fdom.
 have he:=some_oget log.[input] hd.
 exists input (oget log.[input]);move:hp;rewrite /sim_entry_matches;by smt().
qed.

lemma sim_lookup_result_unique pk suffix g log ct input hout :
 log.[input]=Some hout=>sim_entry_matches pk suffix g log ct input=>
 (forall other otherout,log.[other]=Some otherout=>
   sim_entry_matches pk suffix g log ct other=>payload_shared_key otherout=payload_shared_key hout)=>
 sim_lookup_result pk suffix g log ct=Some(payload_shared_key hout).
proof.
 move=>hi hp hu.
 have hdom:input \in log by rewrite /dom hi.
 have hn:sim_lookup_result pk suffix g log ct<>None by smt(sim_lookup_result_none).
 have he:=some_oget (sim_lookup_result pk suffix g log ct) hn.
 pose key:=oget(sim_lookup_result pk suffix g log ct).
 have [other otherout [ho [hs [hc hk]]]]:=sim_lookup_result_found pk suffix g log ct key he.
 have hpother:sim_entry_matches pk suffix g log ct other
  by rewrite /sim_entry_matches ho /= hs hc.
 have hv:=hu other otherout ho hpother.
 by rewrite he -/key hk hv.
qed.

lemma sim_lookup_functional pk0 suffix0 star0 log0 n0 ct0 g gm0 : acwc2_cache_matches g gm0=>
 hoare[SimLookup(FOGActual).decap:
 ct=ct0 /\ SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\
 SimPublic.count=n0 /\ SimHistory.h=log0 /\ ROG.m=gm0 ==>
 res=sim_lookup_spec pk0 suffix0 star0 g log0 ct0 /\ ROG.m=gm0 /\
 SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\
 SimPublic.count=n0+1 /\ SimHistory.h=log0].
proof.
 move=>hg;conseq(sim_lookup_value pk0 suffix0 star0 log0 ct0 g gm0 hg)
 (sim_lookup_frame FOGActual pk0 suffix0 star0 log0 n0);smt().
qed.

lemma sim_lookup_correct pk0 suffix0 star0 log0 n0 ct0 g gm0 : acwc2_cache_matches g gm0=>
 phoare[SimLookup(FOGActual).decap:
 ct=ct0 /\ SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\
 SimPublic.count=n0 /\ SimHistory.h=log0 /\ ROG.m=gm0 ==>
 res=sim_lookup_spec pk0 suffix0 star0 g log0 ct0 /\ ROG.m=gm0 /\
 SimPublic.pk=pk0 /\ SimPublic.suffix=suffix0 /\ SimPublic.cstar=star0 /\
 SimPublic.count=n0+1 /\ SimHistory.h=log0]=1%r.
proof.
 move=>hg;conseq(sim_lookup_lossless FOGActual rog_get_ll)
 (sim_lookup_functional pk0 suffix0 star0 log0 n0 ct0 g gm0 hg);smt().
qed.
