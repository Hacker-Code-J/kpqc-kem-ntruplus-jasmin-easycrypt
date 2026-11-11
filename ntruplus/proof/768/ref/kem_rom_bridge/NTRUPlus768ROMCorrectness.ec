require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152 Array2336 Array14466 Array13634 Array13506.
require import NTRUPlus768ROMOracles NTRUPlus768ROMPayloadHash.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768KEMPayloadAlgebra.
require import NTRUPlus768ValidKeyM1Recovery NTRUPlus768EncapGuardSpec.
require import NTRUPlus768ROMKeygen NTRUPlus768ROMEncap NTRUPlus768ROMDecap.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768KeygenCompleteSpec.
require import NTRUPlus768EncapCompleteRNG NTRUPlus768EncapCompleteProof.
require import NTRUPlus768DecapCompleteProof NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768KEMFailureModel NTRUPlus768KEMFailureProof.

(* Exact existing array callers in the classical lazy-ROM model. Both random
   byte ports may share B state. B is separated from all four oracle tables. *)
module KEMROMCorrectness(B:KEMRNG) = {
 proc run() : bool = {
  var failed:bool;
  ROE.init(); ROF.init(); ROG.init(); ROH.init();
  failed <@ KEMCorrectness(KeygenRNGPort(B),ExpandROM,SHAKEFROM,SHAKEGROM,SHAKEHROM,EncapRNGPort(B)).run();
  return failed;
 }
}.

(* The only new observation reads cache entries already queried by the real
   encapsulation. Actual coins are retained locally by the existing private
   wrapper; actual coin and workspace clearing still executes. *)
module KEMROMPrivate(B:KEMRNG) = {
 proc run() : bool * bool = {
  var w:keygen_witness; var cleared:W8.t Array14466.t;
  var coins:W8.t Array96.t; var hout:W8.t Array224.t; var pad:W8.t Array192.t;
  var suffix:W8.t Array32.t; var bad:bool;
  var er:encap_result; var dr:decap_result;
  ROE.init(); ROF.init(); ROG.init(); ROH.init();
  (w,cleared) <@ KeygenInstrumented(KeygenRNGPort(B),ExpandROM,SHAKEFROM).run(witness);
  (er,coins) <@ EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,EncapRNGPort(B)).run(w.`kg_pk,witness);
  suffix <- complete_sk_suffix w.`kg_sk;
  hout <- oget ROH.m.[(coins,suffix)];
  pad <- oget ROG.m.[payload_serialized hout];
  bad <- !sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf (payload_r hout) (payload_m coins pad);
  dr <@ CompleteDecaps(SHAKEGROM,SHAKEHROM).run(er.`1,w.`kg_sk,witness);
  return (kem_failure er dr,bad);
 }
}.

lemma rom_decap_from_relation (w:keygen_witness) coins0 suffix0 fm0 gm0 hm0 (er:encap_result) :
 hoare[CompleteDecaps(SHAKEGROM,SHAKEHROM).run:
 ct=er.`1 /\ sk=w.`kg_sk /\ workspace=witness /\ ROF.m=fm0 /\ ROG.m=gm0 /\ ROH.m=hm0 /\
 rom_key_relation w fm0 /\ suffix0=complete_sk_suffix w.`kg_sk /\
 rom_encap_relation w.`kg_pk coins0 suffix0 fm0 gm0 hm0 (er.`1,er.`2,er.`3) /\
 sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf
   (payload_r (oget hm0.[(coins0,suffix0)]))
   (payload_m coins0 (oget gm0.[payload_serialized (oget hm0.[(coins0,suffix0)])])) ==>
 !kem_failure er res].
proof.
 case (rom_key_relation w fm0 /\ suffix0=complete_sk_suffix w.`kg_sk /\
 rom_encap_relation w.`kg_pk coins0 suffix0 fm0 gm0 hm0 (er.`1,er.`2,er.`3) /\
 sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf
   (payload_r (oget hm0.[(coins0,suffix0)]))
   (payload_m coins0 (oget gm0.[payload_serialized (oget hm0.[(coins0,suffix0)])]))) => H.
 + move: H => [hkey [hs [henc hn]]].
   rewrite /rom_key_relation in hkey.
   move: hkey => [hk hf].
   rewrite /rom_encap_relation in henc.
   move: henc => [hfs [hh [hg he]]].
   have hct := congr1
     (fun z:W8.t Array1152.t * W8.t Array32.t * W32.t => z.`1) _ _ he.
   have hss := congr1
     (fun z:W8.t Array1152.t * W8.t Array32.t * W32.t => z.`2) _ _ he.
   have hz := congr1
     (fun z:W8.t Array1152.t * W8.t Array32.t * W32.t => z.`3) _ _ he.
   rewrite /= in hct.
   rewrite /= in hss.
   rewrite /= in hz.
   rewrite hs in hh.
   rewrite hs in hg.
   rewrite hs in hn.
   rewrite hs in hct.
   rewrite hs in hss.
   conseq(rom_decap_success w coins0 (oget hm0.[(coins0,complete_sk_suffix w.`kg_sk)])
     (oget gm0.[payload_serialized (oget hm0.[(coins0,complete_sk_suffix w.`kg_sk)])]) gm0 hm0 witness hk hg hh hn) => />; first by smt().
   by rewrite /kem_failure /=; smt().
 conseq (_:false ==> true) => //; smt().
qed.

lemma rom_encap_from_key (Q<:EncapRNG {-ROF,-ROG,-ROH}) (w:keygen_witness) fm0 :
 hoare[EncapRandomInstrumented(SHAKEFROM,SHAKEGROM,SHAKEHROM,Q).run:
 pk=w.`kg_pk /\ ROF.m=fm0 /\ rom_key_relation w fm0 ==>
 rom_key_relation w ROF.m /\
 rom_encap_relation w.`kg_pk res.`2 (complete_sk_suffix w.`kg_sk)
   ROF.m ROG.m ROH.m (res.`1.`1,res.`1.`2,res.`1.`3)].
proof.
 case (rom_key_relation w fm0) => hk.
 + rewrite /rom_key_relation in hk; move:hk=>[hkey hf].
   have hcan:=payload_key_canonical _ _ _ _ _ _ _ _ hkey.
   move:hcan=>[hpk hsk].
   conseq(rom_encap_instrumented Q w.`kg_pk (complete_sk_suffix w.`kg_sk) fm0 hpk hf) => />;
     rewrite /rom_key_relation; smt().
 conseq (_:false ==> true) => //; smt().
qed.

lemma rom_decap_conditional (w:keygen_witness) coins0 suffix0 fm0 gm0 hm0 (er:encap_result) :
 hoare[CompleteDecaps(SHAKEGROM,SHAKEHROM).run:
 ct=er.`1 /\ sk=w.`kg_sk /\ workspace=witness /\ ROF.m=fm0 /\ ROG.m=gm0 /\ ROH.m=hm0 /\
 rom_key_relation w fm0 /\ suffix0=complete_sk_suffix w.`kg_sk /\
 rom_encap_relation w.`kg_pk coins0 suffix0 fm0 gm0 hm0 (er.`1,er.`2,er.`3) ==>
 sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf
   (payload_r (oget hm0.[(coins0,suffix0)]))
   (payload_m coins0 (oget gm0.[payload_serialized (oget hm0.[(coins0,suffix0)])])) =>
 !kem_failure er res].
proof.
 case (sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf
   (payload_r (oget hm0.[(coins0,suffix0)]))
   (payload_m coins0 (oget gm0.[payload_serialized (oget hm0.[(coins0,suffix0)])]))) => hn.
 + conseq(rom_decap_from_relation w coins0 suffix0 fm0 gm0 hm0 er) => />; smt().
 conseq (_:true ==> true) => //; smt().
qed.

lemma rom_public_projection (B<:KEMRNG {-ROE,-ROF,-ROG,-ROH}) :
 equiv[KEMROMCorrectness(B).run ~ KEMROMPrivate(B).run:
 ={glob B,glob ROE,glob ROF,glob ROG,glob ROH} ==>
 res{1}=res{2}.`1 /\ ={glob B,glob ROE,glob ROF,glob ROG,glob ROH}].
proof.
 proc; inline{1} KEMCorrectness(KeygenRNGPort(B),ExpandROM,SHAKEFROM,SHAKEGROM,SHAKEHROM,EncapRNGPort(B)).run
   Keygen(KeygenRNGPort(B),ExpandROM,SHAKEFROM).run.
 seq 6 5 : (pk{1}=w{2}.`kg_pk /\ sk{1}=w{2}.`kg_sk /\
   ={glob B,glob ROE,glob ROF,glob ROG,glob ROH}).
 + wp; call (_: ={glob B,glob ROE,glob ROF}); first by sim.
   inline ROE.init ROF.init ROG.init ROH.init.
   by auto.
 wp; call (_: ={glob ROG,glob ROH}); first by sim.
 wp; call(encap_instrumented_projection (EncapRNGPort(B)) SHAKEFROM SHAKEGROM SHAKEHROM).
 by auto => />.
qed.

lemma rom_failure_implies_bad (B<:KEMRNG {-ROE,-ROF,-ROG,-ROH}) :
 hoare[KEMROMPrivate(B).run:true ==> res.`1 => res.`2].
proof.
 proc.
 seq 6 : (rom_key_relation w ROF.m /\
 rom_encap_relation w.`kg_pk coins (complete_sk_suffix w.`kg_sk) ROF.m ROG.m ROH.m (er.`1,er.`2,er.`3)).
 + ecall(rom_encap_from_key (EncapRNGPort(B)) w ROF.m).
   call(rom_keygen_instrumented (KeygenRNGPort(B)) ExpandROM).
   inline ROE.init ROF.init ROG.init ROH.init.
   by auto => />.
 wp; ecall(rom_decap_conditional w coins suffix ROF.m ROG.m ROH.m er).
 by auto => />; smt().
qed.

(* Event inclusion on returned executions. No losslessness is asserted for
   the finite-seed ROM retry loops; termination needs an additional premise. *)
lemma rom_failure_probability (B<:KEMRNG {-ROE,-ROF,-ROG,-ROH}) &m :
 Pr[KEMROMCorrectness(B).run() @ &m:res] <= Pr[KEMROMPrivate(B).run() @ &m:res.`2].
proof.
 have heq : Pr[KEMROMCorrectness(B).run() @ &m:res] = Pr[KEMROMPrivate(B).run() @ &m:res.`1].
 + by byequiv(rom_public_projection B).
 rewrite heq.
 have hz:Pr[KEMROMPrivate(B).run() @ &m:res.`1 /\ !res.`2]=0%r.
 + byphoare (_:true ==> res.`1 /\ !res.`2) => //; hoare.
   conseq(rom_failure_implies_bad B) => />; smt().
 rewrite Pr[mu_split res.`2] hz /=.
 by byequiv (_: ={glob B,glob ROE,glob ROF,glob ROG,glob ROH} ==> ={res}) => //; sim.
qed.
