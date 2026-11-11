require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array1152.
require import NTRUPlus768SecKeygen NTRUPlus768SecBaseGames.
require import NTRUPlus768CPAReduction NTRUPlus768CPAChallengeBridge.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768FreshRetryLaw NTRUPlus768AcceptanceProbability.
require import NTRUPlus768GenModel NTRUPlus768GenDistribution NTRUPlus768GenKeyProjection.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768ROMOracles NTRUPlus768CanonicalDecoder NTRUPlus768EncapGuardSpec.
require import NTRUPlus768OWCodec NTRUPlus768OWCodecProof.

(* The sampler is a distributional specification of the actual byte key.
   Both sides below have no oracle/global-state effect. Its final exact
   equivalence can therefore be composed with an arbitrary continuation. *)
op [opaque] ow_public_key_law = dmap gen_fg_law
 (fun (fg:NTRUPoly.poly*NTRUPoly.poly)=>ow_encode(gen_public_key fg.`1 fg.`2)).
module OWKeySample = {
 proc run() : W8.t Array1152.t = {
  var fg:NTRUPoly.poly*NTRUPoly.poly;
  fg<$gen_fg_law;
  return ow_encode(gen_public_key fg.`1 fg.`2);
 }
}.

lemma ow_base_late_probability &m (event:W8.t Array1152.t->bool) :
 Pr[SecBaseLateF.run()@&m:event res]=Pr[SecBaseKeygen.run()@&m:event res].
proof.
 byequiv(_:true ==> ={res})=> //.
 proc*;inline{1} SecBaseLateF.run;wp;call{1} rof_get_ll;call(sec_pk_same SecBaseKeygen);auto.
qed.
lemma ow_base_rom_probability &m (event:W8.t Array1152.t->bool) :
 Pr[SecBaseKeygen.run()@&m:event res]=Pr[SecPublicROMKeygen.run()@&m:event res].
proof.
 rewrite -(ow_base_late_probability &m event).
 apply/eq_sym;by byequiv sec_keygen_hoist=> //.
qed.

lemma ow_public_rom_canonical :
 phoare[SecPublicROMKeygen.run:true ==>encap_key_canonical res]=1%r.
proof.
 have hc:phoare[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run:
 true ==>encap_key_canonical res.`1]=1%r.
 + by conseq fresh_keygen_lossless_unconditional cpa_keygen_canonical.
 proc;call hc;auto.
qed.
lemma ow_base_canonical :
 phoare[SecBaseKeygen.run:true ==>encap_key_canonical res]=1%r.
proof.
 bypr=> &m _;rewrite(ow_base_rom_probability &m encap_key_canonical).
 by byphoare ow_public_rom_canonical=> //.
qed.
lemma ow_base_canonical_hoare :
 hoare[SecBaseKeygen.run:true ==>encap_key_canonical res].
proof. by conseq ow_base_canonical. qed.

lemma ow_core_public_projection (w:keygen_witness) :
 (gen_actual_core w).`1=ow_key_poly w.`kg_pk.
proof. by rewrite /gen_actual_core /gen_serialized_core ow_decode_poly. qed.

lemma ow_public_rom_polynomial_law &m (event:NTRUPoly.poly->bool) :
 Pr[SecPublicROMKeygen.run()@&m:event(ow_key_poly res)]=
 mu gen_key_law(fun (key:NTRUPoly.poly*NTRUPoly.poly)=>event key.`1).
proof.
 byphoare(_:true ==>event(ow_key_poly res))=> //.
 proc;inline Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run;wp.
 call(gen_fresh_core_phoare(fun (key:NTRUPoly.poly*NTRUPoly.poly)=>event key.`1)).
 auto=> />;smt(ow_core_public_projection).
qed.
lemma ow_base_polynomial_law &m (event:NTRUPoly.poly->bool) :
 Pr[SecBaseKeygen.run()@&m:event(ow_key_poly res)]=
 mu gen_fg_law(fun (fg:NTRUPoly.poly*NTRUPoly.poly)=>event(gen_public_key fg.`1 fg.`2)).
proof.
 rewrite(ow_base_rom_probability &m (fun pk=>event(ow_key_poly pk)))
 (ow_public_rom_polynomial_law &m event) /gen_key_law dmapE /gen_key_from_fg /=.
 done.
qed.

lemma ow_base_reencode_probability &m (event:W8.t Array1152.t->bool) :
 Pr[SecBaseKeygen.run()@&m:event res]=
 Pr[SecBaseKeygen.run()@&m:event(ow_encode(ow_key_poly res))].
proof.
 byequiv(_:true ==>res{1}=ow_encode(ow_key_poly res{2}))=> //.
 conseq(sec_pk_same SecBaseKeygen) ow_base_canonical_hoare _=> //.
 smt(ow_encode_decode).
qed.

lemma ow_base_keygen_bytes &m (event:W8.t Array1152.t->bool) :
 Pr[SecBaseKeygen.run()@&m:event res]=mu ow_public_key_law event.
proof.
 rewrite(ow_base_reencode_probability &m event)
 (ow_base_polynomial_law &m (fun p=>event(ow_encode p))) /ow_public_key_law dmapE /=.
 done.
qed.
lemma ow_key_sample_law &m (event:W8.t Array1152.t->bool) :
 Pr[OWKeySample.run()@&m:event res]=mu ow_public_key_law event.
proof.
 rewrite /ow_public_key_law dmapE.
 byphoare(_:true ==>event res)=> //;proc;rnd;auto.
qed.

lemma ow_base_keygen_sample :
 equiv[SecBaseKeygen.run ~ OWKeySample.run:true ==> ={res}].
proof.
 bypr(res{1})(res{2})=> // &1 &2 pk.
 by rewrite(ow_base_keygen_bytes &1 (pred1 pk))(ow_key_sample_law &2 (pred1 pk)).
qed.
