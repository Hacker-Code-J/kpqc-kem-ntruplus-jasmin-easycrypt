require import AllCore Distr FMap StdOrder.
from Jasmin require import JWord.
require import Array768 Array1152 Array2336.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768KeygenCompleteSpec.
require import NTRUPlus768ROMKeygen NTRUPlus768ROMOracles NTRUPlus768FreshRetryLaw.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768SpreadBase NTRUPlus768SpreadProcedures.
require import NTRUPlus768AcceptanceProbability.
import RealOrder.

(* This is generated-key validity, not public-byte canonicity alone. The
   witness is proof data and is not an input to the encryption procedure. *)
op [opaque] spread_valid_public_key (pk:W8.t Array1152.t) =
 exists (w:keygen_witness),pke_key_relation w /\ pk=w.`kg_pk.

lemma spread_key_valid_public w : pke_key_relation w=>spread_valid_public_key w.`kg_pk.
proof. move=>hk; rewrite /spread_valid_public_key; exists w; done. qed.

lemma spread_public_mass_bound pk m ct :
 spread_valid_public_key pk=>pke_domain m=>
 mu pke_psi1(fun r=>pke_enc_spec pk m r=Some ct)<=1%r/(2%r^768).
proof.
 rewrite /spread_valid_public_key; move=>[w [hk ->]] hm.
 exact(spread_base_bound w m ct hk hm).
qed.

lemma spread_pke_public_bound pk0 m0 ct0 &mem :
 spread_valid_public_key pk0=>pke_domain m0=>
 Pr[SpreadPKE.run(pk0,m0) @ &mem:res=Some ct0]<=1%r/(2%r^768).
proof.
 move=>hp hm.
 rewrite(spread_pke_probability pk0 m0 (fun out=>out=Some ct0) &mem hm).
 exact(spread_public_mass_bound pk0 m0 ct0 hp hm).
qed.
lemma spread_pke_public_bound_ph ct0 :
 phoare[SpreadPKE.run:spread_valid_public_key pk /\ pke_domain m ==>
 res=Some ct0]<=(1%r/(2%r^768)).
proof.
 bypr=> &mem [hp hm]; exact(spread_pke_public_bound pk{mem} m{mem} ct0 &mem hp hm).
qed.

(* The original public API performs its actual unbounded retries, Finish
   and workspace clear. This is a property of returned keys only. *)
lemma spread_keygen_public_valid (E<:KeygenExpand {-ROF}) :
 hoare[Keygen(UniformSeedRNG,E,SHAKEFROM).run:true ==>spread_valid_public_key res.`1].
proof.
 conseq(rom_keygen_public UniformSeedRNG E)=> />.
 move=>fm w hk.
 exact(spread_key_valid_public w (pke_key_from_rom w fm hk)).
qed.

(* The message is supplied before setup and the fresh encryption sample.
   The target ciphertext occurs only as a fixed event in the theorems. *)
module SpreadGenerated(E:KeygenExpand) = {
 proc run(m:pke_poly) : W8.t Array1152.t option = {
  var pk:W8.t Array1152.t;var sk:W8.t Array2336.t;
  var ct:W8.t Array1152.t option;
  (pk,sk)<@Keygen(UniformSeedRNG,E,SHAKEFROM).run();
  ct<@SpreadPKE.run(pk,m);
  return ct;
 }
}.
module SpreadGeneratedROM = {
 proc run(m:pke_poly) : W8.t Array1152.t option = {
  var ct:W8.t Array1152.t option;
  ROE.init();ROF.init();
  ct<@SpreadGenerated(ExpandROM).run(m);
  return ct;
 }
}.

lemma spread_generated_bound_ph (E<:KeygenExpand {-ROF}) ct0 :
 phoare[SpreadGenerated(E).run:pke_domain m ==>res=Some ct0]<=(1%r/(2%r^768)).
proof.
 proc;call(spread_pke_public_bound_ph ct0);call(spread_keygen_public_valid E);auto.
qed.
lemma spread_generated_bound (E<:KeygenExpand {-ROF}) m0 ct0 &mem :
 pke_domain m0=>Pr[SpreadGenerated(E).run(m0) @ &mem:res=Some ct0]<=1%r/(2%r^768).
proof. move=>hm; byphoare(spread_generated_bound_ph E ct0)=> //. qed.

(* Nonreturning ROM KeyGen contributes no ciphertext mass. No conditioning
   on return and no actual-ROM losslessness premise is used. *)
lemma spread_generated_rom_bound_ph ct0 :
 phoare[SpreadGeneratedROM.run:pke_domain m ==>res=Some ct0]<=(1%r/(2%r^768)).
proof.
 proc;call(spread_generated_bound_ph ExpandROM ct0).
 call(_:true ==>true);first by trivial.
 call(_:true ==>true);first by trivial.
 auto.
qed.
lemma spread_generated_rom_bound m0 ct0 &mem :
 pke_domain m0=>Pr[SpreadGeneratedROM.run(m0) @ &mem:res=Some ct0]<=1%r/(2%r^768).
proof. move=>hm; byphoare(spread_generated_rom_bound_ph ct0)=> //. qed.

(* Independent expansion has its separately established retry termination
   theorem. This does not supply losslessness for the ROM instance. *)
lemma spread_generated_fresh_lossless : islossless SpreadGenerated(FreshExpand).run.
proof.
 proc;call spread_pke_lossless.
 call(fresh_keygen_ll fresh_f_accept_positive fresh_g_accept_positive);auto.
qed.
