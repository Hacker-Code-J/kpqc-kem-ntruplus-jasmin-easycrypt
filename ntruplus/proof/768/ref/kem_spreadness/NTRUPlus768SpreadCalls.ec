require import AllCore Distr FMap FSet.
from Jasmin require import JWord.
require import Array96 Array192 Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768PolySOTPEncodeCheckedRoundTrip.
require import NTRUPlus768SOTPContracts NTRUPlus768ACWC2HashG NTRUPlus768RRecCodec.
require import NTRUPlus768ROMOracles NTRUPlus768KeygenCompleteProof.
require import NTRUPlus768SpreadProcedures NTRUPlus768SpreadCache.
require import NTRUPlus768ACWC2Oracle NTRUPlus768SpreadTransfer.

(* A distinct experiment explicitly starts a fresh G table. *)
module SpreadFreshG = {
 proc run(pk:W8.t Array1152.t,msg:W8.t Array96.t) : W8.t Array1152.t option = {
  var ct:W8.t Array1152.t option;
  ROG.init();ct <@ SpreadEncoded.run(pk,msg);return ct;
 }
}.

lemma spread_sotp_domain msg pad : pke_domain(poly_sotp_encode_spec msg pad).
proof. rewrite sotp_domainE;exact(poly_sotp_encode_spec_trit_input msg pad). qed.

(* The actual CBD, serialized G query, SOTP and PKE kernels agree with
   the reference while preserving the complete, possibly nonempty G map. *)
lemma spread_encoded_equiv : equiv[SpreadEncoded.run ~ SpreadEncodedValue.run:
 ={pk,msg,ROG.m} ==> ={res,ROG.m}].
proof.
 proc;seq 1 1:(={pk,msg,r,ROG.m} /\ pke_domain r{1}).
 + outline{2} 1 ~ SpreadSampleValue.run.
   call spread_sample_equiv;auto.
 seq 1 1:(={pk,msg,r,pad,ROG.m} /\ pke_domain r{1}).
 + call acwc2_hash_g_equiv;auto.
 ecall{1}(spread_enc_correct pk{1} (poly_sotp_encode_spec msg{1} pad{1}) r{1}).
 ecall{1}(sotp_encode_correct msg{1} pad{1}).
 auto=> />;smt(spread_sotp_domain).
qed.

lemma spread_encoded_probability pk msg event &m :
 Pr[SpreadEncoded.run(pk,msg) @ &m:event res]=
 Pr[SpreadEncodedValue.run(pk,msg) @ &m:event res].
proof. byequiv spread_encoded_equiv=> //. qed.

lemma spread_encoded_actual_bound w msg ct &m : pke_key_relation w=>
 Pr[SpreadEncoded.run(w.`kg_pk,msg) @ &m:res=Some ct]<=
 ((fsize ROG.m{m}+1)%r/(2%r^768)).
proof.
 move=>hw;rewrite(spread_encoded_probability w.`kg_pk msg (fun out=>out=Some ct) &m).
 byphoare(spread_encoded_cache_bound w msg ct ROG.m{m} hw)=> //.
qed.

lemma spread_encoded_actual_ph w msg0 ct0 gm0 : pke_key_relation w=>
 phoare[SpreadEncoded.run:pk=w.`kg_pk /\ msg=msg0 /\ ROG.m=gm0 ==>
 res=Some ct0]<=((fsize gm0+1)%r/(2%r^768)).
proof.
 move=>hw;bypr=> &mem [hp [hm hg]];rewrite hp hm.
 have h:=spread_encoded_actual_bound w msg0 ct0 &mem hw.
 by move:h;rewrite hg.
qed.

lemma spread_encoded_empty_ph w msg0 ct0 : pke_key_relation w=>
 phoare[SpreadEncoded.run:pk=w.`kg_pk /\ msg=msg0 /\ ROG.m=empty ==>
 res=Some ct0]<=(1%r/(2%r^768)).
proof.
 move=>hw;have h:=spread_encoded_actual_ph w msg0 ct0 empty hw.
 by move:h;rewrite fsize_empty /=.
qed.

lemma spread_fresh_g_lossless : islossless SpreadFreshG.run.
proof. proc;call spread_encoded_lossless;call rog_init_ll;auto. qed.

lemma spread_fresh_g_bound w msg0 ct0 &m : pke_key_relation w=>
 Pr[SpreadFreshG.run(w.`kg_pk,msg0) @ &m:res=Some ct0]<=1%r/(2%r^768).
proof.
 move=>hw;byphoare(_:pk=w.`kg_pk /\ msg=msg0 ==>res=Some ct0)=> //.
 proc;call(spread_encoded_empty_ph w msg0 ct0 hw);inline ROG.init;auto.
qed.

(* A prepared full function agrees with the actual caller on every
   sampled trit input. This is an equality, not a fixed-G rho bound. *)
lemma spread_encoded_prepared_actual w msg g gm ct &m :
 acwc2_cache_matches g gm=>ROG.m{m}=gm=>
 Pr[SpreadEncoded.run(w.`kg_pk,msg) @ &m:res=Some ct]=spread_cipher_mass w msg g ct.
proof.
 move=>hc hg;rewrite(spread_encoded_probability w.`kg_pk msg (fun out=>out=Some ct) &m).
 exact(spread_encoded_prepared_probability w msg g gm ct &m hc hg).
qed.
