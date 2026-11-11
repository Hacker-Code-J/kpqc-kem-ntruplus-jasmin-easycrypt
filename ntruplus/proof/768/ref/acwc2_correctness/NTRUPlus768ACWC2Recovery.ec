require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array96 Array192 Array768 Array1152 Array2336.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768PKECallProof.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768EncapGuardSpec.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768PolySOTPRoundTrip.
require import NTRUPlus768SOTPContracts NTRUPlus768RRecModel NTRUPlus768RRecAlgebra NTRUPlus768RRecCallProof.
require import NTRUPlus768ACWC2HashG NTRUPlus768RRecCodec NTRUPlus768ROMOracles.
require import NTRUPlus768ACWC2Model NTRUPlus768ACWC2Procedures.

(* The invariant is explicit: a full-function reference or a completed
   cache supplies it. It is not an unconditional fixed-function claim
   about an initially empty lazy random oracle. *)
lemma acwc2_enc_functional (G<:ACWC2GPort) (g:acwc2_g_map) (I:(glob G)->bool) pk0 msg0 r0 :
 (forall x,pke_domain x => hoare[G.run:r=x /\ I(glob G) ==>res=g x /\ I(glob G)]) =>
 pke_domain r0 =>
 hoare[ACWC2Enc(G).run:pk=pk0 /\ msg=msg0 /\ r=r0 /\ I(glob G) ==>
 res=acwc2_enc_spec g pk0 msg0 r0 /\ I(glob G)].
proof.
 move=>hG hr; proc.
 call(pke_enc_functional pk0 (acwc2_code g msg0 r0) r0 (acwc2_code_domain g msg0 r0) hr).
 call(sotp_encode_functional msg0 (g r0)); call(hG r0 hr).
 skip; rewrite (acwc2_codeE g msg0 r0) (acwc2_enc_specE g pk0 msg0 r0); auto.
qed.
lemma acwc2_dec_functional (G<:ACWC2GPort) (g:acwc2_g_map) (I:(glob G)->bool) pk0 sk0 ct0 :
 (forall x,pke_domain x => hoare[G.run:r=x /\ I(glob G) ==>res=g x /\ I(glob G)]) =>
 hoare[ACWC2Dec(G).run:pk=pk0 /\ sk=sk0 /\ ct=ct0 /\ I(glob G) ==>
 res=acwc2_dec_spec g pk0 sk0 ct0 /\ I(glob G)].
proof.
 move=>hG.
 case(pke_dec_spec ct0 (acwc2_secret_bytes sk0)=None)=>hc; last first.
 + case(rrec_spec pk0 (oget(pke_dec_spec ct0 (acwc2_secret_bytes sk0))) ct0=None)=>hr; last first.
   - have hd:pke_domain(oget(rrec_spec pk0 (oget(pke_dec_spec ct0 (acwc2_secret_bytes sk0))) ct0)).
     + have [_ [hd _]]:=rrec_spec_sound _ _ _ _ (some_oget _ hr); exact hd.
     proc; rcondt 3.
     + wp; call(pke_dec_functional ct0 (acwc2_secret_bytes sk0)); auto.
     rcondt 4.
     + call(rrec_functional pk0 (oget(pke_dec_spec ct0 (acwc2_secret_bytes sk0))) ct0).
       wp; call(pke_dec_functional ct0 (acwc2_secret_bytes sk0)); auto.
     call(sotp_decode_functional (oget(pke_dec_spec ct0 (acwc2_secret_bytes sk0)))
       (g (oget(rrec_spec pk0 (oget(pke_dec_spec ct0 (acwc2_secret_bytes sk0))) ct0)))).
     call(hG _ hd).
     call(rrec_functional pk0 (oget(pke_dec_spec ct0 (acwc2_secret_bytes sk0))) ct0).
     wp; call(pke_dec_functional ct0 (acwc2_secret_bytes sk0)).
     auto=> />; by rewrite /acwc2_dec_spec /= hc hr.
   proc; rcondt 3.
   + wp; call(pke_dec_functional ct0 (acwc2_secret_bytes sk0)); auto.
   rcondf 4.
   + call(rrec_functional pk0 (oget(pke_dec_spec ct0 (acwc2_secret_bytes sk0))) ct0).
     wp; call(pke_dec_functional ct0 (acwc2_secret_bytes sk0)); auto.
   call(rrec_functional pk0 (oget(pke_dec_spec ct0 (acwc2_secret_bytes sk0))) ct0).
   wp; call(pke_dec_functional ct0 (acwc2_secret_bytes sk0)).
   auto=> />; by rewrite /acwc2_dec_spec /= hc hr.
 proc; rcondf 3.
 + wp; call(pke_dec_functional ct0 (acwc2_secret_bytes sk0)); auto.
 wp; call(pke_dec_functional ct0 (acwc2_secret_bytes sk0)).
 auto=> />; by rewrite /acwc2_dec_spec hc.
qed.
lemma acwc2_roundtrip_functional (G<:ACWC2GPort) (g:acwc2_g_map) (I:(glob G)->bool) pk0 sk0 msg0 r0 :
 (forall x,pke_domain x => hoare[G.run:r=x /\ I(glob G) ==>res=g x /\ I(glob G)]) =>
 pke_domain r0 =>
 hoare[ACWC2RoundTrip(G).run:pk=pk0 /\ sk=sk0 /\ msg=msg0 /\ r=r0 /\ I(glob G) ==>
 res=acwc2_failure g pk0 sk0 msg0 r0 /\ I(glob G)].
proof.
 move=>hG hr; case(acwc2_enc_spec g pk0 msg0 r0=None)=>hc; proc.
 + rcondf 3.
   - wp; call(acwc2_enc_functional G g I pk0 msg0 r0 hG hr); auto.
   wp; call(acwc2_enc_functional G g I pk0 msg0 r0 hG hr).
   auto=> />; by rewrite /acwc2_failure hc.
 rcondt 3.
 + wp; call(acwc2_enc_functional G g I pk0 msg0 r0 hG hr); auto.
 wp; call(acwc2_dec_functional G g I pk0 sk0 (oget(acwc2_enc_spec g pk0 msg0 r0)) hG).
 wp; call(acwc2_enc_functional G g I pk0 msg0 r0 hG hr).
 auto=> />; by rewrite /acwc2_failure /= hc.
qed.

lemma acwc2_full_g_functional g0 r0 :
 hoare[ACWC2FullG.run:r=r0 /\ ACWC2FullG.table=g0 ==>res=g0 r0 /\ ACWC2FullG.table=g0].
proof. proc; auto. qed.
lemma acwc2_full_roundtrip_functional g0 pk0 sk0 msg0 r0 : pke_domain r0 =>
 hoare[ACWC2RoundTrip(ACWC2FullG).run:
 pk=pk0 /\ sk=sk0 /\ msg=msg0 /\ r=r0 /\ ACWC2FullG.table=g0 ==>
 res=acwc2_failure g0 pk0 sk0 msg0 r0 /\ ACWC2FullG.table=g0].
proof.
 move=>hr; apply(acwc2_roundtrip_functional ACWC2FullG g0 (fun st=>st=g0) pk0 sk0 msg0 r0 _ hr).
 move=>x hx; exact(acwc2_full_g_functional g0 x).
qed.

lemma acwc2_secret_bytes_key w : acwc2_secret_bytes w.`kg_sk=pke_secret_bytes w.
proof. by rewrite /acwc2_secret_bytes /pke_secret_bytes. qed.
lemma acwc2_honest_enc g w msg r : pke_key_relation w =>
 acwc2_enc_spec g w.`kg_pk msg r=Some(pke_ciphertext w.`kg_pk (acwc2_code g msg r) r).
proof.
 move=>hk; rewrite /acwc2_enc_spec; exact(pke_enc_accept _ _ _ (pke_key_canonical w hk)).
qed.
lemma acwc2_recovery_from_base g w msg r : pke_key_relation w => pke_domain r =>
 pke_dec_spec (pke_ciphertext w.`kg_pk (acwc2_code g msg r) r) (pke_secret_bytes w)=Some(acwc2_code g msg r) =>
 acwc2_dec_spec g w.`kg_pk w.`kg_sk (pke_ciphertext w.`kg_pk (acwc2_code g msg r) r)=Some msg.
proof.
 move=>hk hr hb.
 have hm:=acwc2_code_domain g msg r.
 have hR:=rrec_keyed_forward w (acwc2_code g msg r) r hk hm hr.
 rewrite /acwc2_dec_spec acwc2_secret_bytes_key hb /= hR /=.
 rewrite /acwc2_code; exact(sotp_encode_decode_option msg (g r)).
qed.
lemma acwc2_failure_inclusion g w msg r : pke_key_relation w => pke_domain r =>
 acwc2_failure g w.`kg_pk w.`kg_sk msg r => acwc2_transformed_base_failure g w.`kg_pk w.`kg_sk msg r.
proof.
 move=>hk hr.
 have he:=acwc2_honest_enc g w msg r hk.
 rewrite /acwc2_failure /acwc2_transformed_base_failure he /= acwc2_secret_bytes_key.
 have h:=acwc2_recovery_from_base g w msg r hk hr; smt().
qed.

(* A single cached G value suffices on the honest-recovery path. The
   invariant below concerns that value, not a full presampled oracle. *)
lemma acwc2_dec_recovery (G<:ACWC2GPort) (I:(glob G)->bool) w msg0 r0 pad0 :
 pke_key_relation w => pke_domain r0 =>
 hoare[G.run:r=r0 /\ I(glob G) ==>res=pad0 /\ I(glob G)] =>
 pke_dec_spec (pke_ciphertext w.`kg_pk (poly_sotp_encode_spec msg0 pad0) r0) (pke_secret_bytes w)
   =Some(poly_sotp_encode_spec msg0 pad0) =>
 hoare[ACWC2Dec(G).run:
 pk=w.`kg_pk /\ sk=w.`kg_sk /\ ct=pke_ciphertext w.`kg_pk (poly_sotp_encode_spec msg0 pad0) r0 /\ I(glob G) ==>
 res=Some msg0 /\ I(glob G)].
proof.
 move=>hk hr hG hb.
 have hm:pke_domain(poly_sotp_encode_spec msg0 pad0).
 + have h:=acwc2_code_domain (fun _=>pad0) msg0 r0; by move:h; rewrite /acwc2_code.
 have hR:=rrec_keyed_forward w (poly_sotp_encode_spec msg0 pad0) r0 hk hm hr.
 proc; rcondt 3.
 + wp; call(pke_dec_functional (pke_ciphertext w.`kg_pk (poly_sotp_encode_spec msg0 pad0) r0)
     (pke_secret_bytes w)); auto=> />; by rewrite acwc2_secret_bytes_key hb.
 rcondt 4.
 + call(rrec_functional w.`kg_pk (poly_sotp_encode_spec msg0 pad0)
     (pke_ciphertext w.`kg_pk (poly_sotp_encode_spec msg0 pad0) r0)).
   wp; call(pke_dec_functional (pke_ciphertext w.`kg_pk (poly_sotp_encode_spec msg0 pad0) r0)
     (pke_secret_bytes w)); auto=> />; by rewrite acwc2_secret_bytes_key hb hR.
 call(sotp_decode_functional (poly_sotp_encode_spec msg0 pad0) pad0); call hG.
 call(rrec_functional w.`kg_pk (poly_sotp_encode_spec msg0 pad0)
   (pke_ciphertext w.`kg_pk (poly_sotp_encode_spec msg0 pad0) r0)).
 wp; call(pke_dec_functional (pke_ciphertext w.`kg_pk (poly_sotp_encode_spec msg0 pad0) r0)
   (pke_secret_bytes w)).
 auto=> />; by rewrite acwc2_secret_bytes_key hb hR sotp_encode_decode_option.
qed.

lemma acwc2_rom_enc_value pk0 msg0 r0 gm0 : pke_domain r0 =>
 hoare[ACWC2ROMEnc.run:pk=pk0 /\ msg=msg0 /\ r=r0 /\ ROG.m=gm0 ==>
 ROG.m.[rr_G_input r0]<>None /\
 res=pke_enc_spec pk0 (poly_sotp_encode_spec msg0 (oget ROG.m.[rr_G_input r0])) r0 /\
 cache_extends gm0 ROG.m].
proof.
 move=>hr; proc.
 seq 1 : (pk=pk0 /\ msg=msg0 /\ r=r0 /\
 ROG.m.[rr_G_input r0]=Some pad /\ cache_extends gm0 ROG.m).
 + call(acwc2_hash_g_value r0 gm0); auto.
 exists* pad; elim*=>pad0.
 have hm:pke_domain(poly_sotp_encode_spec msg0 pad0).
 + have h:=acwc2_code_domain (fun _=>pad0) msg0 r0; by move:h; rewrite /acwc2_code.
 call(pke_enc_functional pk0 (poly_sotp_encode_spec msg0 pad0) r0 hm hr).
 call(sotp_encode_functional msg0 pad0); auto=> /> &mr hcache hext.
 by rewrite hcache.
qed.
lemma acwc2_rom_dec_recovery w msg0 r0 pad0 gm0 :
 pke_key_relation w => pke_domain r0 => gm0.[rr_G_input r0]=Some pad0 =>
 pke_dec_spec (pke_ciphertext w.`kg_pk (poly_sotp_encode_spec msg0 pad0) r0) (pke_secret_bytes w)
   =Some(poly_sotp_encode_spec msg0 pad0) =>
 hoare[ACWC2ROMDec.run:
 pk=w.`kg_pk /\ sk=w.`kg_sk /\ ct=pke_ciphertext w.`kg_pk (poly_sotp_encode_spec msg0 pad0) r0 /\ ROG.m=gm0 ==>
 res=Some msg0 /\ ROG.m=gm0].
proof.
 move=>hk hr hcache hb.
 apply(acwc2_dec_recovery ACWC2HashG (fun st=>st=gm0) w msg0 r0 pad0 hk hr _ hb).
 conseq(acwc2_hash_g_cached r0 gm0 pad0)=> />; smt().
qed.
lemma acwc2_rom_dec_recovery_correct w msg0 r0 pad0 gm0 :
 pke_key_relation w => pke_domain r0 => gm0.[rr_G_input r0]=Some pad0 =>
 pke_dec_spec (pke_ciphertext w.`kg_pk (poly_sotp_encode_spec msg0 pad0) r0) (pke_secret_bytes w)
   =Some(poly_sotp_encode_spec msg0 pad0) =>
 phoare[ACWC2ROMDec.run:
 pk=w.`kg_pk /\ sk=w.`kg_sk /\ ct=pke_ciphertext w.`kg_pk (poly_sotp_encode_spec msg0 pad0) r0 /\ ROG.m=gm0 ==>
 res=Some msg0 /\ ROG.m=gm0]=1%r.
proof.
 move=>hk hr hcache hb.
 by conseq(acwc2_dec_lossless ACWC2HashG acwc2_hash_g_lossless)
   (acwc2_rom_dec_recovery w msg0 r0 pad0 gm0 hk hr hcache hb).
qed.

require import NTRUPlus768ACWC2BaseModel.
lemma acwc2_transformed_base_pad g w msg r :
 acwc2_transformed_base_failure g w.`kg_pk w.`kg_sk msg r=acwc2_pad_bad w msg r (g r).
proof.
 by rewrite /acwc2_pad_bad /acwc2_base_failure
   /acwc2_transformed_base_failure /acwc2_enc_spec /acwc2_code acwc2_secret_bytes_key.
qed.
lemma acwc2_failure_pad_inclusion g w msg r : pke_key_relation w => pke_domain r =>
 acwc2_failure g w.`kg_pk w.`kg_sk msg r => acwc2_pad_bad w msg r (g r).
proof.
 move=>hk hr; rewrite -acwc2_transformed_base_pad.
 exact(acwc2_failure_inclusion g w msg r hk hr).
qed.

lemma acwc2_roundtrip_correct (G<:ACWC2GPort) (g:acwc2_g_map) (I:(glob G)->bool) pk0 sk0 msg0 r0 :
 (forall x,pke_domain x => hoare[G.run:r=x /\ I(glob G) ==>res=g x /\ I(glob G)]) =>
 islossless G.run => pke_domain r0 =>
 phoare[ACWC2RoundTrip(G).run:pk=pk0 /\ sk=sk0 /\ msg=msg0 /\ r=r0 /\ I(glob G) ==>
 res=acwc2_failure g pk0 sk0 msg0 r0 /\ I(glob G)]=1%r.
proof.
 move=>hG hLL hr.
 by conseq(acwc2_roundtrip_lossless G hLL)(acwc2_roundtrip_functional G g I pk0 sk0 msg0 r0 hG hr).
qed.
lemma acwc2_full_roundtrip_correct g0 pk0 sk0 msg0 r0 : pke_domain r0 =>
 phoare[ACWC2RoundTrip(ACWC2FullG).run:
 pk=pk0 /\ sk=sk0 /\ msg=msg0 /\ r=r0 /\ ACWC2FullG.table=g0 ==>
 res=acwc2_failure g0 pk0 sk0 msg0 r0 /\ ACWC2FullG.table=g0]=1%r.
proof.
 move=>hr; by conseq(acwc2_roundtrip_lossless ACWC2FullG acwc2_full_g_lossless)
  (acwc2_full_roundtrip_functional g0 pk0 sk0 msg0 r0 hr).
qed.
