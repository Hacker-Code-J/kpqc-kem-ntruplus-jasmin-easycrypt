require import AllCore List Distr DList FMap Finite.
from Jasmin require import JWord.
require import Array192 Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768RRecCodec NTRUPlus768ACWC2HashG.
require import NTRUPlus768ACWC2Domains NTRUPlus768NoiseIndependentBlocks.

type acwc2_g_function = pke_poly -> W8.t Array192.t.
op [opaque] acwc2_gpads_law = dlist uniform192 (size acwc2_r_enum).
op [opaque] acwc2_gfun (pads:W8.t Array192.t list) : acwc2_g_function =
 fun r=>nth witness pads (index r acwc2_r_enum).
op [opaque] acwc2_eager_g_law = dmap acwc2_gpads_law acwc2_gfun.
op acwc2_g_observe ['a] (f:pke_poly -> W8.t Array192.t -> 'a) (g:acwc2_g_function) =
 map (fun r=>f r (g r)) acwc2_r_enum.
op [opaque] acwc2_g_cache (pads:W8.t Array192.t list) =
 ofassoc(map (fun r=>(rr_G_input r,acwc2_gfun pads r)) acwc2_r_enum).
op acwc2_cache_matches (g:acwc2_g_function)
 (gm:(W8.t Array1152.t,W8.t Array192.t) fmap) =
 forall r,pke_domain r=>gm.[rr_G_input r]=Some(g r).

lemma acwc2_uniform192_finite : is_finite(support uniform192).
proof.
 rewrite /uniform192; apply acwc2_dmap_finite.
 apply acwc2_dlist_finite=> //; rewrite /W8.dword; exact(finite_duniform _).
qed.
lemma acwc2_gpads_lossless : is_lossless acwc2_gpads_law.
proof. rewrite /acwc2_gpads_law; apply/dlist_ll; exact uniform192_ll. qed.
lemma acwc2_gpads_finite : is_finite(support acwc2_gpads_law).
proof. rewrite /acwc2_gpads_law; apply acwc2_dlist_finite; [exact size_ge0|exact acwc2_uniform192_finite]. qed.
lemma acwc2_eager_g_lossless : is_lossless acwc2_eager_g_law.
proof. rewrite /acwc2_eager_g_law; apply/dmap_ll; exact acwc2_gpads_lossless. qed.
lemma acwc2_eager_g_finite : is_finite(support acwc2_eager_g_law).
proof. rewrite /acwc2_eager_g_law; apply acwc2_dmap_finite; exact acwc2_gpads_finite. qed.
lemma acwc2_g_index r : pke_domain r => 0<=index r acwc2_r_enum<size acwc2_r_enum.
proof. rewrite -acwc2_r_enum_domain; smt(index_ge0 index_mem). qed.

lemma acwc2_dlist_nth ['a] (d:'a distr) (x0:'a) n i :
 is_lossless d => 0<=i<n =>
 dmap (dlist d n) (fun xs=>nth x0 xs i)=d.
proof.
 move=>hd hi.
 have h:=dmap_dlist_partial_perm x0 d (fun _=>i) n 1 _ _ hd _ _;
   first 4 smt().
 have hh:=congr1 (fun (D:'a list distr)=>dmap D (head x0)) _ _ h.
 move:hh; rewrite /= dlist1 !dmap_comp /(\o) /= ?dmap_id=>hh.
 have he:dmap (dlist d n) (fun xs=>nth x0 xs i)=
   dmap (dlist d n) (fun xs=>head x0 (mkseq (fun _=>nth x0 xs i) 1)).
 + apply eq_dmap=>xs; by rewrite mkseq1.
 by rewrite he hh.
qed.
lemma acwc2_g_marginal r : pke_domain r =>
 dmap acwc2_eager_g_law (fun g=>g r)=uniform192.
proof.
 move=>hr; rewrite /acwc2_eager_g_law
   (dmap_comp acwc2_gfun (fun g=>g r) acwc2_gpads_law) /acwc2_gpads_law /acwc2_gfun /(\o).
 exact(acwc2_dlist_nth uniform192 witness _ _ uniform192_ll (acwc2_g_index r hr)).
qed.

lemma acwc2_g_observe_pads ['a] (f:pke_poly -> W8.t Array192.t -> 'a) pads :
 size pads=size acwc2_r_enum =>
 acwc2_g_observe f (acwc2_gfun pads)=
 mapi (fun i=>f (nth witness acwc2_r_enum i)) pads.
proof.
 move=>hs; apply(eq_from_nth witness).
 + by rewrite /acwc2_g_observe size_map size_mapi hs.
 move=>i hi; rewrite /acwc2_g_observe size_map in hi.
 rewrite /acwc2_g_observe (nth_map witness) 1:hi /= /acwc2_gfun.
 rewrite(index_uniq witness i acwc2_r_enum hi acwc2_r_enum_uniq).
 by rewrite (nth_mapi witness pads witness) 1:/#.
qed.
lemma acwc2_g_independent_observations ['a] (f:pke_poly -> W8.t Array192.t -> 'a) :
 dmap acwc2_eager_g_law (acwc2_g_observe f)=
 djoin(map (fun r=>dmap uniform192 (f r)) acwc2_r_enum).
proof.
 rewrite /acwc2_eager_g_law (dmap_comp acwc2_gfun (acwc2_g_observe f) acwc2_gpads_law).
 have he:dmap acwc2_gpads_law (acwc2_g_observe f \o acwc2_gfun)=
   dmap acwc2_gpads_law (mapi (fun i=>f(nth witness acwc2_r_enum i))).
 + apply eq_dmap_in=>pads hp; apply acwc2_g_observe_pads.
   rewrite /acwc2_gpads_law in hp.
   exact(supp_dlist_size uniform192 (size acwc2_r_enum) pads (size_ge0 _) hp).
 rewrite he /acwc2_gpads_law independent_blocks_mapi 1:size_ge0.
 have hm:map (fun i=>dmap uniform192(f(nth witness acwc2_r_enum i))) (range 0 (size acwc2_r_enum))=
   map (fun r=>dmap uniform192(f r)) acwc2_r_enum.
 + have hh:=congr1 (List.map (fun r=>dmap uniform192(f r))) _ _ (map_nth_range witness acwc2_r_enum).
   by move:hh; rewrite -map_comp /(\o).
 by rewrite /= hm.
qed.

lemma acwc2_assoc_graph ['a 'k 'v] (key:'a->'k) (value:'a->'v) rs r :
 (forall x y,x \in rs=>y \in rs=>key x=key y=>x=y) => r \in rs =>
 assoc(map (fun x=>(key x,value x)) rs)(key r)=Some(value r).
proof.
 elim:rs=>[|x xs ih] //= hi hr; rewrite assoc_cons.
 case(key r=key x)=>he.
 + have hx:r=x by apply hi; smt().
   by rewrite hx.
 apply ih; smt().
qed.
lemma acwc2_g_cache_lookup pads r : pke_domain r =>
 (acwc2_g_cache pads).[rr_G_input r]=Some(acwc2_gfun pads r).
proof.
 move=>hr; rewrite /acwc2_g_cache ofassoc_get.
 apply acwc2_assoc_graph.
 + move=>x y hx hy he; apply(rr_G_input_injective x y) => //;
   by rewrite -acwc2_r_enum_domain.
 by rewrite acwc2_r_enum_domain.
qed.
lemma acwc2_g_cache_matches pads : acwc2_cache_matches (acwc2_gfun pads) (acwc2_g_cache pads).
proof. exact(acwc2_g_cache_lookup pads). qed.
lemma acwc2_keep_old ['a 'b] (fresh old:('a,'b) fmap) : cache_extends old (fresh+old).
proof.
 move=>x y hx; rewrite joinE.
 have hm:x \in old by rewrite domE hx.
 by rewrite hm.
qed.
lemma acwc2_prepare_matches pads :
 acwc2_cache_matches (acwc2_gfun pads) (acwc2_g_cache pads+empty).
proof. move=>r hr; rewrite joinE mem_empty /=; exact(acwc2_g_cache_lookup pads r hr). qed.

(* Completion preserves all existing entries. Only the fresh experiment
   initializer resets G; no continuation or adversary gets that capability.
   All finite enumerations remain symbolic. *)
module ACWC2EagerOracle = {
 proc prepare(pads:W8.t Array192.t list) = {
  ROG.m<-acwc2_g_cache pads+ROG.m;
 }
 proc init() : acwc2_g_function = {
  var pads:W8.t Array192.t list;
  ROG.init();
  pads<$acwc2_gpads_law;
  prepare(pads);
  return acwc2_gfun pads;
 }
}.
lemma acwc2_prepare_lossless : islossless ACWC2EagerOracle.prepare.
proof. by proc; auto. qed.
lemma acwc2_prepare_preserves gm0 : hoare[ACWC2EagerOracle.prepare :
 ROG.m=gm0 ==> cache_extends gm0 ROG.m].
proof. proc; auto=> /> &hr; exact(acwc2_keep_old _ gm0). qed.
lemma acwc2_prepare_empty pads0 : hoare[ACWC2EagerOracle.prepare :
 ROG.m=empty /\ pads=pads0 ==> acwc2_cache_matches(acwc2_gfun pads0)ROG.m].
proof. proc; auto=> />; exact(acwc2_prepare_matches pads0). qed.
lemma acwc2_eager_init_lossless : islossless ACWC2EagerOracle.init.
proof. proc; call acwc2_prepare_lossless; rnd; call rog_init_ll; auto=> />; exact acwc2_gpads_lossless. qed.
lemma acwc2_eager_init_matches : hoare[ACWC2EagerOracle.init : true ==>
 acwc2_cache_matches res ROG.m].
proof. proc; ecall(acwc2_prepare_empty pads); rnd; call rog_init_empty; auto. qed.
lemma acwc2_eager_init_law &m (event:acwc2_g_function->bool) :
 Pr[ACWC2EagerOracle.init() @ &m:event res]=mu acwc2_eager_g_law event.
proof.
 rewrite /acwc2_eager_g_law dmapE.
 byphoare (_:true ==>event res)=> //.
 proc; inline ACWC2EagerOracle.prepare ROG.init; wp; rnd; auto.
qed.
lemma acwc2_prepared_hash_g r0 g gm0 : pke_domain r0 => acwc2_cache_matches g gm0 =>
 hoare[ACWC2HashG.run : r=r0 /\ ROG.m=gm0 ==> res=g r0 /\ ROG.m=gm0].
proof.
 move=>hr hg; have hc:=hg r0 hr.
 conseq(acwc2_hash_g_cached r0 gm0 (g r0))=> />; smt().
qed.

require import NTRUPlus768ACWC2Model NTRUPlus768ACWC2Procedures NTRUPlus768ACWC2Recovery.
(* Both actual kernel callers use the same prepared table. This theorem
   concerns their result and unchanged table, not equality of a full eager
   table with an initially empty lazy table. *)
lemma acwc2_prepared_roundtrip_correct g gm0 pk0 sk0 msg0 r0 :
 pke_domain r0 => acwc2_cache_matches g gm0 =>
 phoare[ACWC2RoundTrip(ACWC2HashG).run:
 pk=pk0 /\ sk=sk0 /\ msg=msg0 /\ r=r0 /\ ROG.m=gm0 ==>
 res=acwc2_failure g pk0 sk0 msg0 r0 /\ ROG.m=gm0]=1%r.
proof.
 move=>hr hg.
 have hG:forall x,pke_domain x =>
   hoare[ACWC2HashG.run:r=x /\ ROG.m=gm0 ==>res=g x /\ ROG.m=gm0].
 + move=>x hx; exact(acwc2_prepared_hash_g x g gm0 hx hg).
 exact(acwc2_roundtrip_correct ACWC2HashG g (fun gm=>gm=gm0)
   pk0 sk0 msg0 r0 hG acwc2_hash_g_lossless hr).
qed.
