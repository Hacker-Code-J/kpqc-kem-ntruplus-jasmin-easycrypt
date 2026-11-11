require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array224 Array1152.
require import NTRUPlus768HistModel NTRUPlus768HistLookup.
require import NTRUPlus768FOModel NTRUPlus768FOChallenge.
require import NTRUPlus768SimModel NTRUPlus768SimLookup.
require import NTRUPlus768SimCandidate NTRUPlus768SimKnownAlgebra.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel.
require import NTRUPlus768DecapCompleteSpec.
require import NTRUPlus768ACWC2Oracle NTRUPlus768FOEagerG.
require import NTRUPlus768KEMPayloadSpec NTRUPlus768ROMOracles.

(* This is the existing base-decryption failure event on actual H entries.
   It is not an assumed uniqueness condition on the order of the list. *)
op [opaque] hist_bad_entries (w:keygen_witness) (g:acwc2_g_function)
 (ex:fo_h_input option) (xs:hist_table) =
 has(fun e:hist_entry=>Some e.`1<>ex /\ fo_base_bad w g e.`1.`1 e.`2)xs.

lemma hist_order_rep_entry xs log input hout : hist_rep xs log=>
 ((input,hout) \in xs <=> log.[input]=Some hout).
proof.
 exact(hist_rep_entry input hout xs log).
qed.

lemma hist_bad_entries_good w g ex xs log : hist_rep xs log=>
 (!hist_bad_entries w g ex xs <=> fo_hcache_good w g ex log).
proof.
 move=>hr;rewrite /hist_bad_entries List.hasPn /fo_hcache_good.
 split.
 + move=>hn input hout hh hx.
   have hm:(input,hout) \in xs by rewrite(hist_order_rep_entry xs log input hout hr).
   have hb:=hn (input,hout) hm;by smt().
 move=>hg [input hout] hm /=.
 have hh:log.[input]=Some hout by move:hm;rewrite(hist_order_rep_entry xs log input hout hr).
 by smt().
qed.

lemma hist_lookup_none_iff pk suffix g xs log ct : hist_rep xs log=>
 (hist_lookup_result pk suffix g xs ct=None <=>
  sim_lookup_result pk suffix g log ct=None).
proof.
 move=>hr;rewrite hist_lookup_result_none sim_lookup_result_none.
 split.
 + move=>hn input hd.
   have hh:log.[input]=Some(oget log.[input]) by apply some_oget.
   have hm:(input,oget log.[input]) \in xs
    by rewrite(hist_order_rep_entry xs log input (oget log.[input]) hr).
   have hb:=hn (input,oget log.[input]) hm.
   by move:hb;rewrite /hist_lookup_matches /sim_entry_matches.
 move=>hn [input hout] hm /=.
 have hh:log.[input]=Some hout by move:hm;rewrite(hist_order_rep_entry xs log input hout hr).
 have hd:input \in log by rewrite domE hh.
 have hb:=hn input hd.
 by move:hb;rewrite /sim_entry_matches hh /= /hist_lookup_matches.
qed.

(* Order independence follows from correctness of the matching entries.
   The proof uses the actual re-encryption and the shared H map. *)
lemma hist_lookup_result_order w g xs log ct :
 pke_key_relation w=>hist_rep xs log=>sim_matching_good w g log ct=>
 hist_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g xs ct=
 sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log ct.
proof.
 move=>hk hr hg.
 case(sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log ct=None)=>ho.
 + have hn:=hist_lookup_none_iff w.`kg_pk (complete_sk_suffix w.`kg_sk) g xs log ct hr.
   by smt().
 have hn:hist_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g xs ct<>None
  by have:=hist_lookup_none_iff w.`kg_pk (complete_sk_suffix w.`kg_sk) g xs log ct hr;smt().
 pose k1:=oget(hist_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g xs ct).
 pose k2:=oget(sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log ct).
 have h1:hist_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g xs ct=Some k1
  by apply some_oget.
 have h2:sim_lookup_result w.`kg_pk (complete_sk_suffix w.`kg_sk) g log ct=Some k2
  by apply some_oget.
 have [[x1 y1] [hm [hmatch hv1]]]:=hist_lookup_result_found
  w.`kg_pk (complete_sk_suffix w.`kg_sk) g xs ct k1 h1.
 have [x2 y2 [hh2 [hs2 [he2 hv2]]]]:=sim_lookup_result_found
  w.`kg_pk (complete_sk_suffix w.`kg_sk) g log ct k2 h2.
 have hh1:log.[x1]=Some y1 by move:hm;rewrite(hist_order_rep_entry xs log x1 y1 hr).
 rewrite /hist_lookup_matches /= in hmatch.
 have [hs1 he1]:=hmatch.
 rewrite sim_candidate_reencryption in he1.
 rewrite sim_candidate_reencryption in he2.
 move:hg;rewrite /sim_matching_good=>hg.
 have hb1:!fo_base_bad w g x1.`1 y1 by exact(hg x1 y1 hh1 hs1 he1).
 have hb2:!fo_base_bad w g x2.`1 y2 by exact(hg x2 y2 hh2 hs2 he2).
 have [_ [_ hv]]:=sim_good_entries_unique w g log x1 x2 y1 y2 ct
  hk hs1 hs2 hh1 hh2 hb1 hb2 he1 he2.
 by rewrite h1 h2;smt().
qed.

lemma hist_lookup_order_good w g xs log star ct :
 pke_key_relation w=>hist_rep xs log=>fo_hcache_good w g None log=>
 hist_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) star g xs ct=
 sim_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) star g log ct.
proof.
 move=>hk hr hg;rewrite /hist_lookup_spec /sim_lookup_spec.
 case(star=Some ct);first done.
 move=>_;apply(hist_lookup_result_order w g xs log ct hk hr).
 rewrite /sim_matching_good=>input hout hh hs he.
 have hx:Some input<>None by done.
 exact(hg input hout hh hx).
qed.

lemma hist_lookup_order_challenge w g xs log table ex hs cs ct :
 pke_key_relation w=>hist_rep xs log=>sim_log_included log table=>
 fo_hcache_good w g ex log=>fo_challenge_invariant w g ex hs cs table=>
 hist_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) (Some cs) g xs ct=
 sim_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) (Some cs) g log ct.
proof.
 move=>hk hr hi hg hc;rewrite /hist_lookup_spec /sim_lookup_spec.
 case(Some cs=Some ct)=>he;first done.
 have hn:ct<>cs by smt().
 apply(hist_lookup_result_order w g xs log ct hk hr).
 exact(sim_matching_challenge_good w g log table ex hs cs ct hi hg hc hn).
qed.

lemma hist_lookup_disagreement_good w g xs log star ct :
 pke_key_relation w=>hist_rep xs log=>
 hist_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) star g xs ct<>
 sim_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) star g log ct=>
 hist_bad_entries w g None xs.
proof.
 move=>hk hr hn;case(hist_bad_entries w g None xs)=>hb;first done.
 have hg:fo_hcache_good w g None log
  by have:=hist_bad_entries_good w g None xs log hr;smt().
 have he:=hist_lookup_order_good w g xs log star ct hk hr hg.
 by smt().
qed.

lemma hist_lookup_disagreement w g xs log table ex hs cs ct :
 pke_key_relation w=>hist_rep xs log=>sim_log_included log table=>
 fo_challenge_invariant w g ex hs cs table=>
 hist_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) (Some cs) g xs ct<>
 sim_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) (Some cs) g log ct=>
 hist_bad_entries w g ex xs.
proof.
 move=>hk hr hi hc hn;case(hist_bad_entries w g ex xs)=>hb;first done.
 have hg:fo_hcache_good w g ex log
  by have:=hist_bad_entries_good w g ex xs log hr;smt().
 have he:=hist_lookup_order_challenge w g xs log table ex hs cs ct hk hr hi hg hc.
 by smt().
qed.

lemma hist_lookup_original_correct w g xs0 log0 star0 ct0 gm0 :
 pke_key_relation w=>hist_rep xs0 log0=>fo_hcache_good w g None log0=>
 acwc2_cache_matches g gm0=>
 phoare[HistLookup(FOGActual).run:
 xs=xs0 /\ pk=w.`kg_pk /\ suffix=complete_sk_suffix w.`kg_sk /\
 cstar=star0 /\ ct=ct0 /\ ROG.m=gm0 ==>
 res.`1=sim_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) star0 g log0 ct0 /\
 ROG.m=gm0]=1%r.
proof.
 move=>hk hr hh hg.
 have he:=hist_lookup_order_good w g xs0 log0 star0 ct0 hk hr hh.
 conseq(hist_lookup_correct w.`kg_pk (complete_sk_suffix w.`kg_sk) star0 xs0 ct0 g gm0 hg);smt().
qed.

lemma hist_lookup_original_challenge_correct w g xs0 log0 table ex hs cs ct0 gm0 :
 pke_key_relation w=>hist_rep xs0 log0=>sim_log_included log0 table=>
 fo_hcache_good w g ex log0=>fo_challenge_invariant w g ex hs cs table=>
 acwc2_cache_matches g gm0=>
 phoare[HistLookup(FOGActual).run:
 xs=xs0 /\ pk=w.`kg_pk /\ suffix=complete_sk_suffix w.`kg_sk /\
 cstar=Some cs /\ ct=ct0 /\ ROG.m=gm0 ==>
 res.`1=sim_lookup_spec w.`kg_pk (complete_sk_suffix w.`kg_sk) (Some cs) g log0 ct0 /\
 ROG.m=gm0]=1%r.
proof.
 move=>hk hr hi hh hc hg.
 have he:=hist_lookup_order_challenge w g xs0 log0 table ex hs cs ct0 hk hr hi hh hc.
 conseq(hist_lookup_correct w.`kg_pk (complete_sk_suffix w.`kg_sk) (Some cs) xs0 ct0 g gm0 hg);smt().
qed.

(* This couples one actual call on each side. It preserves the prepared
   G map, not the sequence of G calls or a logged G-query history. *)
lemma hist_lookup_original_equiv w g xs0 log0 table ex hs cs ct0 gm0 n0 :
 pke_key_relation w=>hist_rep xs0 log0=>sim_log_included log0 table=>
 fo_hcache_good w g ex log0=>fo_challenge_invariant w g ex hs cs table=>
 acwc2_cache_matches g gm0=>
 equiv[SimLookup(FOGActual).decap ~ HistLookup(FOGActual).run:
 ct{1}=ct0 /\ SimPublic.pk{1}=w.`kg_pk /\
 SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\
 SimPublic.cstar{1}=Some cs /\ SimPublic.count{1}=n0 /\ SimHistory.h{1}=log0 /\
 xs{2}=xs0 /\ pk{2}=w.`kg_pk /\ suffix{2}=complete_sk_suffix w.`kg_sk /\
 cstar{2}=Some cs /\ ct{2}=ct0 /\ ROG.m{1}=gm0 /\ ROG.m{2}=gm0 ==>
 res{1}=res.`1{2} /\ ROG.m{1}=gm0 /\ ROG.m{2}=gm0 /\
 SimPublic.pk{1}=w.`kg_pk /\ SimPublic.suffix{1}=complete_sk_suffix w.`kg_sk /\
 SimPublic.cstar{1}=Some cs /\ SimPublic.count{1}=n0+1 /\ SimHistory.h{1}=log0].
proof.
 move=>hk hr hi hh hc hg;proc*.
 ecall{1}(sim_lookup_correct w.`kg_pk (complete_sk_suffix w.`kg_sk) (Some cs) log0 n0 ct0 g gm0 hg).
 ecall{2}(hist_lookup_original_challenge_correct w g xs0 log0 table ex hs cs ct0 gm0 hk hr hi hh hc hg).
 auto=> />;smt().
qed.
