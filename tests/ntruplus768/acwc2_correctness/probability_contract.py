"""Finite G independence, biased CBD weights, conditional centering and maximum order."""
BASE='ntruplus/proof/768/ref/acwc2_correctness/'
DOMAINS=BASE+'NTRUPlus768ACWC2Domains.ec'
ORACLE=BASE+'NTRUPlus768ACWC2Oracle.ec'
COLLISION=BASE+'NTRUPlus768ACWC2Collision.ec'
MOMENT=BASE+'NTRUPlus768ACWC2Moment.ec'
CONCENTRATION=BASE+'NTRUPlus768ACWC2Concentration.ec'
RECOVERY=BASE+'NTRUPlus768ACWC2Recovery.ec'
RULES=(
 (DOMAINS,'G is indexed by distinct randomness values not their buffer preimages',r'op acwc2_r_enum : pke_poly list = to_seq(support pke_psi1).'),
 (DOMAINS,'randomness weights are actual CBD point masses',r'op acwc2_r_weight (r:pke_poly) = mu1 pke_psi1 r.'),
 (DOMAINS,'message maximum covers all 96-byte messages',r'op acwc2_message_enum : W8.t Array96.t list = to_seq(support uniform96).'),
 (DOMAINS,'message enumeration retains its full bit cardinality',r'lemma acwc2_message_cardinality : size acwc2_message_enum=2^768.'),
 (ORACLE,'finite G draws independent pads for the unique randomness enumeration',r'op acwc2_gpads_law = dlist uniform192 (size acwc2_r_enum).'),
 (ORACLE,'one randomness value always selects the same G coordinate',r'op acwc2_gfun (pads:W8.t Array192.t list) : acwc2_g_function = fun r=>nth witness pads (index r acwc2_r_enum).'),
 (ORACLE,'factorized observation reads one G entry per summand',r'''op acwc2_g_observe ['a] (f:pke_poly -> W8.t Array192.t -> 'a) (g:acwc2_g_function) = map (fun r=>f r (g r)) acwc2_r_enum.'''),
 (ORACLE,'cache completion preserves old entries in the right-biased join',r'proc prepare(pads:W8.t Array192.t list) = { ROG.m<-acwc2_g_cache pads+ROG.m; }'),
 (ORACLE,'independent G experiment resets once before drawing and installing its table',r'proc init() : acwc2_g_function = { var pads:W8.t Array192.t list; ROG.init(); pads<$acwc2_gpads_law; prepare(pads); return acwc2_gfun pads; }'),
 (ORACLE,'independent sampled cache matching requires an initially empty table',r'lemma acwc2_prepare_empty pads0 : hoare[ACWC2EagerOracle.prepare : ROG.m=empty /\ pads=pads0 ==> acwc2_cache_matches(acwc2_gfun pads0)ROG.m].'),
 (COLLISION,'exact collision is the squared actual randomness weights',r'lemma acwc2_r_weight_collision : BRA.big predT (fun r=>acwc2_r_weight r^2) acwc2_r_enum=(3%r/8%r)^768.'),
 (MOMENT,'moment variables are normalized, centered and bounded separately',r'op acwc2_centered_bounded (d:real distr) (w:real) = is_finite(support d) /\ is_lossless d /\ E d idfun=0%r /\ (forall x,x \in d=>`|x|<=w) /\ 0%r<=w.'),
 (MOMENT,'moment expectation uses a product of component laws',r'op acwc2_moment (ds:real distr list) n = E(djoin ds)(fun xs=>(acwc2_sum xs)^n).'),
 (CONCENTRATION,'finite maximum really maximizes every message value',r'''op acwc2_finite_max ['m] (ms:'m list) (f:'m->real) = foldr (fun m v=>maxr (f m) v) 0%r ms.'''),
 (CONCENTRATION,'Markov requires a positive threshold and an eighth moment',r'''lemma acwc2_eighth_markov ['a] (d:'a distr) (f:'a->real) eps : is_finite(support d) =>0%r<eps => mu d(fun x=>eps<=f x)<=E d(fun x=>(f x)^8)/(eps^8).'''),
 (CONCENTRATION,'oracle expectation remains outside the message maximum',r'''lemma acwc2_finite_max_concentration ['m 'a] (d:'a distr) (ms:'m list) (f:'m->'a->real) c eps K : is_finite(support d) =>is_lossless d =>0%r<=c =>0%r<eps =>0%r<=K => (forall m x,m \in ms=>x \in d=>0%r<=f m x<=1%r) => (forall m,m \in ms=>E d(fun x=>(f m x-c)^8)<=K) => E d(fun x=>acwc2_finite_max ms(fun m=>f m x))<= c+eps+(size ms)%r*K/(eps^8).'''),
 (RECOVERY,'actual failure is only bounded by the single-entry base envelope',r'lemma acwc2_failure_pad_inclusion g w msg r : pke_key_relation w => pke_domain r => acwc2_failure g w.`kg_pk w.`kg_sk msg r => acwc2_pad_bad w msg r (g r).'),
)
MUTATIONS=(
 ('CBD-randomness-weights-falsely-uniform',DOMAINS,'mu1 pke_psi1 r.','1%r/(3%r^768).'),
 ('G-coordinate-enumeration-duplicates-randomness-values',DOMAINS,'to_seq(support pke_psi1).','to_seq(support pke_psi1) ++ to_seq(support pke_psi1).'),
 ('G-table-reuses-one-pad-for-all-distinct-inputs',ORACLE,'dlist uniform192 (size acwc2_r_enum).','dmap uniform192 (fun pad=>nseq (size acwc2_r_enum) pad).'),
 ('G-lookup-ignores-randomness-index',ORACLE,'nth witness pads (index r acwc2_r_enum)','nth witness pads 0'),
 ('G-prepare-overwrites-prior-cache-entries',ORACLE,'ROG.m<-acwc2_g_cache pads+ROG.m;','ROG.m<-ROG.m+acwc2_g_cache pads;'),
 ('G-prepare-erases-cache-on-every-completion',ORACLE,'ROG.m<-acwc2_g_cache pads+ROG.m;','ROG.init(); ROG.m<-acwc2_g_cache pads;'),
 ('G-init-fresh-law-retains-a-stale-table',ORACLE,'ROG.init(); pads<$acwc2_gpads_law;','pads<$acwc2_gpads_law;'),
 ('G-table-matching-forgets-empty-table-premise',ORACLE,r'ROG.m=empty /\ pads=pads0 ==> acwc2_cache_matches',r'pads=pads0 ==> acwc2_cache_matches'),
 ('moment-centering-premise-removed',MOMENT,r'is_lossless d /\ E d idfun=0%r /\ ',r'is_lossless d /\ '),
 ('moment-weight-bound-discarded',MOMENT,r'(forall x,x \in d=>`|x|<=w)',r'(forall x,x \in d=>`|x|<=1%r)'),
 ('moment-product-law-replaced-with-correlated-sum',MOMENT,'E(djoin ds)(fun xs=>(acwc2_sum xs)^n)','E(correlated_join ds)(fun xs=>(acwc2_sum xs)^n)'),
 ('worst-message-maximum-replaced-with-minimum',CONCENTRATION,'maxr (f m) v','minr (f m) v'),
 ('maximum-moved-outside-G-expectation',CONCENTRATION,'E d(fun x=>acwc2_finite_max ms(fun m=>f m x))<=','acwc2_finite_max ms(fun m=>E d(fun x=>f m x))<='),
 ('message-union-factor-omitted',CONCENTRATION,'c+eps+(size ms)%r*K/(eps^8).','c+eps+K/(eps^8).'),
 ('transformed-failure-wrongly-identified-with-base-envelope',RECOVERY,'acwc2_failure g w.`kg_pk w.`kg_sk msg r => acwc2_pad_bad','acwc2_failure g w.`kg_pk w.`kg_sk msg r <=> acwc2_pad_bad'),
)

RULES+=(
 (MOMENT,'eighth moment is proved from per-component conditions with constant 105',r'''lemma acwc2_independent_eighth ['i] (rs:'i list) (w:'i->real) (d:'i->real distr) : (forall i,i \in rs=>acwc2_centered_bounded(d i)(w i)) => E(djoin(map d rs))(fun xs=>(acwc2_sum xs)^8)<= 105%r*(Bigreal.BRA.big predT(fun i=>(w i)^2)rs)^4.'''),
 (CONCENTRATION,'outer key expectation retains its own conditional mean and inner message maximum',r'''lemma acwc2_expected_max_concentration ['k 'm 'a] (dk:'k distr) (g:'k->'a distr) (ms:'m list) (f:'k->'m->'a->real) (c:'k->real) eps K : is_finite(support dk) =>is_lossless dk =>0%r<eps =>0%r<=K => (forall k,k \in dk=>is_finite(support(g k)) /\ is_lossless(g k) /\ 0%r<=c k) => (forall k m x,k \in dk=>m \in ms=>x \in g k=>0%r<=f k m x<=1%r) => (forall k m,k \in dk=>m \in ms=>E(g k)(fun x=>(f k m x-c k)^8)<=K) => E dk(fun k=>E(g k)(fun x=>acwc2_finite_max ms(fun m=>f k m x)))<= E dk c+eps+(size ms)%r*K/(eps^8).'''),
)
MUTATIONS+=(
 ('eighth-moment-conclusion-smuggled-in-as-a-premise',MOMENT,r'(forall i,i \in rs=>acwc2_centered_bounded(d i)(w i)) => E(djoin(map d rs))',r'(forall i,i \in rs=>acwc2_centered_bounded(d i)(w i)) => acwc2_moment(map d rs)8=0%r => E(djoin(map d rs))'),
 ('key-expectation-moved-inside-message-maximum',CONCENTRATION,'E dk(fun k=>E(g k)(fun x=>acwc2_finite_max ms(fun m=>f k m x)))<=','acwc2_finite_max ms(fun m=>E dk(fun k=>E(g k)(fun x=>f k m x)))<='),
 ('conditional-key-centering-replaced-by-global-average',CONCENTRATION,'E(g k)(fun x=>(f k m x-c k)^8)<=K','E(g k)(fun x=>(f k m x-E dk c)^8)<=K'),
)

RULES+=((ORACLE,'prepared shared G gives the actual roundtrip event and unchanged cache',r'lemma acwc2_prepared_roundtrip_correct g gm0 pk0 sk0 msg0 r0 : pke_domain r0 => acwc2_cache_matches g gm0 => phoare[ACWC2RoundTrip(ACWC2HashG).run: pk=pk0 /\ sk=sk0 /\ msg=msg0 /\ r=r0 /\ ROG.m=gm0 ==> res=acwc2_failure g pk0 sk0 msg0 r0 /\ ROG.m=gm0]=1%r.'),)
MUTATIONS+=(('actual-prepared-roundtrip-assumes-no-cache-agreement',ORACLE,'pke_domain r0 => acwc2_cache_matches g gm0 => phoare[ACWC2RoundTrip(ACWC2HashG).run:','pke_domain r0 => phoare[ACWC2RoundTrip(ACWC2HashG).run:'),)

MUTATIONS+=(('failure-envelope-weakened-with-a-no-wrap-premise',RECOVERY,'lemma acwc2_failure_pad_inclusion g w msg r : pke_key_relation w => pke_domain r =>','lemma acwc2_failure_pad_inclusion g w msg r : pke_key_relation w => pke_domain r => sampled_m1_no_wrap w.`kg_fbuf w.`kg_gbuf r (acwc2_code g msg r) =>'),)
