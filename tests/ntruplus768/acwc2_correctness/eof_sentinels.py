"""Frozen complete semantic EOF declarations and isolated unfinished-proof inventory."""
SENTINELS = {
    'acwc2_correctness/NTRUPlus768ACWC2BaseModel.ec': r"""

lemma __acwc2_correctness_eof_0 w code r :
 acwc2_base_failure w code r =
 (pke_enc_spec w.`kg_pk code r=None \/
 pke_dec_spec(oget(pke_enc_spec w.`kg_pk code r))(pke_secret_bytes w)<>Some code).
proof. exact (acwc2_base_failureE w code r). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2Model.ec': r"""

lemma __acwc2_correctness_eof_4 g pk sk ct : pke_dec_spec ct (acwc2_secret_bytes sk)=None =>
 acwc2_dec_spec g pk sk ct=None.
proof. exact (acwc2_dec_reject_base g pk sk ct). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2Procedures.ec': r"""

lemma __acwc2_correctness_eof_5 (G<:ACWC2GPort) : islossless G.run => islossless ACWC2RoundTrip(G).run.
proof. exact (acwc2_roundtrip_lossless G). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2Recovery.ec': r"""

lemma __acwc2_correctness_eof_6 g0 pk0 sk0 msg0 r0 : pke_domain r0 =>
 phoare[ACWC2RoundTrip(ACWC2FullG).run:
 pk=pk0 /\ sk=sk0 /\ msg=msg0 /\ r=r0 /\ ACWC2FullG.table=g0 ==>
 res=acwc2_failure g0 pk0 sk0 msg0 r0 /\ ACWC2FullG.table=g0]=1%r.
proof. exact (acwc2_full_roundtrip_correct g0 pk0 sk0 msg0 r0). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2Domains.ec': r"""

lemma __acwc2_correctness_eof_2 : size acwc2_message_enum=2^768.
proof. exact (acwc2_message_cardinality). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2Collision.ec': r"""

lemma __acwc2_correctness_eof_3 :
 BRA.big predT (fun r=>acwc2_r_weight r^2) acwc2_r_enum=(3%r/8%r)^768.
proof. exact (acwc2_r_weight_collision). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2MomentConvex.ec': r"""

lemma __acwc2_correctness_eof_7 (d:real distr) (f:real->real) w s :
 is_finite(support d) => is_lossless d =>
 E d idfun=0%r => (forall x,x \in d=>`|x|<=w) =>
 0%r<=w => (forall a b,convex f a b) =>
 E d (fun x=>f(s+x)) <= (f(s+w)+f(s-w))/2%r.
proof. exact (acwc2_centered_chord d f w s). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2Moment.ec': r"""

lemma __acwc2_correctness_eof_8 ['i] (rs:'i list) (w:'i->real) (d:'i->real distr) :
 (forall i,i \in rs=>acwc2_centered_bounded(d i)(w i)) =>
 E(djoin(map d rs))(fun xs=>(acwc2_sum xs)^8)<=
 105%r*(Bigreal.BRA.big predT(fun i=>(w i)^2)rs)^4.
proof. exact (acwc2_independent_eighth rs w d). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2Concentration.ec': r"""

lemma __acwc2_correctness_eof_9 ['k 'm 'a]
 (dk:'k distr) (g:'k->'a distr) (ms:'m list)
 (f:'k->'m->'a->real) (c:'k->real) eps K :
 is_finite(support dk) =>is_lossless dk =>0%r<eps =>0%r<=K =>
 (forall k,k \in dk=>is_finite(support(g k)) /\ is_lossless(g k) /\ 0%r<=c k) =>
 (forall k m x,k \in dk=>m \in ms=>x \in g k=>0%r<=f k m x<=1%r) =>
 (forall k m,k \in dk=>m \in ms=>E(g k)(fun x=>(f k m x-c k)^8)<=K) =>
 E dk(fun k=>E(g k)(fun x=>acwc2_finite_max ms(fun m=>f k m x)))<=
 E dk c+eps+(size ms)%r*K/(eps^8).
proof. exact (acwc2_expected_max_concentration dk g ms f c eps K). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2Numerical.ec': r"""

lemma __acwc2_correctness_eof_1 (average worst:real) :
 average<1%r/(2%r^354) => worst<=average+acwc2_epsilon+acwc2_union_tail =>
 worst<1%r/(2%r^353).
proof. exact (acwc2_numerical_combination average worst). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2Oracle.ec': r"""

lemma __acwc2_correctness_eof_10 g gm0 pk0 sk0 msg0 r0 :
 pke_domain r0 => acwc2_cache_matches g gm0 =>
 phoare[ACWC2RoundTrip(ACWC2HashG).run:
 pk=pk0 /\ sk=sk0 /\ msg=msg0 /\ r=r0 /\ ROG.m=gm0 ==>
 res=acwc2_failure g pk0 sk0 msg0 r0 /\ ROG.m=gm0]=1%r.
proof. exact (acwc2_prepared_roundtrip_correct g gm0 pk0 sk0 msg0 r0). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2Mean.ec': r"""

lemma __acwc2_correctness_eof_11 w msg :
 E acwc2_eager_g_law (fun g=>(acwc2_weighted_bad w msg g-acwc2_base_mean w)^8) <=
 105%r*(BRA.big predT (fun r=>(acwc2_r_weight r)^2) acwc2_r_enum)^4.
proof. exact (acwc2_eager_eighth_bound w msg). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2KeyMean.ec': r"""

lemma __acwc2_correctness_eof_12 &m :
 E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]))
   (fun (out:keygen_output)=>acwc2_base_mean out.`1)<1%r/(2%r^354).
proof. exact (acwc2_fresh_key_mean_bound &m). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2Error.ec': r"""

lemma __acwc2_correctness_eof_13 w g : pke_key_relation w =>
 acwc2_worst_error w g<=
 acwc2_finite_max acwc2_message_enum (fun msg=>acwc2_weighted_bad w msg g).
proof. exact (acwc2_worst_error_bound w g). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2Execution.ec': r"""

lemma __acwc2_correctness_eof_14 &m w pads msg :
 Pr[ACWC2FixedOracleTrial.run(pads,w.`kg_pk,w.`kg_sk,msg) @ &m:res]=
 acwc2_message_error w (acwc2_gfun pads) msg.
proof. exact (acwc2_fixed_oracle_trial_error &m w pads msg). qed.
""",
    'acwc2_correctness/NTRUPlus768ACWC2WorstCase.ec': r"""

lemma __acwc2_correctness_eof_15 &m :
 E (mk(fun z=>Pr[KeygenSource(FreshExpand).guess(witness) @ &m:res=z]))
  (fun (out:keygen_output)=>E acwc2_gpads_law
   (fun (pads:W8.t Array192.t list)=>acwc2_finite_max acwc2_message_enum
    (fun (msg:W8.t Array96.t)=>
      Pr[ACWC2FixedOracleTrial.run(pads,out.`1.`kg_pk,out.`1.`kg_sk,msg) @ &m:res])))
 <1%r/(2%r^353).
proof. exact (acwc2_fresh_worst_actual_calls &m). qed.
""",
}

SEMANTIC_TARGETS = {'acwc2_correctness/NTRUPlus768ACWC2BaseModel.ec': 'acwc2_base_failureE',
 'acwc2_correctness/NTRUPlus768ACWC2Collision.ec': 'acwc2_r_weight_collision',
 'acwc2_correctness/NTRUPlus768ACWC2Concentration.ec': 'acwc2_expected_max_concentration',
 'acwc2_correctness/NTRUPlus768ACWC2Domains.ec': 'acwc2_message_cardinality',
 'acwc2_correctness/NTRUPlus768ACWC2Error.ec': 'acwc2_worst_error_bound',
 'acwc2_correctness/NTRUPlus768ACWC2Execution.ec': 'acwc2_fixed_oracle_trial_error',
 'acwc2_correctness/NTRUPlus768ACWC2KeyMean.ec': 'acwc2_fresh_key_mean_bound',
 'acwc2_correctness/NTRUPlus768ACWC2Mean.ec': 'acwc2_eager_eighth_bound',
 'acwc2_correctness/NTRUPlus768ACWC2Model.ec': 'acwc2_dec_reject_base',
 'acwc2_correctness/NTRUPlus768ACWC2Moment.ec': 'acwc2_independent_eighth',
 'acwc2_correctness/NTRUPlus768ACWC2MomentConvex.ec': 'acwc2_centered_chord',
 'acwc2_correctness/NTRUPlus768ACWC2Numerical.ec': 'acwc2_numerical_combination',
 'acwc2_correctness/NTRUPlus768ACWC2Oracle.ec': 'acwc2_prepared_roundtrip_correct',
 'acwc2_correctness/NTRUPlus768ACWC2Procedures.ec': 'acwc2_roundtrip_lossless',
 'acwc2_correctness/NTRUPlus768ACWC2Recovery.ec': 'acwc2_full_roundtrip_correct',
 'acwc2_correctness/NTRUPlus768ACWC2WorstCase.ec': 'acwc2_fresh_worst_actual_calls'}

MODULE_BINDERS = {'acwc2_correctness/NTRUPlus768ACWC2BaseModel.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2Collision.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2Concentration.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2Domains.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2Error.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2Execution.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2KeyMean.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2Mean.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2Model.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2Moment.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2MomentConvex.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2Numerical.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2Oracle.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2Procedures.ec': ('G',),
 'acwc2_correctness/NTRUPlus768ACWC2Recovery.ec': (),
 'acwc2_correctness/NTRUPlus768ACWC2WorstCase.ec': ()}

NEGATIVE_PROOFS = ('acwc2_correctness/NTRUPlus768ACWC2BaseModel.ec',
 'acwc2_correctness/NTRUPlus768ACWC2Model.ec',
 'acwc2_correctness/NTRUPlus768ACWC2Procedures.ec',
 'acwc2_correctness/NTRUPlus768ACWC2Recovery.ec',
 'acwc2_correctness/NTRUPlus768ACWC2Domains.ec',
 'acwc2_correctness/NTRUPlus768ACWC2Collision.ec',
 'acwc2_correctness/NTRUPlus768ACWC2MomentConvex.ec',
 'acwc2_correctness/NTRUPlus768ACWC2Moment.ec',
 'acwc2_correctness/NTRUPlus768ACWC2Concentration.ec',
 'acwc2_correctness/NTRUPlus768ACWC2Numerical.ec',
 'acwc2_correctness/NTRUPlus768ACWC2Oracle.ec',
 'acwc2_correctness/NTRUPlus768ACWC2Mean.ec',
 'acwc2_correctness/NTRUPlus768ACWC2KeyMean.ec',
 'acwc2_correctness/NTRUPlus768ACWC2Error.ec',
 'acwc2_correctness/NTRUPlus768ACWC2Execution.ec',
 'acwc2_correctness/NTRUPlus768ACWC2WorstCase.ec')
