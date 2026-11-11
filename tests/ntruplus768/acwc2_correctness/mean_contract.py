"""Concrete base-envelope centering and the actual PKE average projection."""
BASE='ntruplus/proof/768/ref/acwc2_correctness/'
MEAN=BASE+'NTRUPlus768ACWC2Mean.ec'
KEYMEAN=BASE+'NTRUPlus768ACWC2KeyMean.ec'
RULES=(
 (MEAN,'weighted envelope averages per-input base indicators with CBD weights',r'op acwc2_weighted_bad (w:keygen_witness) (msg:W8.t Array96.t) (g:acwc2_g_function) = BRA.big predT (fun r=>acwc2_r_weight r*b2r(acwc2_pad_bad w msg r (g r))) acwc2_r_enum.'),
 (MEAN,'each summand is centered using its own fixed-key fixed-r pad mean',r'op acwc2_centered_value (w:keygen_witness) (msg:W8.t Array96.t) (r:pke_poly) (pad:W8.t Array192.t) = acwc2_r_weight r*(b2r(acwc2_pad_bad w msg r pad)-mu uniform192(acwc2_pad_bad w msg r)).'),
 (MEAN,'concrete centered law samples one uniform pad for that coordinate',r'op acwc2_centered_distr w msg r = dmap uniform192(acwc2_centered_value w msg r).'),
 (MEAN,'fixed-message mean identifies the key-dependent base mean',r'lemma acwc2_fixed_mean_base w msg : acwc2_fixed_mean w msg=acwc2_base_mean w.'),
 (MEAN,'concrete bounded-centered premises are proved without an assumed moment',r'lemma acwc2_actual_centered_bounded w msg r : acwc2_centered_bounded (acwc2_centered_distr w msg r) (acwc2_r_weight r).'),
 (KEYMEAN,'actual previous PKE trial returns the complete base-failure event',r'lemma acwc2_pke_trial_value (x0:kem_keygen_observation) : hoare[PKEAverageTrial.run:x=x0 ==> res=acwc2_base_failure x0.`1.`1 (poly_cbd1_spec x0.`3) (poly_cbd1_spec x0.`2)].'),
 (KEYMEAN,'stateless key observer samples independent r and code buffers',r'module ACWC2BaseObserver = { proc guess(out:keygen_output) : bool = { var bs:W8.t Array192.t*W8.t Array192.t; bs <$ uniform192 `*` uniform192; return acwc2_base_failure out.`1 (poly_cbd1_spec bs.`2) (poly_cbd1_spec bs.`1); } }.'),
)
MUTATIONS=(
 ('weighted-envelope-drops-CBD-point-mass',MEAN,'fun r=>acwc2_r_weight r*b2r(acwc2_pad_bad w msg r (g r))','fun r=>b2r(acwc2_pad_bad w msg r (g r))'),
 ('single-coordinate-centered-mean-replaced-with-whole-key-mean',MEAN,'b2r(acwc2_pad_bad w msg r pad)-mu uniform192(acwc2_pad_bad w msg r)','b2r(acwc2_pad_bad w msg r pad)-acwc2_base_mean w'),
 ('centered-Bernoulli-indicator-assumed-fair',MEAN,'b2r(acwc2_pad_bad w msg r pad)-mu uniform192(acwc2_pad_bad w msg r)','b2r(acwc2_pad_bad w msg r pad)-1%r/2%r'),
 ('centered-support-bound-assumed-as-extra-premise',MEAN,'lemma acwc2_actual_centered_bounded w msg r :','lemma acwc2_actual_centered_bounded w msg r : acwc2_centered_bounded (acwc2_centered_distr w msg r) (acwc2_r_weight r) =>'),
 ('key-mean-projects-reference-trial-instead-of-actual-PKE',KEYMEAN,'hoare[PKEAverageTrial.run:x=x0 ==>','hoare[ReferencePKETrial.run:x=x0 ==>'),
 ('key-mean-reuses-randomness-buffer-as-code',KEYMEAN,'(poly_cbd1_spec bs.`2) (poly_cbd1_spec bs.`1);','(poly_cbd1_spec bs.`1) (poly_cbd1_spec bs.`1);'),
)

RULES+=((MEAN,'actual per-entry envelope discharges the eighth-moment theorem with no numerical assumption',r'lemma acwc2_eager_eighth_bound w msg : E acwc2_eager_g_law (fun g=>(acwc2_weighted_bad w msg g-acwc2_base_mean w)^8) <= 105%r*(BRA.big predT (fun r=>(acwc2_r_weight r)^2) acwc2_r_enum)^4.'),)
MUTATIONS+=(
 ('independence-applied-to-actual-transformed-failures',MEAN,'fun r=>acwc2_r_weight r*b2r(acwc2_pad_bad w msg r (g r))','fun r=>acwc2_r_weight r*b2r(acwc2_failure g w.`kg_pk w.`kg_sk msg r)'),
 ('concrete-eighth-moment-assumes-a-per-key-average-bound',MEAN,'lemma acwc2_eager_eighth_bound w msg :','lemma acwc2_eager_eighth_bound w msg : acwc2_base_mean w<1%r/(2%r^354) =>'),
)
