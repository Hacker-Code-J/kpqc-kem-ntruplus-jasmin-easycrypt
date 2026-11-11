require import AllCore StdOrder.
require import NTRUPlus768RTModel NTRUPlus768RTKernelTypes.
require import NTRUPlus768RTBounds NTRUPlus768RTAdaptive NTRUPlus768RTReduction.
require import NTRUPlus768RTPhaseCost NTRUPlus768RTOuterCost.
import IntOrder.

(* These closed prices use the source-calibrated word/array/list model.
   The accompanying calibration gate binds each price to the executed
   source block; it is part of the trusted cost-instrumentation frontend.
   The ledger and kernel profiles are erased proof observations.
   tA reserves only the adversary's own work, excluding oracle bodies.
   The actual invocation flag is zero or one, so this reserve is paid
   at most once. No unknown whole-reduction time or kernel price occurs.
   The result is not a native-cycle, integer bit-cost or parameter-family
   PPT theorem. Ideal ROM operations remain explicit model primitives. *)
(* The hardness games call run. Its single call to measure and result
   projection have a real entry/caller/return cost after ghost erasure;
   output equivalence alone does not erase this dispatcher cost. *)
op rt_run_di_overhead=rt_outer_copy 768+rt_outer_frame 1 0+2.
op rt_run_do_overhead=rt_outer_copy 768+rt_outer_frame 1 0+2.
op rt_run_co_overhead=rt_outer_copy(2*768)+rt_outer_frame 2 768+2+rt_outer_copy 768.
op rt_complete_di_charge tA p k =
 rt_run_di_overhead+rt_outer_di_charge tA k+rt_phase_charge rt_concrete_phase_prices p.
op rt_complete_do_charge tA p k =
 rt_run_do_overhead+rt_outer_do_charge tA k+rt_phase_charge rt_concrete_phase_prices p.
op rt_complete_co_charge tA p k =
 rt_run_co_overhead+rt_outer_co_charge tA k+rt_phase_charge rt_concrete_phase_prices p.
op rt_complete_di_bound tA q b =
 rt_run_di_overhead+rt_outer_di_bound tA+rt_q_envelope rt_concrete_phase_prices q b.
op rt_complete_do_bound tA q b =
 rt_run_do_overhead+rt_outer_do_bound tA+rt_q_envelope rt_concrete_phase_prices q b.
op rt_complete_co_bound tA q b =
 rt_run_co_overhead+rt_outer_co_bound tA+rt_q_envelope rt_concrete_phase_prices q b.

lemma rt_complete_phase_cap calls p : rt_invocation_profile calls p=>
 rt_phase_charge rt_concrete_phase_prices p<=
 rt_q_envelope rt_concrete_phase_prices p.`rp_q p.`rp_b.
proof.
 move=>hp;have hi:=rt_invocation_bounds calls p hp.
 apply(rt_concrete_phase_q_bound p);move:hi;rewrite /rt_callback_ok;smt().
qed.
lemma rt_complete_di_cap tA p k : 0<=tA=>
 rt_invocation_profile k.`rtk_adversary p=>rtk_le k rt_di_kernel_bound=>
 rt_complete_di_charge tA p k<=rt_complete_di_bound tA p.`rp_q p.`rp_b.
proof.
 move=>ht hp hk;have houter:=rt_outer_di_cap tA k ht hk.
 have hphase:=rt_complete_phase_cap k.`rtk_adversary p hp.
 rewrite /rt_complete_di_charge /rt_complete_di_bound;smt().
qed.
lemma rt_complete_do_cap tA p k : 0<=tA=>
 rt_invocation_profile k.`rtk_adversary p=>rtk_le k rt_do_kernel_bound=>
 rt_complete_do_charge tA p k<=rt_complete_do_bound tA p.`rp_q p.`rp_b.
proof.
 move=>ht hp hk;have houter:=rt_outer_do_cap tA k ht hk.
 have hphase:=rt_complete_phase_cap k.`rtk_adversary p hp.
 rewrite /rt_complete_do_charge /rt_complete_do_bound;smt().
qed.
lemma rt_complete_co_cap tA p k : 0<=tA=>
 rt_invocation_profile k.`rtk_adversary p=>rtk_le k rt_co_kernel_bound=>
 rt_complete_co_charge tA p k<=rt_complete_co_bound tA p.`rp_q p.`rp_b.
proof.
 move=>ht hp hk;have houter:=rt_outer_co_cap tA k ht hk.
 have hphase:=rt_complete_phase_cap k.`rtk_adversary p hp.
 rewrite /rt_complete_co_charge /rt_complete_co_bound;smt().
qed.

lemma rt_complete_self_reserve tA q b :
 rt_complete_di_bound tA q b=tA+rt_complete_di_bound 0 q b /\
 rt_complete_do_bound tA q b=tA+rt_complete_do_bound 0 q b /\
 rt_complete_co_bound tA q b=tA+rt_complete_co_bound 0 q b.
proof.
 have ha:=rt_outer_bound_values tA;have hz:=rt_outer_bound_values 0.
 rewrite /rt_complete_di_bound /rt_complete_do_bound /rt_complete_co_bound;smt().
qed.

(* Q counts every public callback, including repeated queries and raw
   calls requesting zero output. B sums actual raw input lengths.
   Neither is the distinct-H bound qC in the security theorem. *)
lemma rt_complete_budget_monotone q b Q B :
 0<=q<=Q=>b<=B=>
 rt_q_envelope rt_concrete_phase_prices q b<=
 rt_q_envelope rt_concrete_phase_prices Q B.
proof.
 move=>hq hb;have hs:=rt_product_upper q q Q hq hq.
 have hc:=rt_concrete_phase_prices_ok.
 have h1:=rt_mul_mono rt_concrete_phase_prices.`pc_call q Q.
 have h2:=rt_mul_mono rt_concrete_phase_prices.`pc_input b B.
 have h3:=rt_mul_mono rt_concrete_phase_prices.`pc_visit (3*q*q+q)(3*Q*Q+Q).
 have h4:=rt_mul_mono rt_concrete_phase_prices.`pc_compare (1248*q*q+1152*q)(1248*Q*Q+1152*Q).
 have h5:=rt_mul_mono rt_concrete_phase_prices.`pc_cons (2*q*q+q)(2*Q*Q+Q).
 have h6:=rt_mul_mono rt_concrete_phase_prices.`pc_encrypt (q*q)(Q*Q).
 have h7:=rt_mul_mono rt_concrete_phase_prices.`pc_candidate (q*q+q)(Q*Q+Q).
 move:hc;rewrite /rt_prices_ok /rt_q_envelope;smt().
qed.

lemma rt_complete_di_budget tA p k Q B : 0<=tA=>
 rt_invocation_profile k.`rtk_adversary p=>rtk_le k rt_di_kernel_bound=>
 p.`rp_q<=Q=>p.`rp_b<=B=>
 rt_complete_di_charge tA p k<=rt_complete_di_bound tA Q B.
proof.
 move=>ht hp hk hq hb;have hc:=rt_complete_di_cap tA p k ht hp hk.
 have hi:=rt_invocation_bounds k.`rtk_adversary p hp.
 have hn:0<=p.`rp_q by move:hi;rewrite /rt_cost_ok /rt_nonnegative;smt().
 have hqq:0<=p.`rp_q<=Q by smt().
 have hm:=rt_complete_budget_monotone p.`rp_q p.`rp_b Q B hqq hb.
 move:hc;rewrite /rt_complete_di_bound;smt().
qed.
lemma rt_complete_do_budget tA p k Q B : 0<=tA=>
 rt_invocation_profile k.`rtk_adversary p=>rtk_le k rt_do_kernel_bound=>
 p.`rp_q<=Q=>p.`rp_b<=B=>
 rt_complete_do_charge tA p k<=rt_complete_do_bound tA Q B.
proof.
 move=>ht hp hk hq hb;have hc:=rt_complete_do_cap tA p k ht hp hk.
 have hi:=rt_invocation_bounds k.`rtk_adversary p hp.
 have hn:0<=p.`rp_q by move:hi;rewrite /rt_cost_ok /rt_nonnegative;smt().
 have hqq:0<=p.`rp_q<=Q by smt().
 have hm:=rt_complete_budget_monotone p.`rp_q p.`rp_b Q B hqq hb.
 move:hc;rewrite /rt_complete_do_bound;smt().
qed.
lemma rt_complete_co_budget tA p k Q B : 0<=tA=>
 rt_invocation_profile k.`rtk_adversary p=>rtk_le k rt_co_kernel_bound=>
 p.`rp_q<=Q=>p.`rp_b<=B=>
 rt_complete_co_charge tA p k<=rt_complete_co_bound tA Q B.
proof.
 move=>ht hp hk hq hb;have hc:=rt_complete_co_cap tA p k ht hp hk.
 have hi:=rt_invocation_bounds k.`rtk_adversary p hp.
 have hn:0<=p.`rp_q by move:hi;rewrite /rt_cost_ok /rt_nonnegative;smt().
 have hqq:0<=p.`rp_q<=Q by smt().
 have hm:=rt_complete_budget_monotone p.`rp_q p.`rp_b Q B hqq hb.
 move:hc;rewrite /rt_complete_co_bound;smt().
qed.

lemma rt_complete_phase_polynomial q b :
 rt_q_envelope rt_concrete_phase_prices q b=
 10909917*q*q+32450882*q+64*b+370295.
proof.
 have hv:=rt_concrete_phase_price_values.
 move:hv;rewrite /rt_q_envelope;move=>[-> [-> [-> [-> [-> [-> [-> ->]]]]]]];ring.
qed.
lemma rt_run_dispatcher_values :
 rt_run_di_overhead=2309 /\ rt_run_do_overhead=2309 /\ rt_run_co_overhead=9222.
proof.
 by rewrite /rt_run_di_overhead /rt_run_do_overhead /rt_run_co_overhead
 /rt_outer_copy /rt_outer_frame.
qed.
lemma rt_complete_bound_values tA q b :
 rt_complete_di_bound tA q b=tA+10909917*q*q+32450882*q+64*b+17679874 /\
 rt_complete_do_bound tA q b=tA+10909917*q*q+32450882*q+64*b+10492283 /\
 rt_complete_co_bound tA q b=tA+10909917*q*q+32450882*q+64*b+18463740.
proof.
 have hv:=rt_outer_bound_values tA;have hr:=rt_run_dispatcher_values.
 rewrite /rt_complete_di_bound /rt_complete_do_bound /rt_complete_co_bound
 rt_complete_phase_polynomial;smt().
qed.
