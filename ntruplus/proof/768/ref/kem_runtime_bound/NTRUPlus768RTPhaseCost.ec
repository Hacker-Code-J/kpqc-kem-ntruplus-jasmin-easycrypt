require import AllCore List StdOrder.
require import NTRUPlus768RTModel NTRUPlus768RTBounds NTRUPlus768RTPrimitiveCost.
require import NTRUPlus768RTKernelCosts NTRUPlus768RTKernelCostsSim.
require import NTRUPlus768HistModel NTRUPlus768HistTable NTRUPlus768HistLookup.
require import NTRUPlus768FOEagerG NTRUPlus768CostExtract.
from Jasmin require import JWord.
require import Array224 Array1152.
import IntOrder.

(* Source-block cost certificates. The checked calibration manifest binds
   these recurrences to every non-kernel source block. Lists use immutable
   cons cells with shared tails; a newly stored fixed-array payload is
   copied. Array by-value boundaries cost allocation+read+write per cell.
   Ideal ROM access/sampling is an explicit model boundary. Integer guards
   and arithmetic are unit-cost, not unbounded-integer bit operations.
   These equations never treat a polynomial/quantified specification as
   one executable instruction. The two free kernel costs are instantiated
   from the checked SimEncrypt and SecCandidate implementations. *)
op rt_phase_copy(n:int)=3*n.
op rt_phase_size(n:int)=8*n+5.
op rt_phase_nth(n:int)=10*n+8.
op rt_phase_of_list(n:int)=5+10*n+n*rt_phase_nth n.
op rt_phase_decode_fixed=64+rt_phase_of_list 1153+24*1153.
op rt_phase_decode(n:int)=4*rt_phase_size n+rt_phase_decode_fixed.
op rt_phase_prefix_fixed=32+24*224.
op rt_phase_stream_fixed=64+4*(rt_phase_copy(1152+224)+8)+32*224.
(* These local block ceilings are independently recomputed from the
   frozen source: scalar tokens, fixed-array copy cells, initializer cells,
   guards and persistent-list operations. Callee bodies are separate. *)
op rt_phase_store_fixed=37202+44211+16147+14019+14019.
op rt_phase_put_fixed=3618+415+1081.
op rt_phase_lookup_fixed=17823+20785.
op rt_phase_extract_fixed=27676.
op rt_phase_history_cons=3*(352+2)+8.
op rt_phase_g_cons=3*(1152+2)+8.
op rt_phase_keep_visit=5132.
op rt_phase_reverse_visit=3198.
op rt_phase_lookup_visit=11139+26805+20785+168.
op rt_phase_extract_visit=51919.
op rt_phase_visit=65536.
op rt_phase_compare=21.
op rt_phase_cons=rt_phase_g_cons.
op rt_phase_input=64.
(* Sum of the finite callback source blocks in phase-calibration.json;
   mutually exclusive callback cases may all be included conservatively. *)
op rt_phase_callback_fixed=344206.
op rt_phase_call=2*rt_phase_decode_fixed+40+rt_phase_prefix_fixed+
 rt_phase_stream_fixed+rt_phase_callback_fixed.
(* Forwarding source blocks sum to 8652+8652+12118+1=29423.
   The power-of-two ceiling also dominates array bindings. Cons is separate. *)
op rt_phase_logged_g_fixed=32768.
(* Sum of the setup source blocks plus three typed-F wrappers, the
   concrete 194-unit uniform32 source expansion and ideal initializers.
   Setup is paid even when Q=0, on each reached extraction path. *)
op rt_phase_setup_fixed=320757+3*7212+194+32.
(* Sim's measured body inlines these four wrappers. Their common native
   calls, tail/peel copies and final G call are already in the measured
   body; only the removed call/entry/return boundaries are added here.
   This is separate from AHPublicG/SimOracles/SecGLogged in logged_g_fixed. *)
op rt_phase_wrapper_boundary(inputs outputs arity return_fields:int)=
 3*inputs+(return_fields+3*outputs)+(2+arity+3*outputs).
op rt_phase_fohash_boundary=rt_phase_wrapper_boundary 768 192 1 1.
op rt_phase_gprepare_boundary=rt_phase_wrapper_boundary 768 2305 1 2.
op rt_phase_foghash_boundary=rt_phase_wrapper_boundary 1153 192 1 1.
op rt_phase_sotp_boundary=rt_phase_wrapper_boundary 288 768 2 1.
op rt_phase_encrypt_wrapper_fixed=rt_phase_fohash_boundary+
 rt_phase_gprepare_boundary+rt_phase_foghash_boundary+rt_phase_sotp_boundary.
op rt_calibrated_phase_prices (c_encrypt c_candidate:int):rt_phase_prices=
 {|pc_call=rt_phase_call;pc_input=rt_phase_input;
 pc_visit=rt_phase_visit;pc_compare=rt_phase_compare;pc_cons=rt_phase_cons;
 pc_encrypt=c_encrypt+rt_phase_logged_g_fixed+rt_phase_encrypt_wrapper_fixed;
 pc_candidate=c_candidate+rt_word_compare_steps 768;
 pc_extract_init=rt_phase_setup_fixed+rt_phase_extract_fixed|}.

(* Worst-case block prices retain returned actual visit/encryption/byte
   comparison counts. A cons is charged only when the corresponding source
   branch allocates it. The metadata checker validates this attribution. *)
op rt_phase_put_body(n k:int)=rt_phase_put_fixed+
 rt_phase_visit*(n+k)+rt_key_compare_steps*n+rt_phase_history_cons*(2*k+1).
op rt_phase_lookup_body(c_encrypt v k comparisons:int)=rt_phase_lookup_fixed+
 rt_phase_visit*v+rt_phase_compare*comparisons+
 (c_encrypt+rt_phase_logged_g_fixed+rt_phase_encrypt_wrapper_fixed)*k+rt_phase_g_cons*k.
op rt_phase_extract_body(c_candidate visits:int)=rt_phase_extract_fixed+
 (rt_phase_visit+c_candidate+rt_word_compare_steps 768)*visits.
op rt_phase_callback_body(n:int)=2*rt_phase_decode n+rt_phase_prefix_fixed+
 rt_phase_stream_fixed+rt_phase_callback_fixed.

lemma rt_phase_encrypt_wrapper_calibration :
 rt_phase_fohash_boundary=3460 /\ rt_phase_gprepare_boundary=16139 /\
 rt_phase_foghash_boundary=4615 /\ rt_phase_sotp_boundary=5477 /\
 rt_phase_encrypt_wrapper_fixed=29691.
proof.
 by rewrite /rt_phase_encrypt_wrapper_fixed /rt_phase_fohash_boundary
 /rt_phase_gprepare_boundary /rt_phase_foghash_boundary /rt_phase_sotp_boundary
 /rt_phase_wrapper_boundary.
qed.
lemma rt_phase_compare_calibration :
 rt_key_compare_steps<=rt_phase_compare*128 /\
 rt_byte_compare_steps 32<=rt_phase_compare*32 /\
 rt_byte_compare_steps 1152<=rt_phase_compare*1152.
proof. by rewrite /rt_key_compare_steps /rt_byte_compare_steps /rt_phase_compare. qed.
lemma rt_phase_node_calibration :
 0<=rt_phase_history_cons<=rt_phase_cons /\
 0<=rt_phase_g_cons<=rt_phase_cons.
proof. by rewrite /rt_phase_history_cons /rt_phase_g_cons /rt_phase_cons. qed.
lemma rt_phase_visit_calibration :
 0<=rt_phase_keep_visit<=rt_phase_visit /\
 0<=rt_phase_reverse_visit<=rt_phase_visit /\
 0<=rt_phase_lookup_visit<=rt_phase_visit /\
 0<=rt_phase_extract_visit<=rt_phase_visit.
proof.
 by rewrite /rt_phase_keep_visit /rt_phase_reverse_visit /rt_phase_lookup_visit
 /rt_phase_extract_visit /rt_phase_visit /rt_phase_copy.
qed.
lemma rt_phase_raw_linear n : 0<=n=>
 rt_phase_callback_body n=rt_phase_call+rt_phase_input*n.
proof.
 move=>hn;rewrite /rt_phase_callback_body /rt_phase_decode /rt_phase_size
 /rt_phase_call /rt_phase_callback_fixed /rt_phase_input;ring.
qed.
lemma rt_phase_of_list_bound n : 0<=n<=1153=>
 0<=rt_phase_of_list n<=rt_phase_of_list 1153.
proof. rewrite /rt_phase_of_list /rt_phase_nth;smt(). qed.
lemma rt_phase_fixed_nonnegative :
 0<=rt_phase_call /\ 0<=rt_phase_input /\ 0<=rt_phase_visit /\
 0<=rt_phase_compare /\ 0<=rt_phase_cons /\
 0<=rt_phase_setup_fixed /\ 0<=rt_phase_extract_fixed /\
 0<=rt_phase_logged_g_fixed /\ 0<=rt_phase_encrypt_wrapper_fixed.
proof.
 by rewrite /rt_phase_call /rt_phase_callback_fixed /rt_phase_input /rt_phase_visit /rt_phase_compare
 /rt_phase_cons /rt_phase_g_cons /rt_phase_setup_fixed /rt_phase_extract_fixed
 /rt_phase_logged_g_fixed /rt_phase_encrypt_wrapper_fixed
 /rt_phase_fohash_boundary /rt_phase_gprepare_boundary /rt_phase_foghash_boundary
 /rt_phase_sotp_boundary /rt_phase_wrapper_boundary /rt_phase_decode_fixed /rt_phase_of_list /rt_phase_nth
 /rt_phase_prefix_fixed /rt_phase_stream_fixed /rt_phase_store_fixed
 /rt_phase_put_fixed /rt_phase_lookup_fixed /rt_phase_copy.
qed.
lemma rt_calibrated_prices_ok ce cc : 0<=ce=>0<=cc=>
 rt_prices_ok(rt_calibrated_phase_prices ce cc).
proof.
 move=>he hc;have hp:=rt_phase_fixed_nonnegative.
 rewrite /rt_prices_ok /rt_calibrated_phase_prices /= /rt_word_compare_steps;smt().
qed.
lemma rt_phase_put_bound ce cc n k : 0<=n=>0<=k=>
 rt_phase_put_body n k<=
 (rt_calibrated_phase_prices ce cc).`pc_call+
 (rt_calibrated_phase_prices ce cc).`pc_visit*(n+k)+
 (rt_calibrated_phase_prices ce cc).`pc_compare*(128*n)+
 (rt_calibrated_phase_prices ce cc).`pc_cons*(2*k+1).
proof.
 rewrite /rt_phase_put_body /rt_calibrated_phase_prices /=
 /rt_phase_call /rt_phase_callback_fixed /rt_phase_input /rt_phase_visit /rt_phase_compare
 /rt_phase_cons /rt_phase_g_cons /rt_phase_history_cons /rt_key_compare_steps
 /rt_phase_decode_fixed /rt_phase_of_list /rt_phase_nth
 /rt_phase_prefix_fixed /rt_phase_stream_fixed /rt_phase_store_fixed
 /rt_phase_put_fixed /rt_phase_lookup_fixed /rt_phase_copy;smt().
qed.
lemma rt_phase_lookup_bound ce cc v k comparisons :
 rt_phase_lookup_body ce v k comparisons<=
 (rt_calibrated_phase_prices ce cc).`pc_call+
 (rt_calibrated_phase_prices ce cc).`pc_visit*v+
 (rt_calibrated_phase_prices ce cc).`pc_compare*comparisons+
 (rt_calibrated_phase_prices ce cc).`pc_encrypt*k+
 (rt_calibrated_phase_prices ce cc).`pc_cons*k.
proof.
 rewrite /rt_phase_lookup_body /rt_calibrated_phase_prices /= /rt_phase_cons
 /rt_phase_call /rt_phase_callback_fixed /rt_phase_decode_fixed /rt_phase_of_list /rt_phase_nth
 /rt_phase_prefix_fixed /rt_phase_stream_fixed /rt_phase_store_fixed
 /rt_phase_put_fixed /rt_phase_lookup_fixed /rt_phase_copy;smt().
qed.
lemma rt_phase_extract_bound ce cc v :
 rt_phase_setup_fixed+rt_phase_extract_body cc v<=
 (rt_calibrated_phase_prices ce cc).`pc_extract_init+
 (rt_calibrated_phase_prices ce cc).`pc_visit*v+
 (rt_calibrated_phase_prices ce cc).`pc_candidate*v.
proof.
 rewrite /rt_phase_extract_body /rt_calibrated_phase_prices /=;smt().
qed.

(* The counts used by each source certificate are the results of the
   actual existing procedures, not an assumed external trace. The source
   calibration checker separately validates the coverage of the prices. *)
lemma rt_hist_put_source_certificate ce cc x0 y0 xs0 :
 hoare[HistTable.put:x=x0 /\ y=y0 /\ xs=xs0 ==>
 rt_phase_put_body(size xs0)(size res.`1-1)<=
 (rt_calibrated_phase_prices ce cc).`pc_call+
 (rt_calibrated_phase_prices ce cc).`pc_visit*res.`2+
 (rt_calibrated_phase_prices ce cc).`pc_compare*res.`3+
 (rt_calibrated_phase_prices ce cc).`pc_cons*(2*(size res.`1-1)+1)].
proof.
 conseq(hist_table_put_spec x0 y0 xs0)=> /> &hr result -> -> ->.
 rewrite hist_put_size /=.
 have h:=rt_phase_put_bound ce cc(size xs{hr})(size(hist_keep x{hr} xs{hr}))
 (size_ge0 xs{hr})(size_ge0(hist_keep x{hr} xs{hr}));smt().
qed.
lemma rt_hist_lookup_source_certificate (G<:FOGPort) ce cc :
 hoare[HistLookup(G).run:true ==>
 rt_phase_lookup_body ce res.`2 res.`3 res.`4<=
 (rt_calibrated_phase_prices ce cc).`pc_call+
 (rt_calibrated_phase_prices ce cc).`pc_visit*res.`2+
 (rt_calibrated_phase_prices ce cc).`pc_compare*res.`4+
 (rt_calibrated_phase_prices ce cc).`pc_encrypt*res.`3+
 (rt_calibrated_phase_prices ce cc).`pc_cons*res.`3].
proof.
 conseq(_:true ==>true);first smt(rt_phase_lookup_bound).
 by trivial.
qed.
lemma rt_extract_source_certificate ce cc pk0 ct0 excluded0 queries0 :
 hoare[CostExtract.run:pk=pk0 /\ ct=ct0 /\ excluded=excluded0 /\ queries=queries0 ==>
 0<=res.`2 /\
 rt_phase_setup_fixed+rt_phase_extract_body cc res.`2<=
 (rt_calibrated_phase_prices ce cc).`pc_extract_init+
 (rt_calibrated_phase_prices ce cc).`pc_visit*res.`2+
 (rt_calibrated_phase_prices ce cc).`pc_candidate*res.`2].
proof.
 conseq(cost_extract_bounds pk0 ct0 excluded0 queries0);
 smt(rt_phase_extract_bound).
qed.
lemma rt_calibrated_phase_bound ce cc p : 0<=ce=>0<=cc=>
 rt_cost_ok p=>p.`rp_xcalls<=1=>
 rt_phase_charge(rt_calibrated_phase_prices ce cc)p<=
 rt_phase_envelope(rt_calibrated_phase_prices ce cc)
 p.`rp_h p.`rp_d p.`rp_g p.`rp_q p.`rp_b.
proof.
 move=>he hc hp hx;exact(rt_phase_charge_bound
 (rt_calibrated_phase_prices ce cc)p(rt_calibrated_prices_ok ce cc he hc)hp hx).
qed.
lemma rt_calibrated_phase_q_bound ce cc p : 0<=ce=>0<=cc=>
 rt_cost_ok p=>p.`rp_xcalls<=1=>p.`rp_h+p.`rp_d+p.`rp_g<=p.`rp_q=>
 rt_phase_charge(rt_calibrated_phase_prices ce cc)p<=
 rt_q_envelope(rt_calibrated_phase_prices ce cc)p.`rp_q p.`rp_b.
proof.
 move=>he hc hp hx hq;exact(rt_phase_q_bound
 (rt_calibrated_phase_prices ce cc)p(rt_calibrated_prices_ok ce cc he hc)hp hx hq).
qed.

(* The public endpoint has no unconstrained kernel price. These names
   denote the constants derived from the checked costed kernel bodies. *)
op rt_concrete_phase_prices = rt_calibrated_phase_prices
 rt_kernel_sim_encrypt_bound rt_kernel_candidate_bound.
lemma rt_concrete_phase_prices_ok : rt_prices_ok rt_concrete_phase_prices.
proof.
 apply(rt_calibrated_prices_ok rt_kernel_sim_encrypt_bound rt_kernel_candidate_bound);
 by done.
qed.
lemma rt_concrete_phase_q_bound p : rt_cost_ok p=>p.`rp_xcalls<=1=>
 p.`rp_h+p.`rp_d+p.`rp_g<=p.`rp_q=>
 rt_phase_charge rt_concrete_phase_prices p<=
 rt_q_envelope rt_concrete_phase_prices p.`rp_q p.`rp_b.
proof.
 move=>hp hx hq;exact(rt_phase_q_bound rt_concrete_phase_prices p
 rt_concrete_phase_prices_ok hp hx hq).
qed.

lemma rt_concrete_phase_price_values :
 rt_concrete_phase_prices.`pc_call=27058600 /\
 rt_concrete_phase_prices.`pc_input=64 /\
 rt_concrete_phase_prices.`pc_visit=65536 /\
 rt_concrete_phase_prices.`pc_compare=21 /\
 rt_concrete_phase_prices.`pc_cons=3470 /\
 rt_concrete_phase_prices.`pc_encrypt=5381077 /\
 rt_concrete_phase_prices.`pc_candidate=5299084 /\
 rt_concrete_phase_prices.`pc_extract_init=370295.
proof.
 rewrite /rt_concrete_phase_prices /rt_calibrated_phase_prices /=
 /rt_phase_call /rt_phase_callback_fixed /rt_phase_decode_fixed /rt_phase_of_list
 /rt_phase_nth /rt_phase_prefix_fixed /rt_phase_stream_fixed /rt_phase_copy
 /rt_phase_input /rt_phase_visit /rt_phase_compare /rt_phase_cons /rt_phase_g_cons
 /rt_phase_logged_g_fixed /rt_phase_encrypt_wrapper_fixed /rt_phase_fohash_boundary
 /rt_phase_gprepare_boundary /rt_phase_foghash_boundary /rt_phase_sotp_boundary
 /rt_phase_wrapper_boundary /rt_word_compare_steps /rt_phase_setup_fixed /rt_phase_extract_fixed;
 smt().
qed.
