require import AllCore Distr StdOrder.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768SecExtractModel.
require import NTRUPlus768RTKernelTypes NTRUPlus768RTKernels NTRUPlus768RTBounds.
require import NTRUPlus768RTKernelCosts NTRUPlus768RTKernelCostsCalls.
require import NTRUPlus768RTWordCodec NTRUPlus768RTPrimitiveCost NTRUPlus768RTPsiSampler.
require import NTRUPlus768RTFixedWordChecks NTRUPlus768RTFixedCBD.
require import NTRUPlus768RTModel NTRUPlus768RTStore NTRUPlus768RTReduction NTRUPlus768RTWordReduction.
require import NTRUPlus768CCAGame.
require import NTRUPlus768OWCodec NTRUPlus768RawXOF NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768SecGOracles.
import IntOrder.

(* Owned array transfers cost allocation+load+store for each cell. The
   frame includes a call, the argument transfers, and a result binding.
   Selectors and non-ghost constructors at a call site are charged in the
   source-block subtotal below, not silently absorbed into a kernel. *)
op rt_outer_copy(n:int)=3*n.
op rt_outer_frame(arity cells:int)=2+arity+rt_outer_copy cells.

(* Explicit lowering of the fixed zero-array expressions in WordCO,
   RTEncrypt and RTMeasuredOW. The observations are erased. This is a
   finite word-step model, not a CPU-cycle or unbounded bit-cost claim. *)
op rt_outer_zero_steps(n:int)=10*n+5.
op rt_outer_zero_call(n:int)=rt_outer_zero_steps n+rt_outer_frame 0 n.
module RTOuterZero = {
 proc words():pke_poly*int = {
  var out:pke_poly;var i,work:int;
  out<-witness;work<-769;
  i<-0;work<-work+1;work<-work+2;
  while(i<768){
   out.[i]<-W16.zero;work<-work+2;
   i<-i+1;work<-work+2;work<-work+2;
  }
  work<-work+2305;return(out,work);
 }
 proc cipher():W8.t Array1152.t*int = {
  var out:W8.t Array1152.t;var i,work:int;
  out<-witness;work<-1153;
  i<-0;work<-work+1;work<-work+2;
  while(i<1152){
   out.[i]<-W8.zero;work<-work+2;
   i<-i+1;work<-work+2;work<-work+2;
  }
  work<-work+3457;return(out,work);
 }
}.
lemma rt_outer_zero_words_eq (x:pke_poly) :
 (forall j,0<=j<768=>x.[j]=W16.zero)=>x=Array768.init(fun _=>W16.zero).
proof. move=>hx;apply Array768.tP=>j hj;rewrite Array768.initiE //;exact(hx j hj). qed.
lemma rt_outer_zero_cipher_eq (x:W8.t Array1152.t) :
 (forall j,0<=j<1152=>x.[j]=W8.zero)=>x=Array1152.init(fun _=>W8.zero).
proof. move=>hx;apply Array1152.tP=>j hj;rewrite Array1152.initiE //;exact(hx j hj). qed.
lemma rt_outer_zero_words_ll : islossless RTOuterZero.words.
proof. proc;wp;while true(768-i);auto=> />;smt(). qed.
lemma rt_outer_zero_cipher_ll : islossless RTOuterZero.cipher.
proof. proc;wp;while true(1152-i);auto=> />;smt(). qed.
lemma rt_outer_zero_words_spec :
 hoare[RTOuterZero.words:true ==>
 res=(Array768.init(fun _=>W16.zero),rt_outer_zero_steps 768)].
proof.
 proc;wp;while(0<=i<=768 /\ work=772+6*i /\
 forall j,0<=j<i=>out.[j]=W16.zero).
 + auto=> />;smt(Array768.get_setE).
 auto=> />;split;first by smt().
 move=>i out hstop hlo hhi hout;have he:i=768 by smt().
 subst i;split;first exact(rt_outer_zero_words_eq out hout).
 by rewrite /rt_outer_zero_steps.
qed.
lemma rt_outer_zero_cipher_spec :
 hoare[RTOuterZero.cipher:true ==>
 res=(Array1152.init(fun _=>W8.zero),rt_outer_zero_steps 1152)].
proof.
 proc;wp;while(0<=i<=1152 /\ work=1156+6*i /\
 forall j,0<=j<i=>out.[j]=W8.zero).
 + auto=> />;smt(Array1152.get_setE).
 auto=> />;split;first by smt().
 move=>i out hstop hlo hhi hout;have he:i=1152 by smt().
 subst i;split;first exact(rt_outer_zero_cipher_eq out hout).
 by rewrite /rt_outer_zero_steps.
qed.
lemma rt_outer_zero_words_correct :
 phoare[RTOuterZero.words:true ==>res=(sec_zero,rt_outer_zero_steps 768)]=1%r.
proof. conseq rt_outer_zero_words_ll rt_outer_zero_words_spec;rewrite /sec_zero;smt(). qed.
lemma rt_outer_zero_cipher_correct :
 phoare[RTOuterZero.cipher:true ==>
 res=(Array1152.init(fun _=>W8.zero),rt_outer_zero_steps 1152)]=1%r.
proof. by conseq rt_outer_zero_cipher_ll rt_outer_zero_cipher_spec. qed.

(* Each component is a proved actual finite-word body cost plus its
   caller boundary. The sole symbolic price is A's own work, excluding
   oracle bodies; it is not the time of B or of the whole reduction. *)
op rt_concrete_kernel_prices(tA:int):rt_kernel_profile =
 rtk_profile
 (19204+rt_outer_frame 1 768)
 (rt_kernel_unit_bound+rt_outer_frame 1 0)
 (rt_kernel_encode_bound+rt_outer_frame 1 1152)
 (rt_kernel_recover_bound+rt_outer_frame 3 768)
 (rt_kernel_pkeenc_bound+rt_outer_frame 3 1152)
 (rt_fixed_trit_bound+rt_outer_frame 1 0)
 (rt_word_compare_steps 768+rt_outer_frame 2 0)
 (rt_byte_compare_steps 1152+rt_outer_frame 2 0)
 (rt_fixed_cbd_bound+5767+192+rt_outer_frame 0 768)
 tA.

lemma rt_outer_scale_call_cost :
 hoare[RTWordScale3.measure:true ==>
 0<=res.`2+rt_outer_frame 1 768<=(rt_concrete_kernel_prices 0).`rtk_scale].
proof. conseq rt_word_scale3_measure_cost;rewrite /rt_concrete_kernel_prices /rtk_profile /rt_outer_frame /rt_outer_copy;smt(). qed.
lemma rt_outer_unit_call_cost :
 hoare[RTKernelUnit.run:true ==>
 0<=res.`2+rt_outer_frame 1 0<=(rt_concrete_kernel_prices 0).`rtk_unit].
proof. conseq rt_kernel_unit_cost;rewrite /rt_concrete_kernel_prices /rtk_profile /rt_outer_frame /rt_outer_copy;smt(). qed.
lemma rt_outer_encode_call_cost :
 hoare[RTKernelEncode.run:true ==>
 0<=res.`2+rt_outer_frame 1 1152<=(rt_concrete_kernel_prices 0).`rtk_encode].
proof. conseq rt_kernel_encode_cost;rewrite /rt_concrete_kernel_prices /rtk_profile /rt_outer_frame /rt_outer_copy;smt(). qed.
lemma rt_outer_recover_call_cost :
 hoare[RTKernelRecover.run:true ==>
 0<=res.`2+rt_outer_frame 3 768<=(rt_concrete_kernel_prices 0).`rtk_recover].
proof. conseq rt_kernel_recover_cost;rewrite /rt_concrete_kernel_prices /rtk_profile /rt_outer_frame /rt_outer_copy;smt(). qed.
lemma rt_outer_encrypt_call_cost :
 hoare[RTKernelPKEEnc.run:true ==>
 0<=res.`2+rt_outer_frame 3 1152<=(rt_concrete_kernel_prices 0).`rtk_encrypt].
proof. conseq rt_kernel_pkeenc_cost;rewrite /rt_concrete_kernel_prices /rtk_profile /rt_outer_frame /rt_outer_copy;smt(). qed.
lemma rt_outer_trit_call_cost :
 hoare[RTFixedWordChecks.trit:true ==>
 0<=res.`2+rt_outer_frame 1 0<=(rt_concrete_kernel_prices 0).`rtk_trit].
proof. conseq rt_fixed_trit_bound_cost;rewrite /rt_concrete_kernel_prices /rtk_profile /rt_outer_frame /rt_outer_copy;smt(). qed.
lemma rt_outer_poly_compare_call_cost :
 hoare[RTPrimitive.word_equal:true ==>
 0<=res.`2+rt_outer_frame 2 0<=(rt_concrete_kernel_prices 0).`rtk_poly_compare].
proof. conseq rt_primitive_word_equal_steps;rewrite /rt_concrete_kernel_prices /rtk_profile /rt_word_compare_steps /rt_outer_frame /rt_outer_copy;smt(). qed.
lemma rt_outer_cipher_compare_call_cost :
 hoare[RTPrimitive.cipher:true ==>
 0<=res.`2+rt_outer_frame 2 0<=(rt_concrete_kernel_prices 0).`rtk_cipher_compare].
proof. conseq rt_primitive_cipher_steps;rewrite /rt_concrete_kernel_prices /rtk_profile /rt_byte_compare_steps /rt_outer_frame /rt_outer_copy;smt(). qed.
lemma rt_outer_psi_call_cost :
 hoare[RTPsiSampler.measure:true ==>
 0<=res.`2+res.`3+rt_outer_frame 0 768<=(rt_concrete_kernel_prices 0).`rtk_psi_draw].
proof. conseq rt_psi_sampler_measure_cost;rewrite /rt_concrete_kernel_prices /rtk_profile /rt_outer_frame /rt_outer_copy /rt_fixed_cbd_bound;smt(). qed.
lemma rt_outer_poly_compare_projection :
 equiv[RTPrimitive.word_equal ~ RTPolyEqual.run: ={x,y} ==>res{1}.`1=res{2}].
proof.
 exists* x{1},y{1};elim*=>x0 y0;proc*.
 ecall{1}(rt_primitive_word_equal_correct x0 y0).
 ecall{2}(rt_poly_equal_correct x0 y0);auto.
qed.

(* These fixed subtotals are expanded statement-by-statement in the
   source-calibration manifest. All possible branches are reserved once.
   This is conservative even when the unit guard rejects before B runs.
   Counter/profile updates, reset_cost, metrics and charge_extract erase
   to no executable work. The calls which compute actual answers remain.
   Setup/RTTranscript and CostExtract bodies are priced by the phase
   certificate, including setup when Q=0. The RTExtract wrapper's own
   argument/result copies are included here in addition to that body. *)
op rt_outer_top_di = rt_outer_copy 768+rt_outer_frame 1 0+2.
op rt_outer_top_do = rt_outer_copy 768+rt_outer_frame 1 0+2.
op rt_outer_top_co = rt_outer_copy(2*768)+rt_outer_frame 2 768+2+rt_outer_copy 768.
op rt_outer_word_inj = rt_outer_copy 768+1+1+rt_outer_frame 1 (4*768)+rt_outer_frame 2 0+2+1.
op rt_outer_word_ow = rt_outer_copy 768+1+1+rt_outer_frame 1 0+2+1.
op rt_outer_word_rlwe = rt_outer_copy(2*768)+1+rt_outer_zero_call 768+
 rt_outer_frame 2 768+1+2+(2+rt_outer_copy 768)+(1+rt_outer_copy 768).
op rt_outer_inj_check = rt_outer_copy(1152+4*768)+1+4+4+7+4+
 2*(2+rt_outer_copy 1152)+2+1.
op rt_outer_encrypt = rt_outer_copy(1152+2*768)+3+rt_outer_zero_call 1152+1+rt_outer_copy 1152.
op rt_outer_ow_kernel = rt_outer_copy 1152+rt_outer_frame 3 1152+
 rt_outer_frame 2 768+1+1.
op rt_outer_aux_inj = rt_outer_copy 1152+rt_outer_frame 1 0+
 rt_outer_frame 1 (4*768)+1+rt_outer_copy(4*768).
op rt_outer_aux_ow = rt_outer_copy(2*1152)+rt_outer_frame 1 0+
 rt_outer_frame 2 768+1+rt_outer_copy 768.
op rt_outer_measured_inj_run = rt_outer_copy 1152+rt_outer_frame 1 (4*768)+2+rt_outer_copy(4*768).
op rt_outer_measured_inj = rt_outer_copy 1152+rt_outer_frame 3 1152+
 rt_outer_frame 2 0+1+
 rt_outer_frame 4 (2*768)+2+1+rt_outer_copy 768+
 (2+3+4+1+rt_outer_copy(4*768))+1+rt_outer_copy(4*768).
op rt_outer_measured_ow = rt_outer_copy(2*1152)+rt_outer_frame 2 0+
 rt_outer_frame 4 (2*768)+1+1+rt_outer_copy 768+2+rt_outer_zero_call 768.
op rt_outer_extract_wrapper = rt_outer_copy(2*1152+768)+rt_outer_frame 4 (2*768)+2+rt_outer_copy(2*768).

op rt_outer_di_fixed = rt_outer_top_di+rt_outer_word_inj+rt_outer_inj_check+
 rt_outer_aux_inj+rt_outer_measured_inj_run+rt_outer_measured_inj+
 rt_outer_extract_wrapper+rt_outer_encrypt.
op rt_outer_do_fixed = rt_outer_top_do+rt_outer_word_ow+rt_outer_ow_kernel+
 rt_outer_aux_ow+rt_outer_measured_ow+rt_outer_extract_wrapper+rt_outer_encrypt.
op rt_outer_co_fixed = rt_outer_top_co+rt_outer_word_rlwe+
 rt_outer_aux_ow+rt_outer_measured_ow+rt_outer_extract_wrapper.
op rt_outer_di_charge tA k=rt_outer_di_fixed+rtk_charge(rt_concrete_kernel_prices tA)k.
op rt_outer_do_charge tA k=rt_outer_do_fixed+rtk_charge(rt_concrete_kernel_prices tA)k.
op rt_outer_co_charge tA k=rt_outer_co_fixed+rtk_charge(rt_concrete_kernel_prices tA)k.
op rt_outer_di_bound tA=rt_outer_di_charge tA rt_di_kernel_bound.
op rt_outer_do_bound tA=rt_outer_do_charge tA rt_do_kernel_bound.
op rt_outer_co_bound tA=rt_outer_co_charge tA rt_co_kernel_bound.

lemma rt_concrete_kernel_prices_ok tA : 0<=tA=>rtk_prices_ok(rt_concrete_kernel_prices tA).
proof. rewrite /rtk_prices_ok /rt_concrete_kernel_prices /rtk_profile /rt_outer_frame /rt_outer_copy;smt(). qed.
lemma rt_outer_di_cap tA k : 0<=tA=>rtk_le k rt_di_kernel_bound=>
 rt_outer_di_charge tA k<=rt_outer_di_bound tA.
proof.
 move=>ht hk;have hb:=rtk_charge_bound (rt_concrete_kernel_prices tA) k rt_di_kernel_bound
 (rt_concrete_kernel_prices_ok tA ht) hk.
 rewrite /rt_outer_di_charge /rt_outer_di_bound;smt().
qed.
lemma rt_outer_do_cap tA k : 0<=tA=>rtk_le k rt_do_kernel_bound=>
 rt_outer_do_charge tA k<=rt_outer_do_bound tA.
proof.
 move=>ht hk;have hb:=rtk_charge_bound (rt_concrete_kernel_prices tA) k rt_do_kernel_bound
 (rt_concrete_kernel_prices_ok tA ht) hk.
 rewrite /rt_outer_do_charge /rt_outer_do_bound;smt().
qed.
lemma rt_outer_co_cap tA k : 0<=tA=>rtk_le k rt_co_kernel_bound=>
 rt_outer_co_charge tA k<=rt_outer_co_bound tA.
proof.
 move=>ht hk;have hb:=rtk_charge_bound (rt_concrete_kernel_prices tA) k rt_co_kernel_bound
 (rt_concrete_kernel_prices_ok tA ht) hk.
 rewrite /rt_outer_co_charge /rt_outer_co_bound;smt().
qed.

(* The complete DI profile already contains its two inner psi samples
   and challenge encryption. No additional copy of those counts is added. *)
lemma rt_outer_word_di_bound
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) p0 tA :
 0<=tA=>hoare[RTWord_DI(S,A).measure:h=ow_coeff_words p0 ==>
 rt_outer_di_charge tA res.`3<=rt_outer_di_bound tA].
proof. move=>ht;conseq(rt_word_di_kernel_profile S A p0);smt(rt_outer_di_cap). qed.
lemma rt_outer_word_do_bound
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) p0 tA :
 0<=tA=>hoare[RTWord_DO(S,A).measure:h=ow_coeff_words p0 ==>
 rt_outer_do_charge tA res.`3<=rt_outer_do_bound tA].
proof. move=>ht;conseq(rt_word_do_kernel_profile S A p0);smt(rt_outer_do_cap). qed.
lemma rt_outer_word_co_bound
 (S<:RTHistory {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory})
 (A<:CCAExtendedAdversary {-S,-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-SecGHistory}) p0 q0 tA :
 0<=tA=>hoare[RTWord_CO(S,A).measure:a=ow_coeff_words p0 /\ b=ow_coeff_words q0 ==>
 rt_outer_co_charge tA res.`3<=rt_outer_co_bound tA].
proof. move=>ht;conseq(rt_word_co_kernel_profile S A p0 q0);smt(rt_outer_co_cap). qed.


lemma rt_concrete_kernel_price_values tA :
 rt_concrete_kernel_prices tA = rtk_profile
 21511 4724206 1659715 9956046 3517914 14600 12297 20745 44942 tA.
proof. rewrite /rt_concrete_kernel_prices /rtk_profile /rt_outer_frame /rt_outer_copy;smt(). qed.
lemma rt_outer_fixed_values :
 rt_outer_di_fixed=154473 /\ rt_outer_do_fixed=94152 /\ rt_outer_co_fixed=84541.
proof.
 by rewrite /rt_outer_di_fixed /rt_outer_do_fixed /rt_outer_co_fixed
 /rt_outer_top_di /rt_outer_top_do /rt_outer_top_co
 /rt_outer_word_inj /rt_outer_word_ow /rt_outer_word_rlwe
 /rt_outer_inj_check /rt_outer_encrypt /rt_outer_ow_kernel
 /rt_outer_aux_inj /rt_outer_aux_ow /rt_outer_measured_inj_run
 /rt_outer_measured_inj /rt_outer_measured_ow /rt_outer_extract_wrapper
 /rt_outer_zero_call /rt_outer_zero_steps /rt_outer_frame /rt_outer_copy.
qed.
lemma rt_outer_bound_values tA :
 rt_outer_di_bound tA=tA+17307270 /\
 rt_outer_do_bound tA=tA+10119679 /\
 rt_outer_co_bound tA=tA+18084223.
proof.
 have hf:=rt_outer_fixed_values.
 rewrite /rt_outer_di_bound /rt_outer_do_bound /rt_outer_co_bound
 /rt_outer_di_charge /rt_outer_do_charge /rt_outer_co_charge
 rt_concrete_kernel_price_values /rtk_charge
 /rt_di_kernel_bound /rt_do_kernel_bound /rt_co_kernel_bound /rtk_profile /=;smt().
qed.
