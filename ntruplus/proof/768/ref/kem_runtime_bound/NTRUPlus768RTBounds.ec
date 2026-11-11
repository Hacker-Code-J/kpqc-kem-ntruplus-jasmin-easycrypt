require import AllCore StdOrder.
require import NTRUPlus768RTModel NTRUPlus768RTKernelTypes.
import IntOrder.

(* These are accounting inequalities. Each price must subsequently be
   instantiated with a body-calibrated primitive-step contract. An
   arbitrary price assignment is not a running-time theorem. *)
type rt_phase_prices = {
 pc_call:int; pc_input:int; pc_visit:int; pc_compare:int;
 pc_cons:int; pc_encrypt:int; pc_candidate:int; pc_extract_init:int;
}.
op rt_prices_ok c =
 0<=c.`pc_call /\ 0<=c.`pc_input /\ 0<=c.`pc_visit /\ 0<=c.`pc_compare /\
 0<=c.`pc_cons /\ 0<=c.`pc_encrypt /\ 0<=c.`pc_candidate /\ 0<=c.`pc_extract_init.
op rt_phase_charge c (p:rt_profile) =
 c.`pc_call*p.`rp_q+c.`pc_input*p.`rp_b+c.`pc_visit*rt_visits p+
 c.`pc_compare*rt_comparisons p+c.`pc_cons*(p.`rp_alloc+rt_g_length p)+
 c.`pc_encrypt*p.`rp_enc+c.`pc_candidate*p.`rp_xvisits+c.`pc_extract_init*p.`rp_xcalls.
op rt_phase_envelope c h d g q b =
 c.`pc_call*q+c.`pc_input*b+c.`pc_visit*(h*(h-1)+g+2*d*h)+
 c.`pc_compare*(64*h*(h-1)+1152*d+1184*d*h)+
 c.`pc_cons*(h*h+g+d*h)+c.`pc_encrypt*(d*h)+
 c.`pc_candidate*(g+d*h)+c.`pc_extract_init.
op rt_q_envelope c q b =
 c.`pc_call*q+c.`pc_input*b+c.`pc_visit*(3*q*q+q)+
 c.`pc_compare*(1248*q*q+1152*q)+c.`pc_cons*(2*q*q+q)+
 c.`pc_encrypt*(q*q)+c.`pc_candidate*(q*q+q)+c.`pc_extract_init.

lemma rt_product_upper a b q : 0<=a<=q=>0<=b<=q=>a*b<=q*q.
proof.
 move=>ha hb;have x:=rt_mul_mono a b q _ _;have y:=rt_mul_mono q a q _ _;smt().
qed.
lemma rt_aggregate_resources p : rt_cost_ok p=>p.`rp_xcalls<=1=>
 0<=p.`rp_alloc+rt_g_length p<=p.`rp_h*p.`rp_h+p.`rp_g+p.`rp_d*p.`rp_h /\
 0<=p.`rp_enc<=p.`rp_d*p.`rp_h /\
 0<=p.`rp_xvisits<=p.`rp_g+p.`rp_d*p.`rp_h /\
 0<=rt_visits p<=p.`rp_h*(p.`rp_h-1)+p.`rp_g+2*p.`rp_d*p.`rp_h /\
 0<=rt_comparisons p<=64*p.`rp_h*(p.`rp_h-1)+1152*p.`rp_d+1184*p.`rp_d*p.`rp_h.
proof.
 move=>hp hx;have he:=rt_encryption_bound p hp;have hv:=rt_one_extraction_bound p hp hx.
 have hc:=rt_comparison_bound p hp.
 have hd:0<=p.`rp_d by move:hp;rewrite /rt_cost_ok /rt_nonnegative;smt().
 have hs:p.`rp_size<=p.`rp_h by move:hp;rewrite /rt_cost_ok;smt().
 have hm:=rt_mul_mono p.`rp_d p.`rp_size p.`rp_h hd hs.
 move:hp;rewrite /rt_cost_ok /rt_nonnegative /rt_g_length;smt().
qed.
lemma rt_phase_charge_bound c p : rt_prices_ok c=>rt_cost_ok p=>p.`rp_xcalls<=1=>
 rt_phase_charge c p<=rt_phase_envelope c p.`rp_h p.`rp_d p.`rp_g p.`rp_q p.`rp_b.
proof.
 move=>hc hp hx;have hr:=rt_aggregate_resources p hp hx.
 have hn:=rt_cost_nonnegative p hp.
 have hv:=rt_mul_mono c.`pc_visit (rt_visits p) (p.`rp_h*(p.`rp_h-1)+p.`rp_g+2*p.`rp_d*p.`rp_h).
 have hb:=rt_mul_mono c.`pc_compare (rt_comparisons p) (64*p.`rp_h*(p.`rp_h-1)+1152*p.`rp_d+1184*p.`rp_d*p.`rp_h).
 have ha:=rt_mul_mono c.`pc_cons (p.`rp_alloc+rt_g_length p) (p.`rp_h*p.`rp_h+p.`rp_g+p.`rp_d*p.`rp_h).
 have he:=rt_mul_mono c.`pc_encrypt p.`rp_enc (p.`rp_d*p.`rp_h).
 have hext:=rt_mul_mono c.`pc_candidate p.`rp_xvisits (p.`rp_g+p.`rp_d*p.`rp_h).
 have hi:=rt_mul_mono c.`pc_extract_init p.`rp_xcalls 1.
 move:hc;rewrite /rt_prices_ok /rt_phase_charge /rt_phase_envelope;smt().
qed.
lemma rt_phase_q_bound c p : rt_prices_ok c=>rt_cost_ok p=>p.`rp_xcalls<=1=>
 p.`rp_h+p.`rp_d+p.`rp_g<=p.`rp_q=>
 rt_phase_charge c p<=rt_q_envelope c p.`rp_q p.`rp_b.
proof.
 move=>hc hp hx hq;have hphase:=rt_phase_charge_bound c p hc hp hx.
 have hn:=rt_cost_nonnegative p hp.
 have hh:0<=p.`rp_h<=p.`rp_q by move:hn;rewrite /rt_nonnegative;smt().
 have hd:0<=p.`rp_d<=p.`rp_q by move:hn;rewrite /rt_nonnegative;smt().
 have hg:0<=p.`rp_g<=p.`rp_q by move:hn;rewrite /rt_nonnegative;smt().
 have hhh:=rt_product_upper p.`rp_h p.`rp_h p.`rp_q hh hh.
 have hdh:=rt_product_upper p.`rp_d p.`rp_h p.`rp_q hd hh.
 have hv:=rt_mul_mono c.`pc_visit (p.`rp_h*(p.`rp_h-1)+p.`rp_g+2*p.`rp_d*p.`rp_h) (3*p.`rp_q*p.`rp_q+p.`rp_q).
 have hb:=rt_mul_mono c.`pc_compare (64*p.`rp_h*(p.`rp_h-1)+1152*p.`rp_d+1184*p.`rp_d*p.`rp_h) (1248*p.`rp_q*p.`rp_q+1152*p.`rp_q).
 have ha:=rt_mul_mono c.`pc_cons (p.`rp_h*p.`rp_h+p.`rp_g+p.`rp_d*p.`rp_h) (2*p.`rp_q*p.`rp_q+p.`rp_q).
 have he:=rt_mul_mono c.`pc_encrypt (p.`rp_d*p.`rp_h) (p.`rp_q*p.`rp_q).
 have hext:=rt_mul_mono c.`pc_candidate (p.`rp_g+p.`rp_d*p.`rp_h) (p.`rp_q*p.`rp_q+p.`rp_q).
 move:hc hphase;rewrite /rt_prices_ok /rt_phase_envelope /rt_q_envelope;smt().
qed.

op rtk_prices_ok c =
 0<=c.`rtk_scale /\ 0<=c.`rtk_unit /\ 0<=c.`rtk_encode /\ 0<=c.`rtk_recover /\
 0<=c.`rtk_encrypt /\ 0<=c.`rtk_trit /\ 0<=c.`rtk_poly_compare /\ 0<=c.`rtk_cipher_compare /\
 0<=c.`rtk_psi_draw /\ 0<=c.`rtk_adversary.
op rtk_charge c k =
 c.`rtk_scale*k.`rtk_scale+c.`rtk_unit*k.`rtk_unit+c.`rtk_encode*k.`rtk_encode+
 c.`rtk_recover*k.`rtk_recover+c.`rtk_encrypt*k.`rtk_encrypt+c.`rtk_trit*k.`rtk_trit+
 c.`rtk_poly_compare*k.`rtk_poly_compare+c.`rtk_cipher_compare*k.`rtk_cipher_compare+
 c.`rtk_psi_draw*k.`rtk_psi_draw+c.`rtk_adversary*k.`rtk_adversary.
lemma rtk_charge_add c x y : rtk_charge c(rtk_add x y)=rtk_charge c x+rtk_charge c y.
proof. rewrite /rtk_charge /rtk_add /rtk_profile /=;ring. qed.
lemma rtk_charge_bound c x y : rtk_prices_ok c=>rtk_le x y=>rtk_charge c x<=rtk_charge c y.
proof.
 move=>hc hxy.
 have h1:=rt_mul_mono c.`rtk_scale x.`rtk_scale y.`rtk_scale.
 have h2:=rt_mul_mono c.`rtk_unit x.`rtk_unit y.`rtk_unit.
 have h3:=rt_mul_mono c.`rtk_encode x.`rtk_encode y.`rtk_encode.
 have h4:=rt_mul_mono c.`rtk_recover x.`rtk_recover y.`rtk_recover.
 have h5:=rt_mul_mono c.`rtk_encrypt x.`rtk_encrypt y.`rtk_encrypt.
 have h6:=rt_mul_mono c.`rtk_trit x.`rtk_trit y.`rtk_trit.
 have h7:=rt_mul_mono c.`rtk_poly_compare x.`rtk_poly_compare y.`rtk_poly_compare.
 have h8:=rt_mul_mono c.`rtk_cipher_compare x.`rtk_cipher_compare y.`rtk_cipher_compare.
 have h9:=rt_mul_mono c.`rtk_psi_draw x.`rtk_psi_draw y.`rtk_psi_draw.
 have h10:=rt_mul_mono c.`rtk_adversary x.`rtk_adversary y.`rtk_adversary.
 move:hc hxy;rewrite /rtk_prices_ok /rtk_le /rtk_charge;smt().
qed.
