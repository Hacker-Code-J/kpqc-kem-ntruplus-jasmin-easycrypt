require import AllCore Bool IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord.
require import Array192.
require import NTRUPlus768UniformOrbitBound NTRUPlus768AcceptanceInput.
require import NTRUPlus768AcceptanceRoots NTRUPlus768AcceptanceSlices.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768AcceptanceAlgebra NTRUPlus768AcceptanceHeadReduction.
import NTRUPoly.BigPoly.

op acceptance_last rho = nth 0 (slice_exponents rho) 4.
op acceptance_digit m p = if p=0 then m %% 32 else m %/ 32.
op acceptance_mask_bit rho m k =
 if 0<=k<8 then slice_bit (acceptance_digit m (k %% 2)) (k %/ 2)
 else if k=2*acceptance_last rho then slice_bit (acceptance_digit m 0) 4
 else if k=2*acceptance_last rho+1 then slice_bit (acceptance_digit m 1) 4
 else false.
op acceptance_masks rho m : W8.t Array192.t =
 Array192.init (fun i=>if 0<=i<2
   then W8.init(fun j=>acceptance_mask_bit rho m (8*i+j)) else W8.zero).
op acceptance_position rho t p = 2*nth 0 (slice_exponents rho) t+p.
op acceptance_pack5 (bits:int -> bool) =
 b2i(bits 0)+2*b2i(bits 1)+4*b2i(bits 2)+8*b2i(bits 3)+16*b2i(bits 4).
op acceptance_postcode rho (buf:W8.t Array192.t) p =
 acceptance_pack5 (fun t=>
  (buf.[acceptance_position rho t p %/ 8]).[acceptance_position rho t p %% 8]).

lemma acceptance_last_range rho : acceptance_last rho=4 \/ acceptance_last rho=5.
proof. rewrite /acceptance_last /slice_exponents /=; smt(). qed.
lemma acceptance_digit_range m p : 0<=m<1024 => 0<=p<2 =>
 0<=acceptance_digit m p<32.
proof. rewrite /acceptance_digit; smt(). qed.
lemma acceptance_digits_determine i j : 0<=i<1024 => 0<=j<1024 =>
 acceptance_digit i 0=acceptance_digit j 0 =>
 acceptance_digit i 1=acceptance_digit j 1 => i=j.
proof. rewrite /acceptance_digit /=; smt(divz_eq). qed.

lemma acceptance_mask_tail rho m k : 2<=k<192 =>
 (acceptance_masks rho m).[k]=W8.zero.
proof. move=>hk; rewrite /acceptance_masks Array192.initiE 1:/#; smt(). qed.
lemma acceptance_xor_tail rho m buf :
 acceptance_same_tail (uniform192_xor (acceptance_masks rho m) buf) buf.
proof.
 move=>k hk; rewrite uniform192_xor_get 1:/# acceptance_mask_tail 1:hk.
 exact (W8.xorw0 buf.[k]).
qed.
lemma acceptance_mask_head rho m k : 0<=k<16 =>
 ((acceptance_masks rho m).[k %/ 8]).[k %% 8]=acceptance_mask_bit rho m k.
proof.
 move=>hk; rewrite /acceptance_masks Array192.initiE 1:/#.
 rewrite /= ifT 1:/# W8.initiE 1:/# /=.
 have ->: 8*(k %/ 8)+k %% 8=k by smt(divz_eq).
 done.
qed.
lemma acceptance_xor_head rho m buf k : 0<=k<16 =>
 ((uniform192_xor (acceptance_masks rho m) buf).[k %/ 8]).[k %% 8]=
 (buf.[k %/ 8]).[k %% 8] ^^ acceptance_mask_bit rho m k.
proof.
 move=>hk; rewrite uniform192_xor_get 1:/# W8.xorwE acceptance_mask_head 1:hk.
 done.
qed.

lemma acceptance_position_range rho t p : 0<=t<5 => 0<=p<2 =>
 0<=acceptance_position rho t p<12.
proof.
 move=>ht hp; have h:=slice_exponent_range rho t ht.
 rewrite /acceptance_position; smt().
qed.
lemma acceptance_mask_selected rho m t p : 0<=t<5 => 0<=p<2 =>
 acceptance_mask_bit rho m (acceptance_position rho t p)=slice_bit (acceptance_digit m p) t.
proof.
 move=>ht hp; rewrite /acceptance_mask_bit /acceptance_position /acceptance_last /slice_exponents /=.
 smt().
qed.

lemma acceptance_pack5_range bits : 0<=acceptance_pack5 bits<32.
proof. rewrite /acceptance_pack5 /b2i; smt(). qed.
lemma acceptance_pack5_bit bits t : 0<=t<5 =>
 slice_bit (acceptance_pack5 bits) t=bits t.
proof.
 move=>ht.
 have ht':t=0 \/ t=1 \/ t=2 \/ t=3 \/ t=4 by smt().
 case ht'=>[->|[->|[->|[->|->]]]];
  rewrite /slice_bit /acceptance_pack5 /b2i /=; smt().
qed.
lemma acceptance_postcode_range rho buf p :
 0<=acceptance_postcode rho buf p<32.
proof. rewrite /acceptance_postcode; exact (acceptance_pack5_range _). qed.
lemma acceptance_postcode_bit rho buf t p : 0<=t<5 =>
 slice_bit (acceptance_postcode rho buf p) t=
 (buf.[acceptance_position rho t p %/ 8]).[acceptance_position rho t p %% 8].
proof. move=>ht; rewrite /acceptance_postcode; exact (acceptance_pack5_bit _ t ht). qed.

lemma acceptance_postcode_xor rho m buf t p : 0<=t<5 => 0<=p<2 =>
 slice_bit (acceptance_postcode rho (uniform192_xor (acceptance_masks rho m) buf) p) t=
 (buf.[acceptance_position rho t p %/ 8]).[acceptance_position rho t p %% 8] ^^
 slice_bit (acceptance_digit m p) t.
proof.
 move=>ht hp; rewrite acceptance_postcode_bit 1:ht acceptance_xor_head.
 + have h:=acceptance_position_range rho t p ht hp; smt().
 by rewrite acceptance_mask_selected.
qed.

lemma acceptance_postcodes_determine rho i j buf : 0<=i<1024 => 0<=j<1024 =>
 (forall p, 0<=p<2 =>
  acceptance_postcode rho (uniform192_xor(acceptance_masks rho i)buf) p=
  acceptance_postcode rho (uniform192_xor(acceptance_masks rho j)buf) p) => i=j.
proof.
 move=>hi hj he.
 have hd:forall p,0<=p<2=>acceptance_digit i p=acceptance_digit j p.
 + move=>p hp.
   have hb:forall t,0<=t<5=>slice_bit(acceptance_digit i p)t=slice_bit(acceptance_digit j p)t.
   - move=>t ht.
     have heq:=he p hp.
     have h:=congr1 (fun n=>slice_bit n t) _ _ heq.
     rewrite /= in h.
     rewrite (acceptance_postcode_xor rho i buf t p ht hp)
       (acceptance_postcode_xor rho j buf t p ht hp) in h.
     smt().
   rewrite -(slice_bits_reconstruction (acceptance_digit i p) (acceptance_digit_range i p hi hp)).
   rewrite -(slice_bits_reconstruction (acceptance_digit j p) (acceptance_digit_range j p hj hp)).
   by rewrite !hb.
 exact (acceptance_digits_determine i j hi hj (hd 0 _) (hd 1 _)).
qed.

lemma acceptance_xor_pair_tail rho i j buf :
 acceptance_same_tail (uniform192_xor(acceptance_masks rho i)buf)
   (uniform192_xor(acceptance_masks rho j)buf).
proof.
 move=>k hk; rewrite (acceptance_xor_tail rho i buf k hk)
   (acceptance_xor_tail rho j buf k hk).
 done.
qed.

lemma acceptance_xor_unselected rho i j buf k :
 8<=k<16 => k<>2*nth 0 (slice_exponents rho) 4 =>
 k<>2*nth 0 (slice_exponents rho) 4+1 =>
 acceptance_head_bit (uniform192_xor(acceptance_masks rho i)buf) k=
 acceptance_head_bit (uniform192_xor(acceptance_masks rho j)buf) k.
proof.
 move=>hk he ho; rewrite /acceptance_head_bit !acceptance_xor_head ~-1:/#.
 rewrite /acceptance_mask_bit /acceptance_last.
 rewrite !ifF ~-1:/#.
 done.
qed.

lemma acceptance_lift_mod x : lift_int(x %% 3457)=lift_int x.
proof. by apply eq_sym; exact (CycloFq.incyclocoeff_mod x). qed.

lemma acceptance_field_pow rho n : 0<=n =>
 CycloFq.incyclocoeff(rho^n)=CycloFq.exp(CycloFq.incyclocoeff rho)n.
proof. move=>hn; by rewrite CycloFq.incyclocoeff_exp ifT. qed.

lemma acceptance_selected_weight_code rho buf p :
 acceptance_selected_weight rho buf p=
 lift_int(slice_weighted_sum rho (acceptance_postcode rho buf p)).
proof.
 rewrite /acceptance_selected_weight /slice_weighted_sum acceptance_lift_mod.
 rewrite !acceptance_postcode_bit ~-1:/#.
 rewrite /acceptance_head_bit /acceptance_position.
 have he:=slice_exponent_range rho 4 _; first smt().
 rewrite /lift_int !CycloFq.incyclocoeffD !CycloFq.incyclocoeffM
   !acceptance_field_pow ~-1:/#.
 by rewrite /slice_exponents /=.
qed.

lemma acceptance_bad_translates_disjoint is_f j :
 0<=j<384 => forall i k buf,
 0<=i<1024 => 0<=k<1024 =>
 quadratic_divides (lift_int(acceptance_root j))
  (acceptance_input is_f (uniform192_xor(acceptance_masks(acceptance_root j)i)buf)) =>
 quadratic_divides (lift_int(acceptance_root j))
  (acceptance_input is_f (uniform192_xor(acceptance_masks(acceptance_root j)k)buf)) => i=k.
proof.
 move=>hj i k buf hi hk hdi hdk.
 apply(acceptance_postcodes_determine (acceptance_root j) i k buf hi hk).
 move=>p hp.
 have hs:=acceptance_head_divisors_equal is_f (acceptance_root j)
   (uniform192_xor(acceptance_masks(acceptance_root j)i)buf)
   (uniform192_xor(acceptance_masks(acceptance_root j)k)buf)
   (acceptance_xor_pair_tail (acceptance_root j) i k buf) _ hdi hdk p hp.
 + move=>z hz he ho; exact(acceptance_xor_unselected (acceptance_root j) i k buf z hz he ho).
 rewrite !acceptance_selected_weight_code in hs.
 exact(acceptance_slice_field_injective j _ _ hj (acceptance_postcode_range _ _ _)
   (acceptance_postcode_range _ _ _) hs).
qed.
