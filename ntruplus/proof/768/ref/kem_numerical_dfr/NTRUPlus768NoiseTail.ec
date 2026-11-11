require import AllCore IntDiv Distr Finite List StdBigop StdOrder.
require import NTRUPlus768NoiseMGF NTRUPlus768UniformOrbitBound.
from Jasmin require import JWord JUtils.
require import Array192 Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768ValidKeyM1Recovery NTRUPlus768NumericalDFRModel.
require import NTRUPlus768NoiseDecomposition NTRUPlus768NoiseNoWrap.
require import NTRUPlus768CBDDistribution NTRUPlus768NoiseIndependentBlocks.
import RealOrder RField.

op noise_coefficient_bound = 2%r*noise_mgf_base^768/(2%r^576).
op noise_unconditional_bound = 1536%r*noise_mgf_base^768/(2%r^576).

lemma noise_chernoff ['a] (d:'a distr) (f:'a -> int) s t :
 is_finite(support d) => 0<=t =>
 mu d (fun x=>t<=s*f x) <= E d (fun x=>2%r^(s*f x))/(2%r^t).
proof.
 move=>hd ht.
 have hp:0%r<2%r^t by apply expr_gt0; smt().
 have hm:=in_ler_exp d (fun x=>if t<=s*f x then 2%r^t else 0%r)
   (fun x=>2%r^(s*f x)) _ _ _.
 + exact(hasE_finite d _ hd).
 + exact(hasE_finite d _ hd).
 + move=>x _; case(t<=s*f x)=>hx; rewrite hx /=.
   - apply ler_weexpn2l; smt().
   apply expr_ge0; smt().
 rewrite expC_cond in hm.
 rewrite ler_pdivl_mulr 1:hp; smt().
qed.

lemma noise_two_sided_chernoff ['a] (d:'a distr) (f:'a -> int) t :
 is_finite(support d) => 0<=t =>
 mu d (fun x=>t<=`|f x|) <=
  (E d (fun x=>2%r^(f x))+E d (fun x=>2%r^(-f x)))/(2%r^t).
proof.
 move=>hd ht.
 have hp:=noise_chernoff d f 1 t hd ht.
 have hn:=noise_chernoff d (fun x=> -f x) 1 t hd ht.
 rewrite /= in hp.
 rewrite /= in hn.
 have he:mu d (fun x=>t<=`|f x|)=
   mu d (predU (fun x=>t<=f x) (fun x=>t<= -f x)).
 + by apply mu_eq=>x; rewrite /predU IntOrder.ler_normr.
 rewrite he mu_or.
 have h0:=mu_bounded d (predI (fun x=>t<=f x) (fun x=>t<= -f x)).
 smt().
qed.

lemma independent_noise_tail ds :
 size ds=768 =>
 all (fun d=>is_finite(support d)) ds =>
 (forall d,d \in ds=>noise_mgf 1 d<=noise_mgf_base /\
   noise_mgf (-1) d<=noise_mgf_base) =>
 mu (djoin ds) (fun xs=>576<=`|noise_sum xs|)<=noise_coefficient_bound.
proof.
 move=>hs hf hm.
 have hK:0%r<=noise_mgf_base by rewrite /noise_mgf_base; smt().
 have hp:=independent_noise_mgf_bound ds 1 noise_mgf_base hK hf _.
 + move=>d hd; have h:=hm d hd; smt().
 have hn:=independent_noise_mgf_bound ds (-1) noise_mgf_base hK hf _.
 + move=>d hd; have h:=hm d hd; smt().
 have ht:=noise_two_sided_chernoff (djoin ds) noise_sum 576
   (noise_finite_djoin ds hf) _; first smt().
 rewrite hs /= in hp.
 rewrite hs /= in hn.
 rewrite (noise_exp_negate (djoin ds) noise_sum) in hn.
 have hd:0%r<2%r^576 by apply expr_gt0; smt().
 have hmom:E (djoin ds)(fun xs=>2%r^(noise_sum xs))+
   E (djoin ds)(fun xs=>2%r^(-noise_sum xs))<=2%r*noise_mgf_base^768 by smt().
 have hfrac:(E (djoin ds)(fun xs=>2%r^(noise_sum xs))+
   E (djoin ds)(fun xs=>2%r^(-noise_sum xs)))/(2%r^576)<=noise_coefficient_bound.
 + rewrite /noise_coefficient_bound.
   apply ler_wpmul2r; first by apply invr_ge0; smt().
   exact hmom.
 smt().
qed.

lemma noise_coefficient_union ['a] (d:'a distr) (events:int -> 'a -> bool) :
 (forall k,0<=k<768=>mu d (events k)<=noise_coefficient_bound) =>
 mu d (indexed_event_union 768 events)<=noise_unconditional_bound.
proof.
 move=>h; have hu:=indexed_event_union_bound d events 768 noise_coefficient_bound _ h;
  first smt().
 rewrite /noise_coefficient_bound in hu.
 rewrite /noise_unconditional_bound; smt().
qed.

(* Exact rational certificates; the displayed integers are checked by ring. *)
lemma noise_mgf_power32 : noise_mgf_base^32<423%r.
proof.
 have hn:1237%r^32=903296626158605961467439703296287963252726016770208499015798667856265305702956140893162013188305281%r by ring.
 have hd:1024%r^32=2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576%r by ring.
 rewrite /noise_mgf_base exprMn 1:// exprVn 1:// hn hd.
 smt().
qed.

lemma noise_integer_certificate : 1536%r*(423%r^24)<2%r^220.
proof.
 have hn:423%r^24=1076883733691680512058434177457060722708245165817023740515026241%r by ring.
 have hd:2%r^220=1684996666696914987166688442938726917102321526408785780068975640576%r by ring.
 rewrite hn hd; smt().
qed.

lemma noise_union_numerical : noise_unconditional_bound<1%r/(2%r^356).
proof.
 have hb:=noise_mgf_power32.
 have hn:0%r<=noise_mgf_base^32 by apply expr_ge0; rewrite /noise_mgf_base; smt().
 have hp:=ler_pexp 24 (noise_mgf_base^32) 423%r _ _; first 2 smt().
 have he:noise_mgf_base^768=(noise_mgf_base^32)^24.
 + exact(exprM noise_mgf_base 32 24).
 have hc:=noise_integer_certificate.
 have hu:1536%r*noise_mgf_base^768<2%r^220 by rewrite he; smt().
 have hd:0%r<2%r^576 by apply expr_gt0; smt().
 have h356:2%r^356<>0%r by rewrite expf_eq0; smt().
 have hsplit:2%r^576=(2%r^220)*(2%r^356).
 + exact(exprD_nneg 2%r 220 356 _ _); smt().
 rewrite /noise_unconditional_bound ltr_pdivr_mulr 1:hd.
 have hcanc:(1%r/(2%r^356))*(2%r^576)=2%r^220.
 + rewrite hsplit; field; smt().
 by rewrite hcanc.
qed.

lemma noise_accepted_numerical :
 (64%r/25%r)*noise_unconditional_bound<1%r/(2%r^354).
proof.
 have h:=noise_union_numerical.
 have hp:0%r<2%r^354 by apply expr_gt0; smt().
 have he:2%r^356=4%r*(2%r^354).
 + rewrite (_:356=2+354) 1:// exprD_nneg 1,2://; ring.
 move:h; rewrite he=>h; smt().
qed.

op noise_kind_at k i = noise_block_kind k (i %% 384).
op noise_quad_sum k (qs:cbd_quad list) =
 noise_sum(mapi(fun i q=>noise_kind_value(noise_kind_at k i)q)qs).
op noise_actual_sum k (bs:four_buffers) =
 (sampled_m1_noise bs.`1.`1 bs.`1.`2
   (poly_cbd1_spec bs.`2.`1) (poly_cbd1_spec bs.`2.`2)).[k].
op noise_coefficient_distrs k =
 map(fun i=>noise_kind_distr(noise_kind_at k i))(range 0 768).

lemma noise_cbd_coeff buf i : 0<=i<768 =>
 (integer_coefficients(poly_cbd1_spec buf)).[i]=poly_cbd1_coeff_int buf i.
proof. move=>hi; by rewrite integer_coefficients_get 1:hi poly_cbd1_spec_coeff 1:hi. qed.

lemma noise_block_values_nth a b k i : 0<=i<384 =>
 nth 0 (noise_block_values a b k) i=
 noise_block k i a.[i] a.[i+384] b.[noise_partner k i] b.[noise_partner k i+384].
proof.
 move=>hi; rewrite /noise_block_values (nth_map 0).
 + rewrite size_range; smt().
 by rewrite nth_range.
qed.

lemma noise_second_half_mod i : 384<=i<768 => i %%384=i-384.
proof.
 move=>hi.
 have he:=divz_eq i 384.
 have hr:=modz_cmp i 384 _; first smt().
 smt().
qed.

lemma noise_quad_values k (bs:four_buffers) :
 mapi(fun i q=>noise_kind_value(noise_kind_at k i)q)
   (cbd_four_blocks(noise_partner k)bs)=
 noise_block_values (integer_coefficients(poly_cbd1_spec bs.`1.`2))
   (integer_coefficients(poly_cbd1_spec bs.`2.`1)) k ++
 noise_block_values (integer_coefficients(poly_cbd1_spec bs.`2.`2))
   (integer_coefficients(poly_cbd1_spec bs.`1.`1)) k.
proof.
 apply(eq_from_nth 0).
 + by rewrite size_mapi /cbd_four_blocks /cbd_pair_blocks size_cat !size_mkseq
    size_cat !noise_block_values_size.
 move=>i hi.
 have hib:0<=i<768 by move:hi; rewrite size_mapi /cbd_four_blocks /cbd_pair_blocks
   size_cat !size_mkseq; smt().
 rewrite (nth_mapi ((0,0),(0,0))); first by move:hi; rewrite size_mapi.
 rewrite /= /cbd_four_blocks /= !nth_cat /cbd_pair_blocks /=
   !size_mkseq ?noise_block_values_size /max /=.
 case(i<384)=>hic.
 + rewrite /= nth_mkseq 1:/# noise_block_values_nth 1:/#.
   rewrite /noise_kind_at modz_small 1:/# /= /noise_kind_value noise_block_kindE.
   have hp:=noise_partner_range k i.
   by rewrite !noise_cbd_coeff ~-1:/#.
 rewrite /= nth_mkseq 1:/# noise_block_values_nth 1:/#.
 have him:=noise_second_half_mod i _; first smt().
 rewrite /noise_kind_at him /= /noise_kind_value noise_block_kindE.
 have hp:=noise_partner_range k (i-384).
 by rewrite !noise_cbd_coeff ~-1:/#.
qed.

lemma noise_actual_as_quad_sum k bs : 0<=k<768 =>
 noise_actual_sum k bs=noise_quad_sum k (cbd_four_blocks(noise_partner k)bs).
proof.
 move=>hk; rewrite /noise_actual_sum sampled_noise_blocks 1:hk
  !noise_product_blocks_sumz /noise_quad_sum noise_quad_values noise_sumE
  !Bigint.sumzE Bigint.BIA.big_cat.
 done.
qed.

lemma noise_actual_coefficient_law k : 0<=k<768 =>
 dmap raw_four_law (noise_actual_sum k)=dmap(djoin(noise_coefficient_distrs k))noise_sum.
proof.
 move=>hk.
 have he:noise_actual_sum k=noise_quad_sum k \o cbd_four_blocks(noise_partner k).
 + apply fun_ext=>bs; exact(noise_actual_as_quad_sum k bs hk).
 rewrite he -dmap_comp /raw_four_law cbd_four_blocks_uniform.
 + exact(noise_partner_injective k).
 + move=>i hi; exact(noise_partner_range k i).
 rewrite /noise_quad_sum (independent_blocks_observation dcbd_quad
   (fun i q=>noise_kind_value(noise_kind_at k i)q) noise_sum 768) 1://.
 by rewrite /noise_coefficient_distrs /noise_kind_distr.
qed.

lemma noise_coefficient_distrs_size k : size(noise_coefficient_distrs k)=768.
proof. by rewrite /noise_coefficient_distrs size_map size_range. qed.

lemma noise_actual_coefficient_tail k : 0<=k<768 =>
 mu raw_four_law (fun bs=>576<=`|noise_actual_sum k bs|)<=noise_coefficient_bound.
proof.
 move=>hk.
 have hl:=noise_actual_coefficient_law k hk.
 have hm:=congr1 (fun d:int distr=>mu d(fun x=>576<=`|x|)) _ _ hl.
 rewrite /= !dmapE /(\o) in hm.
 rewrite hm.
 apply independent_noise_tail; first exact(noise_coefficient_distrs_size k).
 + rewrite /noise_coefficient_distrs all_map allP=>i hi /=; exact(noise_kind_finite _).
 move=>d; rewrite /noise_coefficient_distrs; move/mapP=>[i [hi ->]].
 exact(noise_kind_mgf_bound _).
qed.

lemma noise_raw_bad_covered bs : four_buffers_bad bs =>
 indexed_event_union 768 (fun k bs=>576<=`|noise_actual_sum k bs|) bs.
proof.
 rewrite four_buffers_badE dfr_badE=>hbad.
 have hm:forall k,0<=k<768=> -1<=coeff(poly_cbd1_spec bs.`2.`2).[k]<=1.
 + move=>k hk; rewrite poly_cbd1_spec_coeff 1:hk.
   exact(poly_cbd1_coeff_int_range bs.`2.`2 k hk).
 have [k [hk hn]]:=no_wrap_violation_noise576 bs.`1.`1 bs.`1.`2
   (poly_cbd1_spec bs.`2.`1)(poly_cbd1_spec bs.`2.`2) hm hbad.
 rewrite /indexed_event_union; exists k; split; first exact hk.
 exact hn.
qed.

lemma raw_four_bad_bound : mu raw_four_law four_buffers_bad<=noise_unconditional_bound.
proof.
 have hs:mu raw_four_law four_buffers_bad<=
   mu raw_four_law (indexed_event_union 768 (fun k bs=>576<=`|noise_actual_sum k bs|)).
 + apply mu_sub=>bs; exact(noise_raw_bad_covered bs).
 have hu:=noise_coefficient_union raw_four_law
   (fun k bs=>576<=`|noise_actual_sum k bs|) noise_actual_coefficient_tail.
 smt().
qed.

lemma raw_four_bad_numerical : mu raw_four_law four_buffers_bad<1%r/(2%r^356).
proof. have hb:=raw_four_bad_bound; have hn:=noise_union_numerical; smt(). qed.
