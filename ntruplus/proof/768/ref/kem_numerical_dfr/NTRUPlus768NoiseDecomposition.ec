require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JUtils.
require import Array768.
require import NTRUPlus768IntegerConvolution.
import IntOrder Ring.IntID.

op noise_partner (k i:int) : int = (k-i) %%384.
op noise_reduce_weight (k s:int) : int =
 if s<768 then b2i(k=s)
 else if s<1152 then b2i(k=s-384)-b2i(k=s-768)
 else -b2i(k=s-1152).
op noise_weighted_block (k i j a c b d:int) : int =
 a*b*noise_reduce_weight k (i+j) +
 (a*d+c*b)*noise_reduce_weight k (i+j+384) +
 c*d*noise_reduce_weight k (i+j+768).

(* Four disjoint input coordinates per block, ordered (a,c,b,d). *)
op noise_block (k i a c b d:int) : int =
 if k<384 then
   if i<=k then a*b-c*d else -(a*d+c*b+c*d)
 else if i<=k-384 then a*d+c*b+c*d else a*b+a*d+c*b.
op noise_block_kind (k i:int) =
 if k<384 then (if i<=k then 0 else 1)
 else (if i<=k-384 then 2 else 3).
op noise_product_blocks (a b:int Array768.t) (k:int) =
 Bigint.BIA.bigi predT (fun i=>
   noise_block k i a.[i] a.[i+384]
     b.[noise_partner k i] b.[noise_partner k i+384]) 0 384.
op noise_block_values (a b:int Array768.t) (k:int) : int list =
 map (fun i=>noise_block k i a.[i] a.[i+384]
   b.[noise_partner k i] b.[noise_partner k i+384]) (range 0 384).

lemma noise_block_kind_range k i : 0<=noise_block_kind k i<4.
proof. rewrite /noise_block_kind; smt(). qed.
lemma noise_block_kindE k i a c b d :
 noise_block k i a c b d =
 if noise_block_kind k i=0 then a*b-c*d
 else if noise_block_kind k i=1 then -(a*d+c*b+c*d)
 else if noise_block_kind k i=2 then a*d+c*b+c*d else a*b+a*d+c*b.
proof. by rewrite /noise_block /noise_block_kind; smt(). qed.
lemma noise_block_values_size a b k : size(noise_block_values a b k)=384.
proof. by rewrite /noise_block_values size_map size_range. qed.
lemma noise_product_blocks_sumz a b k :
 noise_product_blocks a b k=sumz(noise_block_values a b k).
proof.
 by rewrite /noise_product_blocks /noise_block_values Bigint.sumzE Bigint.BIA.big_map.
qed.

lemma noise_partner_range k i : 0<=noise_partner k i<384.
proof. rewrite /noise_partner; smt(modz_cmp). qed.
lemma noise_partner_involution k i : 0<=i<384 =>
 noise_partner k (noise_partner k i)=i.
proof. move=> hi; rewrite /noise_partner; smt(divz_eq modz_cmp). qed.
lemma noise_partner_injective k i j : 0<=i<384 => 0<=j<384 =>
 noise_partner k i=noise_partner k j => i=j.
proof. move=> hi hj he; smt(noise_partner_involution). qed.
lemma noise_coordinate_partition i j (b c:bool) :
 0<=i<384 => 0<=j<384 =>
 i+384*b2i b=j+384*b2i c => i=j /\ b=c.
proof. move=> hi hj; rewrite /b2i; case b; case c; smt(). qed.
lemma noise_coordinate_range i (b:bool) : 0<=i<384 =>
 0<=i+384*b2i b<768.
proof. rewrite /b2i; case b; smt(). qed.

lemma noise_partner_formula k i : 0<=i<384 =>
 noise_partner k i=
 if i<=k %%384 then k %%384-i else k %%384-i+384.
proof.
 move=> hi; rewrite /noise_partner.
 have he:(k-i) %%384=(k %%384-i) %%384 by smt(divz_eq modz_cmp).
 rewrite he.
 have hk:0<=k %%384<384 by smt(modz_cmp).
 case(i<=k %%384)=>hh.
 + rewrite modz_small; smt().
 + rewrite -modzDr modz_small; smt().
qed.

lemma integer_reduced_monomial_get k s : 0<=k<768 =>
 (integer_reduced_monomial s).[k]=noise_reduce_weight k s.
proof.
 move=> hk; rewrite /integer_reduced_monomial /noise_reduce_weight.
 case(s<768)=>hs.
 + by rewrite integer_unit_get 1:hk /b2i.
 case(s<1152)=>hs'.
 + rewrite integer_add_get 1:hk integer_scale_get 1:hk
     !integer_unit_get 1:hk 1:hk /b2i; smt().
 + rewrite integer_scale_get 1:hk integer_unit_get 1:hk /b2i; smt().
qed.
lemma noise_reduce_support k s : noise_reduce_weight k s<>0 =>
 s=k \/ s=k+384 \/ s=k+768 \/ s=k+1152.
proof. rewrite /noise_reduce_weight /b2i; smt(). qed.
lemma noise_reduce_off_partner k i j t : 0<=j<384 =>
 j<>noise_partner k i => noise_reduce_weight k (i+j+384*t)=0.
proof.
 move=> hj hn; have h:=noise_reduce_support k (i+j+384*t).
 rewrite /noise_partner in hn.
 smt(divz_eq modz_cmp).
qed.
lemma noise_weighted_off_partner k i j a c b d : 0<=j<384 =>
 j<>noise_partner k i => noise_weighted_block k i j a c b d=0.
proof.
 move=> hj hn; rewrite /noise_weighted_block.
 have h0:=noise_reduce_off_partner k i j 0 hj hn.
 have h1:=noise_reduce_off_partner k i j 1 hj hn.
 have h2:=noise_reduce_off_partner k i j 2 hj hn.
 by move:h0 h1 h2=> /= -> -> ->; ring.
qed.
lemma noise_block_matrix k i : 0<=k<768 => 0<=i<384 =>
 (noise_reduce_weight k (i+noise_partner k i),
  noise_reduce_weight k (i+noise_partner k i+384),
  noise_reduce_weight k (i+noise_partner k i+768)) =
 if k<384 then if i<=k then (1,0,-1) else (0,-1,-1)
 else if i<=k-384 then (0,1,1) else (1,1,0).
proof.
 move=> hk hi; rewrite (noise_partner_formula k i hi).
 case(k<384)=>hl.
 + have hm:k %%384=k by rewrite modz_small; smt().
   rewrite hm /noise_reduce_weight /b2i; smt().
 + have hm:k %%384=k-384 by smt(divz_eq modz_cmp).
   rewrite hm /noise_reduce_weight /b2i; smt().
qed.
lemma noise_weighted_is_block k i a c b d : 0<=k<768 => 0<=i<384 =>
 noise_weighted_block k i (noise_partner k i) a c b d=noise_block k i a c b d.
proof.
 move=> hk hi; have hm:=noise_block_matrix k i hk hi.
 rewrite /noise_weighted_block /noise_block.
 case(k<384)=>h1; case(i<=k)=>h2; case(i<=k-384)=>h3;
   move:hm; rewrite h1 h2 h3 /=; move=> [-> [-> ->]]; ring.
qed.

lemma integer_sum_get (vs:int Array768.t list) k : 0<=k<768 =>
 (integer_sum vs).[k]=Bigint.BIA.big predT (fun v=>v.[k]) vs.
proof.
 move=> hk; elim:vs=>[|v vs ih].
 + by rewrite /integer_sum /= integer_zero_get 1:hk Bigint.BIA.big_nil.
 + by rewrite /integer_sum /= integer_add_get 1:hk -/integer_sum ih Bigint.BIA.big_consT.
qed.
lemma integer_product_coefficient a b k : 0<=k<768 =>
 (integer_product a b).[k]=
 Bigint.BIA.bigi predT(fun i=>Bigint.BIA.bigi predT(fun j=>
   a.[i]*b.[j]*noise_reduce_weight k (i+j)) 0 768) 0 768.
proof.
 move=> hk; rewrite /integer_product integer_sum_get 1:hk Bigint.BIA.big_map.
 apply Bigint.BIA.eq_big_int=>i hi /=.
 rewrite integer_sum_get 1:hk Bigint.BIA.big_map.
 apply Bigint.BIA.eq_big_int=>j hj /=.
 by rewrite integer_scale_get 1:hk integer_reduced_monomial_get 1:hk.
qed.
lemma noise_sum_halves (f:int->int) :
 Bigint.BIA.bigi predT f 0 768 =
 Bigint.BIA.bigi predT(fun i=>f i+f(i+384)) 0 384.
proof.
 rewrite (Bigint.BIA.big_cat_int 384) 1,2://.
 rewrite (Bigint.BIA.big_addn 0 768 384) /=.
 by rewrite Bigint.BIA.big_split.
qed.
lemma noise_sum_single (f:int->int) x : 0<=x<384 =>
 (forall j,0<=j<384 => j<>x => f j=0) =>
 Bigint.BIA.bigi predT f 0 384=f x.
proof.
 move=> hx hf.
 rewrite (Bigint.BIA.bigD1 _ _ x) ?(mem_range,range_uniq) //=.
 rewrite Bigint.BIA.big1_seq ?addr0 //=.
 move=> j [hne /mem_range hj]; exact(hf j hj hne).
qed.

lemma integer_product_paired a b k : 0<=k<768 =>
 (integer_product a b).[k]=
 Bigint.BIA.bigi predT(fun i=>Bigint.BIA.bigi predT(fun j=>
   noise_weighted_block k i j a.[i] a.[i+384] b.[j] b.[j+384]) 0 384) 0 384.
proof.
 move=> hk; rewrite (integer_product_coefficient a b k hk) noise_sum_halves.
 apply Bigint.BIA.eq_big_int=>i hi /=.
 rewrite -Bigint.BIA.big_split noise_sum_halves.
 apply Bigint.BIA.eq_big_int=>j hj /=.
 rewrite /noise_weighted_block.
 have h1:i+384+j=i+j+384 by ring.
 have h2:i+(j+384)=i+j+384 by ring.
 have h3:i+384+(j+384)=i+j+768 by ring.
 rewrite h1 h2 h3; ring.
qed.

lemma integer_product_noise_blocks a b k : 0<=k<768 =>
 (integer_product a b).[k]=noise_product_blocks a b k.
proof.
 move=> hk; rewrite (integer_product_paired a b k hk) /noise_product_blocks.
 apply Bigint.BIA.eq_big_int=>i hi /=.
 rewrite (noise_sum_single _ (noise_partner k i)) 1:noise_partner_range.
 + move=> j hj hn; exact(noise_weighted_off_partner k i j
     a.[i] a.[i+384] b.[j] b.[j+384] hj hn).
 exact(noise_weighted_is_block k i a.[i] a.[i+384]
   b.[noise_partner k i] b.[noise_partner k i+384] hk hi).
qed.

lemma two_integer_products_noise_blocks a b c d k : 0<=k<768 =>
 (integer_add(integer_product a b)(integer_product c d)).[k]=
 noise_product_blocks a b k+noise_product_blocks c d k.
proof.
 move=> hk; by rewrite integer_add_get 1:hk !integer_product_noise_blocks 1:hk 1:hk.
qed.

lemma two_integer_products_block_list a b c d k : 0<=k<768 =>
 (integer_add(integer_product a b)(integer_product c d)).[k]=
 sumz(noise_block_values a b k ++noise_block_values c d k).
proof.
 move=> hk; by rewrite (two_integer_products_noise_blocks a b c d k hk)
   !noise_product_blocks_sumz !Bigint.sumzE Bigint.BIA.big_cat.
qed.
lemma two_product_block_list_size a b c d k :
 size(noise_block_values a b k ++noise_block_values c d k)=768.
proof. by rewrite size_cat !noise_block_values_size. qed.

(* A coordinate permutation of a complete input, preserving each half.
   Involution supplies the inverse required by the product-law argument. *)
op noise_permutation (k x:int) =
 noise_partner k (x %%384)+384*(x %/384).
lemma noise_permutation_range k x : 0<=x<768 => 0<=noise_permutation k x<768.
proof.
 move=> hx; have hp:=noise_partner_range k (x %%384).
 rewrite /noise_permutation; smt(divz_eq modz_cmp).
qed.
lemma noise_permutation_involution k x : 0<=x<768 =>
 noise_permutation k (noise_permutation k x)=x.
proof.
 move=> hx; rewrite /noise_permutation.
 have hp:=noise_partner_range k (x %%384).
 have hxmod:0<=x %%384<384 by smt(modz_cmp).
 have hmod:(noise_partner k (x %%384)+384*(x %/384)) %%384=
   noise_partner k (x %%384) by smt(divz_eq modz_cmp).
 have hdiv:(noise_partner k (x %%384)+384*(x %/384)) %/384=x %/384
   by smt(divz_eq modz_cmp).
 rewrite hmod hdiv (noise_partner_involution k (x %%384) hxmod).
 smt(divz_eq).
qed.
lemma noise_permutation_pair k i (b:bool) : 0<=i<384 =>
 noise_permutation k (i+384*b2i b)=noise_partner k i+384*b2i b.
proof.
 move=> hi; rewrite /noise_permutation.
 have hm:(i+384*b2i b) %%384=i by smt(divz_eq modz_cmp).
 have hd:(i+384*b2i b) %/384=b2i b by smt(divz_eq modz_cmp).
 by rewrite hm hd.
qed.
