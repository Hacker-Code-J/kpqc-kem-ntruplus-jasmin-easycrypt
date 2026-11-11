require import AllCore IntDiv List Ring StdBigop StdOrder.
from Jasmin require import JWord.
require import Array192 Array768.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768PolySOTPDecodeAlgebra.
require import NTRUPlus768KeygenSamplerAlgebra.
require import NTRUPlus768BasemulAlgebra NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics.
require import NTRUPlus768ForwardNTTStage1Semantics NTRUPlus768ForwardNTTRadix3Semantics.
require import NTRUPlus768UniformOrbitBound.
import NTRUPoly.BigPoly.
abbrev ( + ) = NTRUPoly.PolyComRing.( + ).
abbrev [ - ] = NTRUPoly.PolyComRing.([-]).
abbrev ( * ) = NTRUPoly.PolyComRing.( * ).
abbrev ( - ) (p q:poly) = p+(-q).
abbrev exp = NTRUPoly.PolyComRing.exp.

op acceptance_shape (is_f:bool) (buf:W8.t Array192.t) =
 if is_f then keygen_f_pre_ntt_spec buf else keygen_g_pre_ntt_spec buf.
op acceptance_input (is_f:bool) (buf:W8.t Array192.t) =
 input_poly (acceptance_shape is_f buf).
op acceptance_head_bit (buf:W8.t Array192.t) (k:int) =
 b2i (buf.[k %/ 8]).[k %% 8].
op acceptance_same_tail (b c:W8.t Array192.t) =
 forall i, 2<=i<192 => b.[i]=c.[i].
op acceptance_head_poly (buf:W8.t Array192.t) : poly =
 PCA.bigi predT (fun k=>polyC(lift_int(3*acceptance_head_bit buf k))*exp X k) 0 16.

lemma acceptance_cbd_bit b j :
 0<=j => poly_cbd1_bit b j=b2i b.[j].
proof.
 move=> hj; rewrite /poly_cbd1_bit /poly_sotp_bit.
 by rewrite W8.b2i_get.
qed.

lemma acceptance_shape_coeff is_f buf k :
 0<=k<768 =>
 coeff (acceptance_shape is_f buf).[k]=
 3*poly_cbd1_coeff_int buf k+(if is_f then keygen_delta0 k else 0).
proof.
 move=> hk; rewrite /acceptance_shape; case is_f=> _ /=.
 + exact (keygen_f_pre_ntt_coeff buf k hk).
 by rewrite keygen_g_pre_ntt_coeff.
qed.

lemma acceptance_cbd_tail b c k :
 acceptance_same_tail b c => 16<=k<768 =>
 poly_cbd1_coeff_int b k=poly_cbd1_coeff_int c k.
proof.
 move=> ht hk.
 rewrite /poly_cbd1_coeff_int /poly_cbd1_head_bit /poly_cbd1_tail_bit.
 rewrite (ht (k %/ 8) _) 1:/# (ht (96+k %/ 8) _) 1:/#.
 done.
qed.

lemma acceptance_cbd_head_difference b c k :
 acceptance_same_tail b c => 0<=k<16 =>
 poly_cbd1_coeff_int b k-poly_cbd1_coeff_int c k=
 acceptance_head_bit b k-acceptance_head_bit c k.
proof.
 move=> ht hk.
 rewrite /poly_cbd1_coeff_int /poly_cbd1_head_bit /poly_cbd1_tail_bit.
 rewrite (ht (96+k %/ 8) _) 1:/#.
 rewrite !acceptance_cbd_bit ~-1:/# /acceptance_head_bit.
 ring.
qed.

lemma acceptance_segment_equal is_f b c base len :
 acceptance_same_tail b c => 16<=base => 0<=len => base+len<=768 =>
 segment_poly (acceptance_shape is_f b) base len=
 segment_poly (acceptance_shape is_f c) base len.
proof.
 move=> ht hb hl hend; rewrite /segment_poly.
 apply PCA.eq_big_int=>k hk.
 rewrite /= /lift_word !acceptance_shape_coeff ~-1:/#.
 by rewrite (acceptance_cbd_tail b c (k+base) ht _) 1:/#.
qed.

lemma acceptance_segment_head_difference is_f b c :
 acceptance_same_tail b c =>
 segment_poly (acceptance_shape is_f b) 0 16-
 segment_poly (acceptance_shape is_f c) 0 16=
 acceptance_head_poly b-acceptance_head_poly c.
proof.
 move=>ht.
 have hc : segment_poly (acceptance_shape is_f b) 0 16+acceptance_head_poly c=
   segment_poly (acceptance_shape is_f c) 0 16+acceptance_head_poly b.
 + rewrite /segment_poly /acceptance_head_poly.
   have hleft := (PCA.big_split predT
    (fun i=>polyC(lift_word(acceptance_shape is_f b).[i+0])*exp X i)
    (fun i=>polyC(lift_int(3*acceptance_head_bit c i))*exp X i) (range 0 16)).
   have hright := (PCA.big_split predT
    (fun i=>polyC(lift_word(acceptance_shape is_f c).[i+0])*exp X i)
    (fun i=>polyC(lift_int(3*acceptance_head_bit b i))*exp X i) (range 0 16)).
   rewrite /NTRUPoly.PolyComRing.(+) -hleft -hright.
   apply PCA.eq_big_int=>k hk.
   rewrite /= /lift_word !acceptance_shape_coeff ~-1:/# /=.
   have hd:=acceptance_cbd_head_difference b c k ht hk.
   have he : 3*poly_cbd1_coeff_int b k+(if is_f then keygen_delta0 k else 0)+
      3*acceptance_head_bit c k =
     3*poly_cbd1_coeff_int c k+(if is_f then keygen_delta0 k else 0)+
      3*acceptance_head_bit b k by smt().
   rewrite -!NTRUPoly.PolyComRing.mulrDl -!NTRUPoly.polyCD /lift_int.
   by rewrite -!CycloFq.incyclocoeffD he.
 have hh:=congr1 (fun p:poly=>p-acceptance_head_poly c-
   segment_poly (acceptance_shape is_f c) 0 16) _ _ hc.
 have hl : (segment_poly (acceptance_shape is_f b) 0 16+acceptance_head_poly c)-
   acceptance_head_poly c-segment_poly (acceptance_shape is_f c) 0 16=
   segment_poly (acceptance_shape is_f b) 0 16-segment_poly (acceptance_shape is_f c) 0 16
   by ring.
 have hr : (segment_poly (acceptance_shape is_f c) 0 16+acceptance_head_poly b)-
   acceptance_head_poly c-segment_poly (acceptance_shape is_f c) 0 16=
   acceptance_head_poly b-acceptance_head_poly c by ring.
 by move:hh; rewrite /= hl hr.

qed.

lemma acceptance_input_head_difference is_f b c :
 acceptance_same_tail b c =>
 acceptance_input is_f b-acceptance_input is_f c=
 acceptance_head_poly b-acceptance_head_poly c.
proof.
 move=> ht; rewrite /acceptance_input /input_poly.
 have hhigh:=acceptance_segment_equal is_f b c 384 384 ht _ _ _;
   first 3 smt().
 have hmid:=acceptance_segment_equal is_f b c 16 368 ht _ _ _;
   first 3 smt().
 have hhead:=acceptance_segment_head_difference is_f b c ht.
 rewrite hhigh.
 rewrite (segment_poly_split (acceptance_shape is_f b) 0 16 368) 1,2:/#.
 rewrite (segment_poly_split (acceptance_shape is_f c) 0 16 368) 1,2:/# /= hmid.
 rewrite -hhead; ring.
qed.
