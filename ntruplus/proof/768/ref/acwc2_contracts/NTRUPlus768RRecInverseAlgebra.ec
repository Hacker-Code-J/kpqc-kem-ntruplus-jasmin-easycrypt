require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.
require import Array4 Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768BaseInvAlgebra NTRUPlus768BaseInvProof.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof.
require import NTRUPlus768PolyBaseInvBridge NTRUPlus768PolyBaseInvProof.
require import NTRUPlus768BaseInvWordAlgebra.
require import NTRUPlus768KeygenCompleteInverse NTRUPlus768KeygenHBridge.
require import NTRUPlus768KeygenPublicKeyBridge NTRUPlus768ValidKeyR2Algebra.
require import NTRUPlus768PolySubAlgebra NTRUPlus768NTTSchedule.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768RRecPublicInverse.
import Ring.IntID IntOrder CycloFq.

(* The determinant is the norm in the terminal quartic. Multiplicativity
   gives the converse needed here: an existing inverse makes this actual
   BaseInv determinant nonzero. This is only four-coefficient algebra. *)
op rrec_quartic_norm (a0 a1 a2 a3 z:int) =
 (a0*a0+z*(a2*a2-2*a1*a3))*(a0*a0+z*(a2*a2-2*a1*a3))-
 z*(a1*a1+z*a3*a3-2*a0*a2)*(a1*a1+z*a3*a3-2*a0*a2).
lemma rrec_norm_product a b z :
 rrec_quartic_norm (coeff0 a b z) (coeff1 a b z) (coeff2 a b z) (coeff3 a b z) z=
 inverse_determinant a z*inverse_determinant b z.
proof.
 rewrite /rrec_quartic_norm /inverse_determinant /inverse_u /inverse_v
 /coeff0 /coeff1 /coeff2 /coeff3; ring.
qed.
lemma rrec_norm_unit c0 c1 c2 c3 z :
 c0%%q=1%%q => c1%%q=0%%q => c2%%q=0%%q => c3%%q=0%%q =>
 rrec_quartic_norm c0 c1 c2 c3 z%%q=1%%q.
proof.
 move=>hc0 hc1 hc2 hc3.
 have h0:incyclocoeff c0=one by apply asint_inj; rewrite incyclocoeffK oneE hc0 /q /=.
 have h1:incyclocoeff c1=zero by apply asint_inj; rewrite incyclocoeffK zeroE hc1 /q /=.
 have h2:incyclocoeff c2=zero by apply asint_inj; rewrite incyclocoeffK zeroE hc2 /q /=.
 have h3:incyclocoeff c3=zero by apply asint_inj; rewrite incyclocoeffK zeroE hc3 /q /=.
 have hn:incyclocoeff(rrec_quartic_norm c0 c1 c2 c3 z)=one.
 + rewrite /rrec_quartic_norm !(incyclocoeffB,incyclocoeffD,incyclocoeffM) h0 h1 h2 h3; ring.
 have he:=congr1 asint _ _ hn.
 by move:he; rewrite incyclocoeffK oneE /q /=.
qed.
lemma rrec_block_known_inverse_nonzero a b z :
 block_product_qring a b qring_unit4 z => inverse_determinant a z%%q<>0.
proof.
 rewrite /block_product_qring qring_unit4_coeff0 qring_unit4_coeff1
 qring_unit4_coeff2 qring_unit4_coeff3.
 move=>hi.
 have h0:coeff0 a b z%%q=1%%q by smt().
 have h1:coeff1 a b z%%q=0%%q by smt().
 have h2:coeff2 a b z%%q=0%%q by smt().
 have h3:coeff3 a b z%%q=0%%q by smt().
 have hn:=rrec_norm_unit (coeff0 a b z) (coeff1 a b z) (coeff2 a b z) (coeff3 a b z) z h0 h1 h2 h3.
 rewrite rrec_norm_product in hn.
 apply/negP=>hz.
 have hzero:(inverse_determinant a z*inverse_determinant b z)%%q=0.
 + by rewrite -modzMml hz /=.
 move:hn; rewrite hzero /q /=; done.
qed.
lemma rrec_known_inverse_status hp inverse :
 in_qrange768 hp => poly_basemul_qring hp inverse ntt_block_identity 192 =>
 keygen_inverse_status hp=W64.zero.
proof.
 move=>hq hi.
 have hs:poly_blocks_succeed hp 192.
 + move=>k hk.
   have hb:=poly_basemul_qring_block_product hp inverse ntt_block_identity k hi hk.
   rewrite(ntt_identity_block k hk) in hb.
   have hd:=rrec_block_known_inverse_nonzero _ _ _ hb.
   have ha:=in_qrange768_block4 hp k hq hk.
   have hz:in_qrange(poly_block_zeta k).
   + rewrite poly_block_zeta_eq; exact(block_zeta_in_qrange k hk).
   have ht:zeta_decode(poly_block_zeta k)=terminal_value k.
   + rewrite poly_block_zeta_eq; move:(block_zeta_math_terminal_value k hk).
     by rewrite /block_zeta_math.
   have hr:=zeta_decode_relation (poly_block_zeta k) hz; rewrite ht in hr.
   have hf:=exact_status_determinant_nonzero_iff (block4 hp k) (poly_block_zeta k) (terminal_value k) ha hz hr.
   rewrite /poly_block_status; exact(iffRL _ _ hf hd).
 by rewrite /keygen_inverse_status hs.
qed.

lemma rrec_block_unit_product a z : block_product_qring qring_unit4 a a z.
proof.
 apply block_product_qring_comm.
 by rewrite /block_product_qring coeff0_qring_unit4 coeff1_qring_unit4
 coeff2_qring_unit4 coeff3_qring_unit4.
qed.
lemma rrec_block_inverse_unique hp a b z i :
 block_product_qring hp a qring_unit4 z =>
 block_product_qring hp b qring_unit4 z => 0<=i<4 =>
 coeff a.[i]%%q=coeff b.[i]%%q.
proof.
 move=>ha hb hi.
 have h:=block_product_reassociate a hp b qring_unit4 qring_unit4 b z
   (block_product_qring_comm _ _ _ _ ha) hb (rrec_block_unit_product b z).
 apply/eq_sym; exact(block_product_unit_coeff a b z i h hi).
qed.
lemma rrec_poly_inverse_unique hp a b :
 poly_basemul_qring hp a ntt_block_identity 192 =>
 poly_basemul_qring hp b ntt_block_identity 192 => poly_coeff_eq_mod_q a b.
proof.
 move=>ha hb j hj.
 have hk:0<=j%/4<192 by smt().
 have hi:0<=j%%4<4 by smt().
 have hidx:4*(j%/4)+j%%4=j by smt(IntDiv.divz_eq).
 have h1:=poly_basemul_qring_block_product _ _ _ _ ha hk.
 have h2:=poly_basemul_qring_block_product _ _ _ _ hb hk.
 rewrite(ntt_identity_block _ hk) in h1.
 rewrite(ntt_identity_block _ hk) in h2.
 have h:=rrec_block_inverse_unique _ _ _ _ (j%%4) h1 h2 hi.
 by move:h; rewrite /block4 !Array4.initiE 1:hi 1:hi /= hidx.
qed.
lemma rrec_public_inverse_known hp inverse :
 in_qrange768 hp => poly_basemul_qring hp inverse ntt_block_identity 192 =>
 rrec_public_inverse hp<>None /\
 poly_coeff_eq_mod_q (oget(rrec_public_inverse hp)) inverse.
proof.
 move=>hq hi; have hs:=rrec_known_inverse_status hp inverse hq hi.
 have hn:rrec_public_inverse hp<>None by rewrite /rrec_public_inverse hs.
 split; first exact hn.
 exact(rrec_poly_inverse_unique hp _ inverse (rrec_public_inverse_product hp hq hn) hi).
qed.
lemma rrec_canonical_coeff p j : in_canonical_range768 p => 0<=j<768 =>
 0<=coeff p.[j]<q.
proof.
 move=>hp hj.
 have hk:0<=j%/4<192 by smt().
 have hi:0<=j%%4<4 by smt().
 have hidx:4*(j%/4)+j%%4=j by smt(IntDiv.divz_eq).
 have hb:=hp (j%/4) hk.
 have hc:in_canonical_range (block4 p (j%/4)).[j%%4].
 + rewrite /in_canonical_range4 in hb.
   have he:j%%4=0 \/ j%%4=1 \/ j%%4=2 \/ j%%4=3 by smt().
   smt().
 by move:hc; rewrite /in_canonical_range /block4 Array4.initiE 1:hi /= hidx.
qed.
lemma rrec_public_inverse_known_canonical hp inverse :
 in_qrange768 hp => in_canonical_range768 inverse =>
 poly_basemul_qring hp inverse ntt_block_identity 192 =>
 rrec_public_inverse hp=Some inverse.
proof.
 move=>hq hc hi; have [hn he]:=rrec_public_inverse_known hp inverse hq hi.
 have ho:=rrec_public_inverse_canonical hp hq hn.
 have hv:oget(rrec_public_inverse hp)=inverse.
 + apply Array768.tP=>j hj.
   have hra:=rrec_canonical_coeff _ j ho hj.
   have hrb:=rrec_canonical_coeff _ j hc hj.
   have hz:=he j hj.
   rewrite (modz_small _ q hra) (modz_small _ q hrb) in hz.
   by rewrite (word_from_coeff (oget(rrec_public_inverse hp)).[j]) (word_from_coeff inverse.[j]) hz.
 by rewrite -hv; apply some_oget.
qed.
