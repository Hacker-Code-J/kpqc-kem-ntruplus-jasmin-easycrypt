require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.
require import Array4 Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768PolyBasemulProof.
require import NTRUPlus768CyclotomicFactorization.
require import NTRUPlus768EvaluationSemantics NTRUPlus768TerminalRepresentation.
require import NTRUPlus768CoefficientRecovery NTRUPlus768KeygenPublicKeyBridge.

(* Congruence modulo a monic quartic uniquely determines a block of four
   coefficients. This is local uniqueness, not an assumed global CRT map. *)
lemma rrec_monomial1_coeff (c:CycloFq.cyclocoeff) (j:int) :
 NTRUPoly."_.[_]" (polyC c * X) j =
 if j=1 then c else CycloFq.zero.
proof.
 rewrite -(NTRUPoly.PolyComRing.expr1 X).
 exact(monomial_coeff c 1 j _); smt().
qed.
lemma rrec_block_poly_coeff (a:W16.t Array4.t) (j:int) : 0<=j<4 =>
 NTRUPoly."_.[_]" (block_poly a) j=lift_word a.[j].
proof.
 move=>hj.
 rewrite /block_poly /block_poly_fq !NTRUPoly.polyDE NTRUPoly.polyCE
   rrec_monomial1_coeff !monomial_coeff 1,2://.
 case(j=0)=>h0; first by rewrite h0 /= !NTRUPoly.Coeff.addr0.
 case(j=1)=>h1; first by rewrite h1 /= !NTRUPoly.Coeff.addr0 NTRUPoly.Coeff.add0r.
 case(j=2)=>h2; first by rewrite h2 /= !NTRUPoly.Coeff.addr0 NTRUPoly.Coeff.add0r.
 have h3:j=3 by smt().
 by rewrite h3 /= !NTRUPoly.Coeff.add0r.
qed.
lemma rrec_block_poly_coeff_out (a:W16.t Array4.t) (j:int) : 4<=j =>
 NTRUPoly."_.[_]" (block_poly a) j=CycloFq.zero.
proof.
 move=>hj.
 rewrite /block_poly /block_poly_fq !NTRUPoly.polyDE NTRUPoly.polyCE
   rrec_monomial1_coeff !monomial_coeff 1,2://.
 have h0:j<>0 by smt().
 have h1:j<>1 by smt().
 have h2:j<>2 by smt().
 have h3:j<>3 by smt().
 by rewrite (negbTE _ h0) (negbTE _ h1) (negbTE _ h2) (negbTE _ h3) !NTRUPoly.Coeff.addr0.
qed.
lemma rrec_block_poly_degree (a:W16.t Array4.t) : NTRUPoly.deg(block_poly a)<=4.
proof. apply NTRUPoly.deg_leP=> // i hi; exact(rrec_block_poly_coeff_out a i hi). qed.
lemma rrec_quartic_degree (k:int) : NTRUPoly.deg(quartic_modulus k)=5.
proof.
 have ht:NTRUPoly.deg(-polyC(terminal_root_field k))<=1.
 + rewrite NTRUPoly.degN; exact(NTRUPoly.degC_le _).
 rewrite /quartic_modulus NTRUPoly.degDl.
 + rewrite NTRUPoly.deg_polyXn //; smt().
 by rewrite NTRUPoly.deg_polyXn.
qed.
lemma rrec_quartic_leading (k:int) : NTRUPoly.lc(quartic_modulus k)=CycloFq.one.
proof.
 rewrite rrec_quartic_degree /= /quartic_modulus
   NTRUPoly.polyDE NTRUPoly.polyNE NTRUPoly.polyXnE //= NTRUPoly.polyCE /=.
 by rewrite NTRUPoly.Coeff.oppr0 NTRUPoly.Coeff.addr0.
qed.
lemma rrec_eqm4_low_degree_unique (k:int) (p r:poly) :
 NTRUPoly.deg p<=4 =>NTRUPoly.deg r<=4 =>eqm4 k p r=>p=r.
proof.
 move=>hp hr [h hh].
 have hd:=NTRUPoly.degB r p.
 have hl:NTRUPoly.deg(r-p)<=4 by smt(IntOrder.ler_maxrP).
 case(h=poly0)=>hz.
 + have he:r-p=poly0 by rewrite hh hz; exact(NTRUPoly.PolyComRing.mul0r _).
   have ->:r=(r-p)+p by ring.
   rewrite he; apply/eq_sym; exact(NTRUPoly.PolyComRing.add0r p).
 have hc:CycloFq.( * ) (NTRUPoly.lc h)(NTRUPoly.lc(quartic_modulus k))<>CycloFq.zero.
 + by rewrite rrec_quartic_leading NTRUPoly.Coeff.mulr1 NTRUPoly.lc_eq0.
 have hm:=NTRUPoly.degM_proper h (quartic_modulus k) hc.
 rewrite rrec_quartic_degree in hm.
 have hpos:=NTRUPoly.ge0_deg h.
 have hn:NTRUPoly.deg h<>0 by rewrite NTRUPoly.deg_eq0.
 rewrite hh in hl; smt().
qed.
lemma rrec_eqm4_block_coeff (k:int) (a b:W16.t Array4.t) (j:int) : eqm4 k(block_poly a)(block_poly b)=>
 0<=j<4 => coeff a.[j] %% q=coeff b.[j] %% q.
proof.
 move=>he hj.
 have hp:=rrec_eqm4_low_degree_unique k (block_poly a)(block_poly b)
   (rrec_block_poly_degree a)(rrec_block_poly_degree b) he.
 have hl:lift_word a.[j]=lift_word b.[j].
 + by rewrite -(rrec_block_poly_coeff a j hj) -(rrec_block_poly_coeff b j hj) hp.
 move/(congr1 CycloFq.asint):hl.
 by rewrite /lift_word /lift_int !CycloFq.incyclocoeffK.
qed.
lemma rrec_terminal_same_poly_mod_q (a b:W16.t Array768.t) (p:poly) :
 terminal_represents a p=>terminal_represents b p=>poly_coeff_eq_mod_q a b.
proof.
 move=>ha hb j hj.
 have hk:0<=j%/4<192 by smt(IntDiv.edivzP).
 have hi:0<=j%%4<4 by smt(IntDiv.edivzP).
 have he:=eqm4_trans (j%/4) (block_poly(block4 a (j%/4))) p
   (block_poly(block4 b (j%/4)))
   (eqm4_sym (j%/4) p (block_poly(block4 a (j%/4))) (ha (j%/4) hk))
   (hb (j%/4) hk).
 have hc:=rrec_eqm4_block_coeff (j%/4) (block4 a (j%/4)) (block4 b (j%/4)) (j%%4) he hi.
 move:hc; rewrite /block4 !Array4.initiE 1,2:hi /=.
 have hj':4*(j%/4)+j%%4=j by smt(IntDiv.edivzP).
 by rewrite hj'.
qed.
