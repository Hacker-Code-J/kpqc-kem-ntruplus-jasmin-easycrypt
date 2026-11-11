From mathcomp Require Import all_ssreflect all_algebra.
Require Import SRIrreducibleBase SRIrreducibleFactor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Pdiv.CommonRing.
Local Open Scope ring_scope.

Lemma sri_bool_squareD (x y:{poly bool}) : (x+y)^+2=x^+2+y^+2.
Proof.
have hz (p:{poly bool}):p+p=0.
  apply/polyP=>i;rewrite coefD coef0;by case:(p`_i).
rewrite !expr2 !mulrDl !mulrDr [y*x]mulrC.
by rewrite -addrA [x*y+(x*y+y*y)]addrA hz add0r.
Qed.
Lemma sri_bool_power2D (x y:{poly bool}) n :
 (x+y)^+(2^n)=x^+(2^n)+y^+(2^n).
Proof.
elim:n=>[|n IH];first by rewrite expn0 !expr1.
by rewrite expnSr !exprM IH sri_bool_squareD.
Qed.
Lemma sri_map2_g : sri_map2 (sri_g [ringType of int])=sri_g [ringType of bool].
Proof. by rewrite /sri_map2 /sri_g !rmorphD !rmorphXn rmorph1 /= map_polyX. Qed.
Lemma sri_phi_mod2 :
 sri_map2 (sri_phi [ringType of int])=(sri_g [ringType of bool])^+128.
Proof.
rewrite /sri_map2 /sri_phi /sri_g !rmorphD ?rmorphB ?rmorphN !rmorphXn rmorph1 /= map_polyX.
rewrite -[128%N]/(2^7)%N !sri_bool_power2D -!exprM expr1n /=.
have hn (p:{poly bool}): -p=p.
  apply/polyP=>i;rewrite coefN;by case:(p`_i).
by rewrite hn.
Qed.

Local Notation G := (sri_g [ringType of int]).
Lemma sri_X9_identity : ('X^9:{poly int})=('X^3-1)*G+1.
Proof.
rewrite /sri_g mulrBl !mulrDr ?mulrDl ?mul1r ?mulr1 -!exprD.
rewrite /= -['X^9+'X^6+'X^3]addrA (opprD ('X^6+'X^3) 1).
by rewrite (addrA ('X^9+('X^6+'X^3)) (-('X^6+'X^3)) (-1)) addrK subrK.
Qed.
Lemma sri_X9_rem : rmodp ('X^9) G = 1.
Proof.
rewrite sri_X9_identity Pdiv.RingMonic.rmodp_addl_mul_small ?sri_g_monic //.
by rewrite size_poly1 sri_g_size.
Qed.
Lemma sri_X9n_rem n : rmodp ('X^(9*n)) G = 1.
Proof.
rewrite exprM -Pdiv.RingMonic.rmodpX ?sri_g_monic // sri_X9_rem expr1n.
by rewrite rmodp_small // size_poly1 sri_g_size.
Qed.
Lemma sri_X9nk_rem n k : rmodp ('X^(9*n+k)) G=rmodp ('X^k) G.
Proof.
rewrite exprD -Pdiv.RingMonic.rmodp_mulml ?sri_g_monic //.
by rewrite sri_X9n_rem mul1r.
Qed.
Lemma sri_X6_rem : rmodp ('X^6) G = -'X^3-1.
Proof.
have he:('X^6:{poly int}) = 1*G+(-'X^3-1) by rewrite /sri_g mul1r -opprD -['X^6+'X^3+1]addrA addrK.
rewrite he Pdiv.RingMonic.rmodp_addl_mul_small ?sri_g_monic //.
apply:(leq_ltn_trans (size_add _ _)).
by rewrite size_opp size_polyXn size_opp size_poly1 sri_g_size.
Qed.
Lemma sri_phi_rem : rmodp (sri_phi [ringType of int]) G=(2:int)*:('X^3+1).
Proof.
rewrite /sri_phi Pdiv.RingMonic.rmodpD ?sri_g_monic // Pdiv.RingMonic.rmodpB ?sri_g_monic //.
have he768:768%N=(9*85+3)%N by [].
have he384:384%N=(9*42+6)%N by [].
rewrite he768 he384 !sri_X9nk_rem sri_X6_rem.
rewrite !rmodp_small ?size_polyXn ?size_poly1 ?sri_g_size //.
by rewrite scaler_nat mulr2n opprB opprK !addrA.
Qed.
Lemma sri_phi_not_ideal4 : forall Q R:{poly int},
 sri_phi [ringType of int] <> G*Q+(4:int)*:R.
Proof.
move=>q r he.
have h:=congr1 (fun p=>rmodp p G) he.
rewrite sri_phi_rem Pdiv.RingMonic.rmodpD ?sri_g_monic // in h.
rewrite [G*q]mulrC Pdiv.RingMonic.rmodp_mull ?sri_g_monic // add0r in h.
rewrite Pdiv.RingMonic.rmodpZ ?sri_g_monic // in h.
have hc:=congr1 (fun p:{poly int}=>p`_0) h.
rewrite !coefZ coefD coefXn coef1 /= add0r mulr1 in hc.
have hd:((4:int) %| (4*(rmodp r G)`_0))%Z by exact:dvdz_mulr.
by rewrite -hc in hd.
Qed.

Print Assumptions sri_phi_mod2.
Print Assumptions sri_phi_not_ideal4.
