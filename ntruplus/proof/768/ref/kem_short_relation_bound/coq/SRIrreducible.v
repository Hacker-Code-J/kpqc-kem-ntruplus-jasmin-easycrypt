From mathcomp Require Import all_ssreflect all_algebra.
Require Export SRIrreducibleBase.
Require Import SRIrreducibleRing SRIrreducibleFactor SRIrreducibleConcrete.
From Coq Require Import Ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Lemma sri_f2_cases (x : bool) : x = 0 \/ x = 1.
Proof. by case: x; [right|left]. Qed.

Lemma sri_poly4 (p : {poly bool}) : (size p <= 4)%N ->
 p = Poly [:: p`_0; p`_1; p`_2; p`_3].
Proof.
move=> hp; apply/polyP=> i; rewrite coef_Poly.
case: i => [|[|[|[|i]]]] //=.
rewrite nth_nil nth_default //.
by apply: (leq_trans hp).
Qed.

Definition sri_p7 : {poly bool} := 'X^2 + 'X + 1.
Definition sri_p11 : {poly bool} := 'X^3 + 'X + 1.
Definition sri_p13 : {poly bool} := 'X^3 + 'X^2 + 1.

Lemma sri_bezout7 : sri_g [ringType of bool] + ('X^4+'X^3)*sri_p7 = 1.
Proof. exact: sri_bezout7_alg. Qed.
Lemma sri_bezout11 : 'X^2*sri_g [ringType of bool] +
 ('X^5+'X^3+'X+1)*sri_p11 = 1.
Proof. exact: sri_bezout11_alg. Qed.
Lemma sri_bezout13 : ('X^2+'X)*sri_g [ringType of bool] +
 ('X^5+'X+1)*sri_p13 = 1.
Proof. exact: sri_bezout13_alg. Qed.

Lemma sri_coprime7 : coprimep sri_p7 (sri_g [ringType of bool]).
Proof.
apply/Bezout_eq1_coprimepP; exists ('X^4+'X^3,1).
by rewrite /= mul1r addrC; exact: sri_bezout7.
Qed.
Lemma sri_coprime11 : coprimep sri_p11 (sri_g [ringType of bool]).
Proof.
apply/Bezout_eq1_coprimepP; exists ('X^5+'X^3+'X+1,'X^2).
by rewrite /= addrC; exact: sri_bezout11.
Qed.
Lemma sri_coprime13 : coprimep sri_p13 (sri_g [ringType of bool]).
Proof.
apply/Bezout_eq1_coprimepP; exists ('X^5+'X+1,'X^2+'X).
by rewrite /= addrC; exact: sri_bezout13.
Qed.

Lemma sri_coprime_divisor_constant (p q : {poly bool}) :
 coprimep p q -> p %| q -> (size p <= 1)%N.
Proof.
move=> hc hd; have h := coprimep_dvdl hd hc.
by move: h; rewrite coprimepp => /eqP ->.
Qed.

Lemma sri_g_root_free (x : bool) : ~~ root (sri_g [ringType of bool]) x.
Proof. by case: x; rewrite /sri_g /root !hornerE /=. Qed.
Lemma sri_g_divisor_root (p : {poly bool}) x :
 p %| sri_g [ringType of bool] -> ~~ root p x.
Proof.
move=> hd; apply/negP=> hr.
have hg : root (sri_g [ringType of bool]) x.
  rewrite -dvdp_XsubCl; apply: (dvdp_trans _ hd).
  by rewrite dvdp_XsubCl.
by move: (sri_g_root_free x); rewrite hg.
Qed.

Lemma sri_poly4_horner (p : {poly bool}) : (size p <= 4)%N ->
 p = (((p`_3)%:P*'X+(p`_2)%:P)*'X+(p`_1)%:P)*'X+(p`_0)%:P.
Proof.
move=> hp; transitivity (Poly [:: p`_0; p`_1; p`_2; p`_3]).
- exact: sri_poly4.
by rewrite /Poly /= !cons_poly_def !mul0r !add0r.
Qed.

Lemma sri_g_no_small_divisor (p : {poly bool}) :
 (size p <= 4)%N -> p %| sri_g [ringType of bool] -> (size p <= 1)%N.
Proof.
move=> hp hd.
pose a0 := p`_0; pose a1 := p`_1; pose a2 := p`_2; pose a3 := p`_3.
have hpE : p = ((a3%:P*'X+a2%:P)*'X+a1%:P)*'X+a0%:P
 by exact: sri_poly4_horner.
have rz := sri_g_divisor_root false hd.
have ro := sri_g_divisor_root true hd.
rewrite hpE /root !hornerE /= in rz ro.
rewrite hpE in hd; rewrite hpE.
clearbody a0 a1 a2 a3; clear hpE hp p.
move: hd rz ro.
case: a0; case: a1; case: a2; case: a3 => //=.
all: change false%:P with (0 : {poly bool}); change true%:P with (1 : {poly bool}).
all: rewrite ?mul0r ?add0r ?mul1r ?addr0.
- have -> : ('X+1)*'X+1 = sri_p7 by exact: sri_horner7_alg.
  move=> hd _ _; exact: (sri_coprime_divisor_constant sri_coprime7 hd).
- have -> : ('X*'X+1)*'X+1 = sri_p11 by exact: sri_horner11_alg.
  move=> hd _ _; exact: (sri_coprime_divisor_constant sri_coprime11 hd).
- have -> : ('X+1)*'X*'X+1 = sri_p13 by exact: sri_horner13_alg.
  move=> hd _ _; exact: (sri_coprime_divisor_constant sri_coprime13 hd).
by rewrite ?mul0r ?add0r ?mul0r ?add0r ?mul0r ?add0r size_poly1.
Qed.

Lemma sri_positive_le_one n : (0<n)%N -> (n<=1)%N -> n = 1%N.
Proof. by case: n => [|[|n]]. Qed.
Lemma sri_factor_complement_small s t :
 (4<s)%N -> 7%N=((t+s)%N).-1 -> (t<=4)%N.
Proof.
case: s => [|[|[|[|[|s]]]]] //=.
case: t => [|[|[|[|[|t]]]]] //=.
by rewrite -addnE !addnS.
Qed.

Lemma sri_g_irred_mod2 : irreducible_poly (sri_g [ringType of bool]).
Proof.
split; first by rewrite sri_g_size.
move=> d dsize ddiv.
have gnz : sri_g [ringType of bool] != 0
 by rewrite -size_poly_gt0 sri_g_size.
have dd := ddiv; move/dvdpP: dd => [e he].
have nz : e*d != 0 by rewrite -he.
move: nz; rewrite mulf_eq0 negb_or => /andP [enz dnz].
have sizes := congr1 (fun p : {poly bool} => size p) he.
rewrite sri_g_size (size_mul enz dnz) in sizes.
have dp : (0 < size d)%N by rewrite size_poly_gt0.
have ep : (0 < size e)%N by rewrite size_poly_gt0.
have [ds|db] := leqP (size d) 4.
- have dc := sri_g_no_small_divisor ds ddiv.
  have sd1 := sri_positive_le_one dp dc.
  by move: dsize; rewrite sd1 eqxx.
have es : (size e <= 4)%N by exact: (sri_factor_complement_small db sizes).
have ediv : e %| sri_g [ringType of bool].
  rewrite he; apply: dvdp_mulr; exact: dvdpp.
have ec := sri_g_no_small_divisor es ediv.
have es1 : size e = 1%N by exact: (sri_positive_le_one ep ec).
have ds7 : size d = 7%N.
  by move: sizes; rewrite es1 add1n /= => <-.
by rewrite -(dvdp_size_eqp ddiv) sri_g_size ds7 eqxx.
Qed.


Lemma sri_mapQ_phi : sri_mapQ (sri_phi [ringType of int]) =
 sri_phi [ringType of rat].
Proof.
by rewrite /sri_mapQ /sri_phi !rmorphD ?rmorphB ?rmorphN !rmorphXn rmorph1 /= map_polyX.
Qed.

Theorem sri_phi_irreducible_Q :
 irreducible_poly (sri_phi [ringType of rat]).
Proof.
rewrite -sri_mapQ_phi.
apply: (@sri_schoenemann (sri_phi [ringType of int]) (sri_g [ringType of int]) 128).
- by rewrite sri_phi_size.
- exact: sri_phi_monic.
- by rewrite sri_map2_g; exact: sri_g_irred_mod2.
- by rewrite sri_map2_g; exact: sri_phi_mod2.
- exact: sri_phi_not_ideal4.
Qed.

Print Assumptions sri_g_irred_mod2.
Print Assumptions sri_phi_irreducible_Q.
