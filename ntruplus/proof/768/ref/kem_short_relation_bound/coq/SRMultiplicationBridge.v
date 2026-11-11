Set Warnings "-notation-overridden,-notation-incompatible-prefix,-ambiguous-paths".
From Coq Require Import Lia ZArith.
From mathcomp Require Import all_ssreflect all_algebra word_ssrZ.
Require Import SRIrreducibleBase.
Require Import SRCountingBase.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ReducedMultiplication.
Variable F : fieldType.

Definition srm_poly n (v : nat -> F) : {poly F} :=
  \poly_(i < n) v i.

Definition srm_column n (d : {poly F}) (v : nat -> F) j : {poly F} :=
  ('X^j * srm_poly n v) %% d.

Definition srm_reduced_matrix n (d : {poly F}) (v : nat -> F) : 'M[F]_n :=
  \matrix_(k,j) (srm_column n d v j)`_k.

Lemma srm_poly_size n v : (size (srm_poly n v) <= n)%N.
Proof. exact: size_poly. Qed.

Lemma srm_poly_coefficient n v i : (i < n)%N -> (srm_poly n v)`_i = v i.
Proof. by move=> hi; rewrite /srm_poly coef_poly hi. Qed.

Lemma srm_poly_zero n v :
  srm_poly n v = 0 -> forall i, (i < n)%N -> v i = 0.
Proof.
move=> hz i hi; rewrite -(srm_poly_coefficient v hi) hz coef0.
by [].
Qed.

Lemma srm_mod_sum (d : {poly F}) (I : Type) (r : seq I) P f :
  (\sum_(i <- r | P i) f i) %% d = \sum_(i <- r | P i) (f i %% d).
Proof. exact: (big_morph (fun p : {poly F} => p %% d) (modpD d) (mod0p d)). Qed.

Lemma srm_product_columns n d v a :
 (srm_poly n a * srm_poly n v) %% d =
 \sum_(j < n) a j *: srm_column n d v j.
Proof.
rewrite {1}/srm_poly poly_def mulr_suml srm_mod_sum.
apply: eq_bigr => j _.
by rewrite -scalerAl modpZl.
Qed.

Lemma srm_reduced_matrix_kernel n (d : {poly F}) (v a : nat -> F) :
 size d = n.+1 ->
 (forall k : 'I_n, \sum_(j < n) srm_reduced_matrix n d v k j * a j = 0) ->
 (srm_poly n a * srm_poly n v) %% d = 0.
Proof.
move=> hd hk; apply/polyP=> k; rewrite coef0.
case: (ltnP k n) => hkn.
- rewrite srm_product_columns coef_sum.
  have := hk (Ordinal hkn).
  rewrite /=; apply: eq_trans _.
  apply: eq_bigr => j _.
  by rewrite coefZ mxE mulrC.
- apply: nth_default.
  apply: leq_trans (_ : n <= k)%N; last exact: hkn.
  have hdn : d != 0 by rewrite -size_poly_gt0 hd.
  have := ltn_modpN0 (srm_poly n a * srm_poly n v) hdn.
  by rewrite hd ltnS.
Qed.

Lemma srm_irreducible_product_kernel n (d : {poly F}) (v a : nat -> F) :
 size d = n.+1 -> irreducible_poly d -> srm_poly n v != 0 ->
 (srm_poly n a * srm_poly n v) %% d = 0 ->
 forall i, (i < n)%N -> a i = 0.
Proof.
move=> hd hir hv hm; apply: srm_poly_zero.
have hvsize : (size (srm_poly n v) < size d)%N.
  by rewrite hd ltnS; exact: srm_poly_size.
have hcop : coprimep d (srm_poly n v).
  by rewrite (irreducible_poly_coprime (srm_poly n v) hir) (gtNdvdp hv hvsize).
have hdiv : d %| srm_poly n a.
  rewrite -(Gauss_dvdpl (srm_poly n a) hcop).
  by apply/modp_eq0P.
case: (eqVneq (srm_poly n a) 0)=> [ha|ha]; first by [].
have hasize : (size (srm_poly n a) < size d)%N.
  by rewrite hd ltnS; exact: srm_poly_size.
by move: hdiv; rewrite (gtNdvdp ha hasize).
Qed.

Lemma srm_irreducible_matrix_kernel n (d : {poly F}) (v a : nat -> F) :
 size d = n.+1 -> irreducible_poly d -> srm_poly n v != 0 ->
 (forall k : 'I_n, \sum_(j < n) srm_reduced_matrix n d v k j * a j = 0) ->
 forall i, (i < n)%N -> a i = 0.
Proof.
move=> hd hir hv hk.
exact: (srm_irreducible_product_kernel hd hir hv (srm_reduced_matrix_kernel hd hk)).
Qed.

End ReducedMultiplication.

Section ConcreteReduction.
Variable F : fieldType.

Definition srm_reduced_monomial s : {poly F} :=
 if (s < 768)%N then 'X^s
 else if (s < 1152)%N then 'X^(s-384) - 'X^(s-768)
 else -'X^(s-1152).

Lemma srm_add_cancel (A B C : {poly F}) : A-B+C+(B-C)=A.
Proof. by rewrite addrA [A-B+C+B]addrAC subrK addrK. Qed.

Lemma srm_middle_decomposition s : (768 <= s)%N ->
 ('X^s : {poly F}) = 'X^(s-768)*sri_phi F + ('X^(s-384)-'X^(s-768)).
Proof.
move/leP=> hs.
have h1 : ((s-768)+768=s)%N by rewrite -!plusE -!minusE;lia.
have h2 : ((s-768)+384=s-384)%N by rewrite -!plusE -!minusE;lia.
by rewrite /sri_phi mulrDr mulrBr mulr1 -!exprD h1 h2 srm_add_cancel.
Qed.

Lemma srm_middle_mod s : (768 <= s)%N ->
 ('X^s : {poly F}) %% sri_phi F = ('X^(s-384)-'X^(s-768)) %% sri_phi F.
Proof.
move=> hs; rewrite {1}(srm_middle_decomposition hs).
by rewrite modpD modp_mull add0r.
Qed.

Lemma srm_monomial_mod s : (s < 1536)%N ->
 ('X^s : {poly F}) %% sri_phi F = srm_reduced_monomial s.
Proof.
move=> hs; rewrite /srm_reduced_monomial.
case: ifP=> hlo.
- apply: modp_small; by rewrite size_polyXn sri_phi_size ltnS.
have h768 : (768 <= s)%N by rewrite leqNgt hlo.
rewrite (srm_middle_mod h768).
case: ifP=> hmid.
- apply: modp_small.
  apply: leq_ltn_trans (size_add _ _) _.
  rewrite size_opp !size_polyXn sri_phi_size gtn_max.
  apply/andP;split;apply/ltP;move/ltP:hmid;move/leP:h768;
    rewrite -!minusE;lia.
- rewrite modpD modpN.
  have hm : (768 <= s-384)%N.
    have h1152 : (1152 <= s)%N by rewrite leqNgt hmid.
    apply/leP;move/leP:h1152;rewrite -!minusE;lia.
  rewrite (srm_middle_mod hm) modpD modpN.
  have h1 : (s-384-384=s-768)%N by rewrite -!minusE;lia.
  have h2 : (s-384-768=s-1152)%N by rewrite -!minusE;lia.
  rewrite h1 h2 addrAC subrr add0r.
  congr (- _).
  apply: modp_small;rewrite size_polyXn sri_phi_size.
  apply/ltP;move/ltP:hs;rewrite -!minusE;lia.
Qed.

Definition srm_weight k s : F :=
 if (s < 768)%N then (k == s)%:R
 else if (s < 1152)%N then (k == (s-384)%N)%:R - (k == (s-768)%N)%:R
 else - (k == (s-1152)%N)%:R.

Lemma srm_reduced_monomial_coefficient k s :
 (srm_reduced_monomial s)`_k = srm_weight k s.
Proof.
rewrite /srm_reduced_monomial /srm_weight.
by case: ifP=> _; [rewrite coefXn |case: ifP=> _;rewrite ?coefD ?coefN !coefXn].
Qed.

Definition srm_convolution (a v : nat -> F) k :=
 \sum_(i < 768) \sum_(j < 768) a i * v j * srm_weight k (i+j)%N.

Lemma srm_product_remainder_coefficient a v k :
 ((srm_poly 768 a * srm_poly 768 v) %% sri_phi F)`_k =
 srm_convolution a v k.
Proof.
rewrite srm_product_columns coef_sum /srm_convolution.
apply: eq_bigr=> i _;rewrite coefZ.
rewrite /srm_column /srm_poly poly_def mulr_sumr srm_mod_sum coef_sum mulr_sumr.
apply: eq_bigr=> j _.
rewrite -scalerAr modpZl coefZ -exprD.
have hij : (i+j < 1536)%N.
  apply/ltP;move/ltP:(ltn_ord i);move/ltP:(ltn_ord j);rewrite -plusE;lia.
by rewrite (srm_monomial_mod hij) srm_reduced_monomial_coefficient mulrA.
Qed.

Lemma srm_convolution_kernel (v a : nat -> F) :
 irreducible_poly (sri_phi F) -> srm_poly 768 v != 0 ->
 (forall k,(k < 768)%N -> srm_convolution a v k = 0) ->
 forall i,(i < 768)%N -> a i = 0.
Proof.
move=> hir hv hk.
apply: (srm_irreducible_product_kernel (sri_phi_size F) hir hv).
apply/polyP=> k;rewrite coef0.
case: (ltnP k 768)=> hk768.
- by rewrite srm_product_remainder_coefficient hk.
- apply: nth_default; apply: leq_trans hk768.
  have hd : sri_phi F != 0 by rewrite -size_poly_gt0 sri_phi_size.
  have := ltn_modpN0 (srm_poly 768 a*srm_poly 768 v) hd.
  by rewrite sri_phi_size ltnS.
Qed.

End ConcreteReduction.

Definition srm_rat (z : Z) : rat := (Z_to_int z)%:~R.

Lemma srm_rat_injective : injective srm_rat.
Proof. move=> x y h;apply:(can_inj Z_to_intK);apply:intr_inj;exact:h. Qed.

Lemma srm_rat0 : srm_rat 0 = 0.
Proof. by rewrite /srm_rat rmorph0. Qed.
Lemma srm_rat1 : srm_rat 1 = 1.
Proof. by rewrite /srm_rat rmorph1. Qed.
Lemma srm_ratM x y : srm_rat (Z.mul x y) = srm_rat x*srm_rat y.
Proof. by rewrite /srm_rat rmorphM intrM. Qed.
Lemma srm_ratN x : srm_rat (Z.opp x) = -srm_rat x.
Proof. by rewrite /srm_rat !rmorphN. Qed.
Lemma srm_ratB x y : srm_rat (Z.sub x y) = srm_rat x-srm_rat y.
Proof. by rewrite /srm_rat !rmorphB. Qed.

Lemma srm_rat_sum n f :
 srm_rat(sr_Zsum n f)=\sum_(i<n) srm_rat(f(Z.of_nat(val i))).
Proof. by rewrite sr_Zsum_big /srm_rat !rmorph_sum. Qed.

Definition srm_Zbit (b:bool) : Z := if b then 1%Z else 0%Z.
Definition srm_Zweight (k s:Z) : Z :=
 if Z.ltb s 768 then srm_Zbit(Z.eqb k s)
 else if Z.ltb s 1152 then
  Z.sub(srm_Zbit(Z.eqb k (Z.sub s 384)))(srm_Zbit(Z.eqb k (Z.sub s 768)))
 else Z.opp(srm_Zbit(Z.eqb k (Z.sub s 1152))).

Lemma srm_Zlt_nat m n : Z.ltb(Z.of_nat m)(Z.of_nat n)=(m<n)%N.
Proof. by case:ltP;case:Z.ltb_spec;lia. Qed.
Lemma srm_Zeq_nat m n : Z.eqb(Z.of_nat m)(Z.of_nat n)=(m==n).
Proof. by case:eqP;case:Z.eqb_spec;lia. Qed.
Lemma srm_Zsub_nat m n : (n<=m)%N->Z.sub(Z.of_nat m)(Z.of_nat n)=Z.of_nat(m-n).
Proof. move/leP=>hm;rewrite -minusE Nat2Z.inj_sub;lia. Qed.

Lemma srm_Zbit_rat b : srm_rat(srm_Zbit b)=b%:R.
Proof. by case:b;rewrite /srm_Zbit ?srm_rat0 ?srm_rat1. Qed.

Lemma srm_Zweight_rat k s :
 srm_rat(srm_Zweight(Z.of_nat k)(Z.of_nat s))=srm_weight [fieldType of rat] k s.
Proof.
rewrite /srm_Zweight /srm_weight.
rewrite (srm_Zlt_nat s 768);case:ifP=>hlo.
- by rewrite srm_Zbit_rat srm_Zeq_nat.
have h768:(768<=s)%N by rewrite leqNgt hlo.
rewrite (srm_Zlt_nat s 1152);case:ifP=>hmid.
- rewrite srm_ratB !srm_Zbit_rat.
  rewrite (srm_Zsub_nat h768) (srm_Zsub_nat (_ : (384<=s)%N)) ?srm_Zeq_nat //.
  exact: leq_trans h768.
- have h1152:(1152<=s)%N by rewrite leqNgt hmid.
  by rewrite srm_ratN srm_Zbit_rat (srm_Zsub_nat h1152) srm_Zeq_nat.
Qed.

Definition srm_Zconvolution (a v:Z->Z)(k:Z) : Z :=
 sr_Zsum 768(fun i=>sr_Zsum 768(fun j=>
  Z.mul(Z.mul(a i)(v j))(srm_Zweight k (Z.add i j)))).

Lemma srm_Zconvolution_rat a v k :
 srm_rat(srm_Zconvolution a v (Z.of_nat k))=
 @srm_convolution [fieldType of rat]
  (fun i=>srm_rat(a(Z.of_nat i)))(fun j=>srm_rat(v(Z.of_nat j)))k.
Proof.
rewrite /srm_Zconvolution /srm_convolution srm_rat_sum.
apply:eq_bigr=>i _;rewrite srm_rat_sum.
apply:eq_bigr=>j _.
rewrite !srm_ratM.
have he:Z.add(Z.of_nat(val i))(Z.of_nat(val j))=Z.of_nat(i+j)%N.
  by rewrite -plusE Nat2Z.inj_add.
by rewrite he srm_Zweight_rat.
Qed.

Lemma srm_Zpoly_nonzero (v:Z->Z) :
 (exists i, (Z.le 0 i /\ Z.lt i 768) /\ v i<>Z.zero) ->
 srm_poly 768(fun i=>srm_rat(v(Z.of_nat i)))!=0.
Proof.
move=>[i [[hi0 hi768]hvi]];apply/negP=>/eqP hp.
have hin:(Z.to_nat i<768)%N by apply/ltP;lia.
have hc:=srm_poly_zero hp hin.
rewrite Z2Nat.id // in hc.
apply:hvi;apply:srm_rat_injective;by rewrite srm_rat0.
Qed.

Definition srm_phi_irreducible : Prop := irreducible_poly(sri_phi [ringType of rat]).

Lemma srm_Zconvolution_kernel (v a:Z->Z) :
 srm_phi_irreducible ->
 (exists i,(Z.le 0 i /\ Z.lt i 768) /\ v i<>Z.zero) ->
 (forall k,(Z.le 0 k /\ Z.lt k 768) -> srm_Zconvolution a v k=Z.zero) ->
 forall i,(Z.le 0 i /\ Z.lt i 768) -> a i=Z.zero.
Proof.
move=> hir hv hk i [hi0 hi768].
have hn:=srm_Zpoly_nonzero hv.
have ha:forall j,(j<768)%N->srm_rat(a(Z.of_nat j))=0.
  apply:(srm_convolution_kernel hir hn)=>k hkn.
  rewrite -srm_Zconvolution_rat.
  have hkz:(Z.le 0 (Z.of_nat k) /\ Z.lt (Z.of_nat k) 768) by move/ltP:hkn;lia.
  by rewrite (hk _ hkz) srm_rat0.
have hin:(Z.to_nat i<768)%N by apply/ltP;lia.
have he:=ha (Z.to_nat i)hin.
rewrite Z2Nat.id // in he.
apply:srm_rat_injective;by rewrite srm_rat0.
Qed.

Print Assumptions srm_Zconvolution_kernel.
