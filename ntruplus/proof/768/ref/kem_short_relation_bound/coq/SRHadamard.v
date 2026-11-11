From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section GramHadamard.
Variable F : realFieldType.

Definition sr_gram {m n : nat} (A : 'M[F]_(m,n)) := A *m A^T.
Definition sr_row_sqnorm {m n : nat} (A : 'M[F]_(m,n)) (i : 'I_m) :=
  \sum_(j < n) (A i j)^+2.

Lemma sr_row_sqnorm_ge0 m n (A : 'M[F]_(m,n)) i :
  0 <= sr_row_sqnorm A i.
Proof. apply: sumr_ge0 => j _; exact: sqr_ge0. Qed.

Lemma sr_gram_diag m n (A : 'M[F]_(m,n)) i :
  sr_gram A i i = sr_row_sqnorm A i.
Proof.
rewrite /sr_gram /sr_row_sqnorm mxE.
apply: eq_bigr => j _; by rewrite mxE expr2.
Qed.

Lemma sr_row_sqnorm_zero m n (A : 'M[F]_(m,n)) i :
  sr_row_sqnorm A i = 0 -> row i A = 0.
Proof.
move=> hz; apply/matrixP => x j; rewrite !mxE.
have h := @psumr_eq0P F _ predT (fun j : 'I_n => (A i j)^+2).
have hj : (A i j)^+2 = 0.
  apply: h => // k _; exact: sqr_ge0.
by move/eqP: hj; rewrite sqrf_eq0 => /eqP.
Qed.

Definition sr_dot {n} (u v : 'rV[F]_n) := (u *m v^T) 0 0.
Lemma sr_dotE n (u v : 'rV[F]_n) : sr_dot u v = \sum_j u 0 j * v 0 j.
Proof. rewrite /sr_dot mxE; apply: eq_bigr=>j _;by rewrite mxE. Qed.
Lemma sr_dot_sym n (u v : 'rV[F]_n) : sr_dot u v = sr_dot v u.
Proof. rewrite !sr_dotE;apply:eq_bigr=>j _;exact:mulrC. Qed.
Lemma sr_dot_self n (u : 'rV[F]_n) : sr_dot u u = sr_row_sqnorm u 0.
Proof. rewrite sr_dotE /sr_row_sqnorm;apply:eq_bigr=>j _;by rewrite expr2. Qed.
Lemma sr_dotBl n (u v w : 'rV[F]_n) : sr_dot (u-v) w=sr_dot u w-sr_dot v w.
Proof. by rewrite /sr_dot mulmxBl !mxE. Qed.
Lemma sr_dotZl n c (u v : 'rV[F]_n) : sr_dot (c*:u) v=c*sr_dot u v.
Proof. by rewrite /sr_dot -scalemxAl !mxE. Qed.
Lemma sr_dotBr n (u v w : 'rV[F]_n) : sr_dot u (v-w)=sr_dot u v-sr_dot u w.
Proof. by rewrite sr_dot_sym sr_dotBl [sr_dot v u]sr_dot_sym [sr_dot w u]sr_dot_sym. Qed.
Lemma sr_dotZr n c (u v : 'rV[F]_n) : sr_dot u (c*:v)=c*sr_dot u v.
Proof. by rewrite sr_dot_sym sr_dotZl sr_dot_sym. Qed.

Definition sr_project_row {n} (u v : 'rV[F]_n) := v-(sr_dot v u / sr_dot u u)*:u.
Lemma sr_project_row_sq n (u v : 'rV[F]_n) : sr_dot u u != 0 ->
 sr_dot (sr_project_row u v) (sr_project_row u v)=
 sr_dot v v-(sr_dot v u)^+2/sr_dot u u.
Proof.
move=> hu;rewrite /sr_project_row sr_dotBl !sr_dotBr !sr_dotZl !sr_dotZr.
rewrite [sr_dot u v]sr_dot_sym expr2 (divfK hu) subrr subr0.
by rewrite mulrAC.
Qed.

Lemma sr_dot_self_ge0 n (u : 'rV[F]_n) : 0 <= sr_dot u u.
Proof. rewrite sr_dot_self;exact:sr_row_sqnorm_ge0. Qed.
Lemma sr_dot_self_zero n (u : 'rV[F]_n) : sr_dot u u=0 -> u=0.
Proof. rewrite sr_dot_self=>h;move:(sr_row_sqnorm_zero h);by rewrite row_id. Qed.
Lemma sr_dot_row m n (B:'M[F]_(m,n)) i (u:'rV[F]_n) :
 sr_dot (row i B) u=(B *m u^T) i 0.
Proof. by rewrite /sr_dot -row_mul mxE. Qed.
Lemma sr_row_sqnorm_row m n (B:'M[F]_(m,n)) i :
 sr_row_sqnorm (row i B) 0=sr_row_sqnorm B i.
Proof. rewrite /sr_row_sqnorm;apply:eq_bigr=>j _;by rewrite mxE. Qed.

Definition sr_proj_coeff {m n} (u:'rV[F]_n) (B:'M[F]_(m,n)) :=
 (sr_dot u u)^-1 *: (B *m u^T).
Definition sr_residual {m n} (u:'rV[F]_n) (B:'M[F]_(m,n)) := B - sr_proj_coeff u B *m u.
Lemma sr_residual_row m n (u:'rV[F]_n) (B:'M[F]_(m,n)) i :
 row i (sr_residual u B)=sr_project_row u (row i B).
Proof.
apply/rowP=>j;rewrite /sr_residual /sr_project_row /sr_proj_coeff !mxE big_ord1 !mxE sr_dot_row.
rewrite !mxE;congr (_-_);congr (_*_);exact:mulrC.
Qed.
Lemma sr_residual_norm_le m n (u:'rV[F]_n) (B:'M[F]_(m,n)) i :
 0<sr_dot u u -> sr_row_sqnorm (sr_residual u B) i <= sr_row_sqnorm B i.
Proof.
move=>hu;have hn:sr_dot u u != 0 by exact:lt0r_neq0.
rewrite -[sr_row_sqnorm (sr_residual u B) i]sr_row_sqnorm_row sr_residual_row
 -sr_dot_self (@sr_project_row_sq n u (row i B) hn) sr_dot_self sr_row_sqnorm_row.
rewrite lerBlDl;apply:ler_wpDl=>//;apply:divr_ge0;[exact:sqr_ge0|exact:ltW].
Qed.
Lemma sr_residual_orthogonal m n (u:'rV[F]_n) (B:'M[F]_(m,n)) :
 sr_dot u u != 0 -> sr_residual u B *m u^T=0.
Proof.
move=>hu;rewrite /sr_residual mulmxBl -mulmxA [u *m u^T]mx11_scalar -/sr_dot
 mul_mx_scalar /sr_proj_coeff scalerA (mulfV hu) scale1r subrr;done.
Qed.
Definition sr_elim {m n} (u:'rV[F]_n) (B:'M[F]_(m,n)) : 'M[F]_(1+m) :=
 block_mx 1%:M 0 (-sr_proj_coeff u B) 1%:M.
Lemma sr_elim_det m n (u:'rV[F]_n) (B:'M[F]_(m,n)) : \det(sr_elim u B)= 1.
Proof. by rewrite /sr_elim det_lblock !det1 mulr1. Qed.
Lemma sr_elim_action m n (u:'rV[F]_n) (B:'M[F]_(m,n)) :
 sr_elim u B *m col_mx u B=col_mx u (sr_residual u B).
Proof.
rewrite /sr_elim mul_block_col mul1mx mul0mx addr0 mulNmx mul1mx /sr_residual.
by rewrite addrC.
Qed.
Lemma sr_gram_left m n (L:'M[F]_m) (A:'M[F]_(m,n)) :
 sr_gram(L *m A)=L *m sr_gram A *m L^T.
Proof. by rewrite /sr_gram trmx_mul !mulmxA. Qed.
Lemma sr_gram_orthogonal m n (u:'rV[F]_n) (B:'M[F]_(m,n)) :
 B *m u^T=0 -> \det(sr_gram(col_mx u B))=sr_dot u u* \det(sr_gram B).
Proof.
move=>hb;have ht:u *m B^T=0.
  apply:trmx_inj;by rewrite trmx_mul trmxK hb trmx0.
by rewrite /sr_gram tr_col_mx mul_col_row hb ht det_lblock det_mx11 /sr_dot.
Qed.
Lemma sr_gram_projection m n (u:'rV[F]_n) (B:'M[F]_(m,n)) :
 sr_dot u u != 0 ->
 \det(sr_gram(col_mx u B))=sr_dot u u* \det(sr_gram(sr_residual u B)).
Proof.
move=>hu.
have he: \det(sr_gram(sr_elim u B *m col_mx u B))= \det(sr_gram(col_mx u B)).
  by rewrite sr_gram_left !det_mulmx det_tr sr_elim_det mul1r mulr1.
rewrite sr_elim_action (@sr_gram_orthogonal m n u (sr_residual u B) (@sr_residual_orthogonal m n u B hu)) in he.
exact:esym he.
Qed.

Lemma sr_row_sqnorm_col_u m n (u:'rV[F]_n) (B:'M[F]_(m,n)) (i:'I_1) :
 sr_row_sqnorm(col_mx u B)(lshift m i)=sr_row_sqnorm u i.
Proof. rewrite /sr_row_sqnorm;apply:eq_bigr=>j _;by rewrite col_mxEu. Qed.
Lemma sr_row_sqnorm_col_d m n (u:'rV[F]_n) (B:'M[F]_(m,n)) i :
 sr_row_sqnorm(col_mx u B)(rshift 1 i)=sr_row_sqnorm B i.
Proof. rewrite /sr_row_sqnorm;apply:eq_bigr=>j _;by rewrite col_mxEd. Qed.
Lemma sr_norm_product_col m n (u:'rV[F]_n) (B:'M[F]_(m,n)) :
 \prod_i sr_row_sqnorm(col_mx u B)i=sr_dot u u* \prod_i sr_row_sqnorm B i.
Proof.
rewrite big_split_ord big_ord1 sr_row_sqnorm_col_u -sr_dot_self.
congr (_*_);apply:eq_bigr=>i _;exact:sr_row_sqnorm_col_d.
Qed.
Lemma sr_gram_col_zero m n (B:'M[F]_(m,n)) :
 \det(sr_gram(col_mx (0:'rV[F]_n) B))=0.
Proof.
by rewrite /sr_gram tr_col_mx trmx0 mul_col_row !mul0mx !mulmx0 det_lblock det0 mul0r.
Qed.

Theorem sr_gram_hadamard m n (A:'M[F]_(m,n)) :
 \det(sr_gram A)<= \prod_i sr_row_sqnorm A i.
Proof.
elim:m A=>[|m IH] A;first by rewrite det_mx00 big_ord0.
pose u : 'rV[F]_n := @usubmx F 1 m n A.
pose B : 'M[F]_(m,n) := @dsubmx F 1 m n A.
have hA:A=col_mx u B by rewrite /u /B vsubmxK.
rewrite hA sr_norm_product_col.
have hd:0<=sr_dot u u by exact:sr_dot_self_ge0.
have [hu|hu]:=eqVneq (sr_dot u u) 0.
- have hz:u=0 by exact:sr_dot_self_zero hu.
  by rewrite hu mul0r hz sr_gram_col_zero.
have hp:0<sr_dot u u by rewrite lt_neqAle eq_sym hu hd.
rewrite(@sr_gram_projection m n u B hu).
apply:(le_trans (ler_wpM2l hd (IH (sr_residual u B)))).
apply:ler_wpM2l=>//;apply:ler_prod=>i _;apply/andP;split.
- exact:sr_row_sqnorm_ge0.
exact:(@sr_residual_norm_le m n u B i hp).
Qed.

Theorem sr_hadamard_square n (A:'M[F]_n) :
 (\det A)^+2<= \prod_i sr_row_sqnorm A i.
Proof.
have h:=sr_gram_hadamard A.
by move:h;rewrite /sr_gram det_mulmx det_tr expr2.
Qed.

End GramHadamard.

From Coq Require Import ZArith.
From mathcomp Require Import word_ssrZ.
Local Open Scope ring_scope.

Definition sr_Zrat : {rmorphism Z -> rat} := [rmorphism of (intr \o Z_to_int)].
Lemma sr_Zrat_le (x y:Z) : (sr_Zrat x <= sr_Zrat y)=(x<=y).
Proof.
rewrite /sr_Zrat /= ler_int.
by apply/idP/idP; [move/leZE/lezP|move/lezP/leZE].
Qed.
Definition sr_Z_row_sqnorm {m n} (A:'M[Z]_(m,n)) (i:'I_m) :=
 \sum_(j<n) A i j * A i j.
Lemma sr_Zrat_row m n (A:'M[Z]_(m,n)) i :
 sr_row_sqnorm(map_mx sr_Zrat A)i=sr_Zrat(sr_Z_row_sqnorm A i).
Proof.
rewrite /sr_row_sqnorm /sr_Z_row_sqnorm rmorph_sum.
apply:eq_bigr=>j _;by rewrite mxE expr2 rmorphM.
Qed.
Lemma sr_Z_row_sqnorm_ge0 m n (A:'M[Z]_(m,n)) i :
 0<=sr_Z_row_sqnorm A i.
Proof. apply:sumr_ge0=>j _;by rewrite -expr2 sqr_ge0. Qed.
Theorem sr_hadamard_Z_square n (A:'M[Z]_n) :
 (\det A)^+2 <= \prod_i sr_Z_row_sqnorm A i.
Proof.
have h:=sr_hadamard_square (map_mx sr_Zrat A).
rewrite det_map_mx in h.
have he:(\prod_i sr_row_sqnorm(map_mx sr_Zrat A)i)=sr_Zrat(\prod_i sr_Z_row_sqnorm A i).
  rewrite rmorph_prod /=;apply:eq_bigr=>i _;exact:sr_Zrat_row.
by move:h;rewrite he -rmorphXn sr_Zrat_le.
Qed.
Theorem sr_hadamard_Z_rows n (A:'M[Z]_n) (bound:Z) :
 (forall i, sr_Z_row_sqnorm A i<=bound) -> (\det A)^+2<=bound^+n.
Proof.
move=>hb;apply:(le_trans (sr_hadamard_Z_square A)).
have h:(\prod_i sr_Z_row_sqnorm A i)<=(\prod_(i:'I_n) bound).
  apply:ler_prod=>i _;apply/andP;split;[exact:sr_Z_row_sqnorm_ge0|exact:hb].
by move:h;rewrite prodr_const card_ord.
Qed.
Theorem sr_hadamard_Z768_square (A:'M[Z]_768) :
 (forall i, (\sum_j A i j*A i j <= 12288)%Z) ->
 ((\det A)*(\det A) <= Z.pow 12288 768)%Z.
Proof.
move=>hb;have h:(\det A)^+2 <= (12288:Z)^+768.
  apply:sr_hadamard_Z_rows=>i;apply/lezP;exact:hb.
apply/lezP;rewrite -(expZE 12288 768) in h.
by move:h;rewrite expr2.
Qed.
Theorem sr_hadamard_Z768 (A:'M[Z]_768) :
 (forall i, (\sum_j A i j*A i j <= 12288)%Z) ->
 (Z.abs(\det A) <= Z.pow 12288 384)%Z.
Proof.
move=>hb.
have hsq:(\det A)^+2 <= (12288:Z)^+768.
  apply:sr_hadamard_Z_rows=>i;apply/lezP;exact:hb.
have hp:0<=(12288:Z)^+384 by apply:exprn_ge0;by [].
have hn:0<=`|\det A| by exact:normr_ge0.
have he:(`|\det A|)^+2<=((12288:Z)^+384)^+2.
  by rewrite -normrX ger0_norm ?sqr_ge0 // -exprM;exact:hsq.
have hle:`|\det A|<=(12288:Z)^+384.
  by move:he;rewrite ler_sqr.
apply/lezP;rewrite (expZE 12288 384);exact:hle.
Qed.

Print Assumptions sr_gram_hadamard.
Print Assumptions sr_hadamard_Z768.
