Set Warnings "-notation-overridden,-notation-incompatible-prefix,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra.
From Coq Require Import ZArith.
From mathcomp.word Require Import word_ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma sr_kernel_det_nonzero (R : idomainType) n (A : 'M[R]_n) :
 (forall x : 'cV[R]_n, A *m x = 0 -> x = 0) -> \det A != 0.
Proof.
move=> hk; apply/negP => hz.
have ht : \det A^T == 0 by rewrite det_tr.
move/det0P: ht => [v hv hzero].
have hc : A *m v^T = 0.
  have := congr1 trmx hzero.
  by rewrite trmx_mul trmxK trmx0.
have hv0 := hk _ hc.
move: hv; rewrite -(trmxK v) hv0 trmx0 eqxx.
by [].
Qed.

Lemma sr_integer_kernel_det_nonzero n (A : 'M[int]_n) :
 (forall x : 'cV[int]_n, A *m x = 0 -> x = 0) -> \det A != 0.
Proof. exact: sr_kernel_det_nonzero. Qed.

Lemma sr_Z_kernel_det_nonzero n (A : 'M[Z]_n) :
 (forall x : 'cV[Z]_n, A *m x = 0 -> x = 0) -> \det A != 0.
Proof. exact: sr_kernel_det_nonzero. Qed.
