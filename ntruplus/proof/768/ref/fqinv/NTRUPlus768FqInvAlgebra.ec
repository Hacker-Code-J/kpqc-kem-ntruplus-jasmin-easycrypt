require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import NTRUPlus768BasemulProof.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768FqInvPrime.

import Ring.IntID IntOrder.

(* Exact word-level value specification of the fqinv addition chain.  The
   authoritative C body is checked separately; no C/Jasmin procedure equivalence
   is claimed here.  Indexed states keep the repeated-squaring trace shared. *)

op fq_rinv_word : W16.t = W16.of_int (-682).

op fqmul_word_spec (a b : W16.t) : W16.t =
  NTRUPlus768BasemulProof.montgomery_reduce
    (NTRUPlus768BasemulProof.mul_i16 a b).

op fqinv_word_left
    (a : W16.t) (state : int -> W16.t) (i : int) : W16.t =
  if i = 0 then a else
  if i = 1 then state 0 else
  if i = 2 then state 1 else
  if i = 3 then state 2 else
  if i = 4 then state 0 else
  if i = 5 then state 4 else
  if i = 6 then state 5 else
  if i = 7 then state 6 else
  if i = 8 then state 4 else
  if i = 9 then state 7 else
  if i = 10 then state 9 else
  if i = 11 then state 10 else
  if i = 12 then state 11 else
  if i = 13 then state 12 else
  if i = 14 then state 13 else
  if i = 15 then state 14 else
  W16.zero.

op fqinv_word_right
    (a : W16.t) (state : int -> W16.t) (i : int) : W16.t =
  if i = 0 then a else
  if i = 1 then state 0 else
  if i = 2 then state 1 else
  if i = 3 then state 2 else
  if i = 4 then state 2 else
  if i = 5 then state 3 else
  if i = 6 then state 5 else
  if i = 7 then a else
  if i = 8 then state 7 else
  if i = 9 then state 7 else
  if i = 10 then state 9 else
  if i = 11 then state 10 else
  if i = 12 then state 11 else
  if i = 13 then state 12 else
  if i = 14 then state 13 else
  if i = 15 then state 8 else
  W16.zero.

op pe0 : int = 0.
op re0 : int = 0.
op pe1 : int = 1.
op re1 : int = 1.
op pe2 : int = 2.
op re2 : int = 1.
op pe4 : int = 4.
op re4 : int = 3.
op pe8 : int = 8.
op re8 : int = 7.
op pe16 : int = 16.
op re16 : int = 15.
op pe10 : int = 10.
op re10 : int = 9.
op pe26 : int = 26.
op re26 : int = 25.
op pe52 : int = 52.
op re52 : int = 51.
op pe53 : int = 53.
op re53 : int = 52.
op pe63 : int = 63.
op re63 : int = 62.
op pe106 : int = 106.
op re106 : int = 105.
op pe212 : int = 212.
op re212 : int = 211.
op pe424 : int = 424.
op re424 : int = 423.
op pe848 : int = 848.
op re848 : int = 847.
op pe1696 : int = 1696.
op re1696 : int = 1695.
op pe3392 : int = 3392.
op re3392 : int = 3391.
op pe3455 : int = 3455.
op re3455 : int = 3454.
op peinv : int = 3455.
op reinv : int = 3456.

lemma Rinv_nonzero : Rinv %% q <> 0.
proof. by rewrite /Rinv /q /=. qed.

op fqinv_pe (i : int) : int =
  if i = 0 then pe2 else
  if i = 1 then pe4 else
  if i = 2 then pe8 else
  if i = 3 then pe16 else
  if i = 4 then pe10 else
  if i = 5 then pe26 else
  if i = 6 then pe52 else
  if i = 7 then pe53 else
  if i = 8 then pe63 else
  if i = 9 then pe106 else
  if i = 10 then pe212 else
  if i = 11 then pe424 else
  if i = 12 then pe848 else
  if i = 13 then pe1696 else
  if i = 14 then pe3392 else
  if i = 15 then pe3455 else pe0.

op fqinv_re (i : int) : int =
  if i = 0 then re2 else
  if i = 1 then re4 else
  if i = 2 then re8 else
  if i = 3 then re16 else
  if i = 4 then re10 else
  if i = 5 then re26 else
  if i = 6 then re52 else
  if i = 7 then re53 else
  if i = 8 then re63 else
  if i = 9 then re106 else
  if i = 10 then re212 else
  if i = 11 then re424 else
  if i = 12 then re848 else
  if i = 13 then re1696 else
  if i = 14 then re3392 else
  if i = 15 then re3455 else re0.

op fqinv_exponent_relations
    (p r : int -> int) (pout rout : int) : bool =
  (forall i, 0 <= i < 16 => 0 <= p i /\ 0 <= r i) /\
  1 + 1 = p 0 /\ 0 + 0 + 1 = r 0 /\
  p 0 + p 0 = p 1 /\ r 0 + r 0 + 1 = r 1 /\
  p 1 + p 1 = p 2 /\ r 1 + r 1 + 1 = r 2 /\
  p 2 + p 2 = p 3 /\ r 2 + r 2 + 1 = r 3 /\
  p 0 + p 2 = p 4 /\ r 0 + r 2 + 1 = r 4 /\
  p 4 + p 3 = p 5 /\ r 4 + r 3 + 1 = r 5 /\
  p 5 + p 5 = p 6 /\ r 5 + r 5 + 1 = r 6 /\
  p 6 + 1 = p 7 /\ r 6 + 0 + 1 = r 7 /\
  p 4 + p 7 = p 8 /\ r 4 + r 7 + 1 = r 8 /\
  p 7 + p 7 = p 9 /\ r 7 + r 7 + 1 = r 9 /\
  p 9 + p 9 = p 10 /\ r 9 + r 9 + 1 = r 10 /\
  p 10 + p 10 = p 11 /\ r 10 + r 10 + 1 = r 11 /\
  p 11 + p 11 = p 12 /\ r 11 + r 11 + 1 = r 12 /\
  p 12 + p 12 = p 13 /\ r 12 + r 12 + 1 = r 13 /\
  p 13 + p 13 = p 14 /\ r 13 + r 13 + 1 = r 14 /\
  p 14 + p 8 = p 15 /\ r 14 + r 8 + 1 = r 15 /\
  0 + p 15 = pout /\ 1 + r 15 + 1 = rout.

lemma fqinv_exponent_schedule :
  fqinv_exponent_relations fqinv_pe fqinv_re peinv reinv.
proof.
  rewrite /fqinv_exponent_relations.
  split.
  + move=> i Hi.
    rewrite /fqinv_pe /fqinv_re.
    smt().
  rewrite /fqinv_pe /fqinv_re.
  rewrite /pe0 /re0 /pe1 /re1 /pe2 /re2 /pe4 /re4 /pe8 /re8.
  rewrite /pe16 /re16 /pe10 /re10 /pe26 /re26 /pe52 /re52.
  rewrite /pe53 /re53 /pe63 /re63 /pe106 /re106 /pe212 /re212.
  rewrite /pe424 /re424 /pe848 /re848 /pe1696 /re1696.
  rewrite /pe3392 /re3392 /pe3455 /re3455 /peinv /reinv.
  done.
qed.

op power_relation
    (base output : W16.t) (base_exp rinv_exp : int) : bool =
  coeff output %% q =
    (exp (coeff base) base_exp * exp Rinv rinv_exp) %% q.

lemma power_relationE
    (base output : W16.t) (base_exp rinv_exp : int) :
  power_relation base output base_exp rinv_exp =>
  coeff output %% q =
    (exp (coeff base) base_exp * exp Rinv rinv_exp) %% q.
proof. by rewrite /power_relation. qed.

lemma mul_mod_q_congr (x y x' y' : int) :
  x %% q = x' %% q =>
  y %% q = y' %% q =>
  (x * y) %% q = (x' * y') %% q.
proof. by move=> Hx Hy; rewrite -modzMml Hx modzMml -modzMmr Hy modzMmr. qed.

lemma power_step_exact
    (a : int) (e1 r1 e2 r2 : int) :
  0 <= e1 => 0 <= r1 => 0 <= e2 => 0 <= r2 =>
  (exp a e1 * exp Rinv r1) *
  (exp a e2 * exp Rinv r2) * Rinv =
  exp a (e1 + e2) * exp Rinv (r1 + r2 + 1).
proof.
  move=> He1 Hr1 He2 Hr2.
  have Hbase : exp a (e1 + e2) = exp a e1 * exp a e2
    by exact (exprD_nneg a e1 e2 He1 He2).
  have Hmont12 : exp Rinv (r1 + r2) = exp Rinv r1 * exp Rinv r2
    by exact (exprD_nneg Rinv r1 r2 Hr1 Hr2).
  have Hrsum : 0 <= r1 + r2 by smt().
  have HmontFinal :
      exp Rinv ((r1 + r2) + 1) = Rinv * exp Rinv (r1 + r2)
    by exact (exprS Rinv (r1 + r2) Hrsum).
  rewrite Hbase HmontFinal Hmont12.
  ring.
qed.

lemma fqmul_word_spec_algebra (a b : W16.t) :
  in_qrange a =>
  in_qrange b =>
  in_qrange (fqmul_word_spec a b) /\
  coeff (fqmul_word_spec a b) %% q =
    (coeff a * coeff b * Rinv) %% q.
proof.
  move=> Ha Hb.
  have Hbound := product_bound (coeff a) (coeff b) Ha Hb.
  have Hreduce := montgomery_reduce_of_int (coeff a * coeff b) Hbound.
  have Hmul :
      NTRUPlus768BasemulProof.mul_i16 a b =
      W32.of_int (coeff a * coeff b)
    by exact (mul_i16E a b).
  rewrite /fqmul_word_spec Hmul.
  move: Hreduce => [Hrange Hcongr].
  split.
  + exact Hrange.
  exact Hcongr.
qed.

lemma fqmul_power_step
    (base x y : W16.t) (e1 r1 e2 r2 : int) :
  0 <= e1 => 0 <= r1 => 0 <= e2 => 0 <= r2 =>
  in_qrange x =>
  in_qrange y =>
  power_relation base x e1 r1 =>
  power_relation base y e2 r2 =>
  in_qrange (fqmul_word_spec x y) /\
  power_relation base (fqmul_word_spec x y)
    (e1 + e2) (r1 + r2 + 1).
proof.
  move=> He1 Hr1 He2 Hr2 Hxrange Hyrange Hx Hy.
  have Hstep := fqmul_word_spec_algebra x y Hxrange Hyrange.
  move: Hstep => [Hrange Hout].
  split; first exact Hrange.
  rewrite /power_relation Hout.
  have Hxy := mul_mod_q_congr
    (coeff x) (coeff y)
    (exp (coeff base) e1 * exp Rinv r1)
    (exp (coeff base) e2 * exp Rinv r2) Hx Hy.
  have Hscaled := mul_mod_q_congr
    (coeff x * coeff y) Rinv
    ((exp (coeff base) e1 * exp Rinv r1) *
     (exp (coeff base) e2 * exp Rinv r2)) Rinv Hxy _.
  + done.
  rewrite Hscaled.
  rewrite (power_step_exact (coeff base) e1 r1 e2 r2 He1 Hr1 He2 Hr2).
  done.
qed.

lemma fqmul_power_step_as
    (base x y output : W16.t) (e1 r1 e2 r2 : int) :
  0 <= e1 => 0 <= r1 => 0 <= e2 => 0 <= r2 =>
  in_qrange x =>
  in_qrange y =>
  power_relation base x e1 r1 =>
  power_relation base y e2 r2 =>
  fqmul_word_spec x y = output =>
  in_qrange output /\
  power_relation base output (e1 + e2) (r1 + r2 + 1).
proof.
  move=> He1 Hr1 He2 Hr2 Hxrange Hyrange Hx Hy Houtput.
  have [Hrange Hpower] := fqmul_power_step
    base x y e1 r1 e2 r2 He1 Hr1 He2 Hr2 Hxrange Hyrange Hx Hy.
  split.
  + exact (eq_ind (fqmul_word_spec x y) output in_qrange
      Houtput Hrange).
  exact (eq_ind (fqmul_word_spec x y) output
    (fun z => power_relation base z (e1 + e2) (r1 + r2 + 1))
    Houtput Hpower).
qed.

lemma fqmul_power_step_as_named
    (base x y output : W16.t)
    (e1 r1 e2 r2 eout rout : int) :
  0 <= e1 => 0 <= r1 => 0 <= e2 => 0 <= r2 =>
  in_qrange x =>
  in_qrange y =>
  power_relation base x e1 r1 =>
  power_relation base y e2 r2 =>
  fqmul_word_spec x y = output =>
  e1 + e2 = eout =>
  r1 + r2 + 1 = rout =>
  in_qrange output /\ power_relation base output eout rout.
proof.
  move=> He1 Hr1 He2 Hr2 Hxrange Hyrange Hx Hy Houtput Heout Hrout.
  have [Hrange Hpower] := fqmul_power_step_as
    base x y output e1 r1 e2 r2 He1 Hr1 He2 Hr2
    Hxrange Hyrange Hx Hy Houtput.
  split; first exact Hrange.
  have Hbase := eq_ind (e1 + e2) eout
    (fun e => power_relation base output e (r1 + r2 + 1))
    Heout Hpower.
  exact (eq_ind (r1 + r2 + 1) rout
    (fun r => power_relation base output eout r) Hrout Hbase).
qed.

lemma initial_power_relation (a : W16.t) :
  power_relation a a 1 0.
proof. by rewrite /power_relation expr1 expr0 /Rinv /q /=. qed.

lemma fq_rinv_word_coeff : coeff fq_rinv_word = -682.
proof.
  rewrite /fq_rinv_word /coeff.
  apply W16.to_sintK_small; smt().
qed.

lemma fq_rinv_word_qrange : in_qrange fq_rinv_word.
proof. by rewrite /in_qrange fq_rinv_word_coeff /q. qed.

lemma fq_rinv_word_power_relation (a : W16.t) :
  power_relation a fq_rinv_word 0 1.
proof.
  rewrite /power_relation fq_rinv_word_coeff expr0 expr1 /Rinv /q /=.
  done.
qed.

lemma fqinv_word_spec_power_relation_generic
    (a output : W16.t) (state : int -> W16.t)
    (p r : int -> int) (pout rout : int) :
  in_qrange a =>
  (forall i, 0 <= i < 16 =>
    fqmul_word_spec (fqinv_word_left a state i)
      (fqinv_word_right a state i) = state i) =>
  fqmul_word_spec fq_rinv_word (state 15) = output =>
  fqinv_exponent_relations p r pout rout =>
  in_qrange output /\ power_relation a output pout rout.
proof.
  move=> Ha Hsteps Houtput Hexps.
  rewrite /fqinv_exponent_relations in Hexps.
  move: Hexps => [Hnonneg Hrec].
  move: Hrec => [Hpe2 Hrec].
  move: Hrec => [Hre2 Hrec].
  move: Hrec => [Hpe4 Hrec].
  move: Hrec => [Hre4 Hrec].
  move: Hrec => [Hpe8 Hrec].
  move: Hrec => [Hre8 Hrec].
  move: Hrec => [Hpe16 Hrec].
  move: Hrec => [Hre16 Hrec].
  move: Hrec => [Hpe10 Hrec].
  move: Hrec => [Hre10 Hrec].
  move: Hrec => [Hpe26 Hrec].
  move: Hrec => [Hre26 Hrec].
  move: Hrec => [Hpe52 Hrec].
  move: Hrec => [Hre52 Hrec].
  move: Hrec => [Hpe53 Hrec].
  move: Hrec => [Hre53 Hrec].
  move: Hrec => [Hpe63 Hrec].
  move: Hrec => [Hre63 Hrec].
  move: Hrec => [Hpe106 Hrec].
  move: Hrec => [Hre106 Hrec].
  move: Hrec => [Hpe212 Hrec].
  move: Hrec => [Hre212 Hrec].
  move: Hrec => [Hpe424 Hrec].
  move: Hrec => [Hre424 Hrec].
  move: Hrec => [Hpe848 Hrec].
  move: Hrec => [Hre848 Hrec].
  move: Hrec => [Hpe1696 Hrec].
  move: Hrec => [Hre1696 Hrec].
  move: Hrec => [Hpe3392 Hrec].
  move: Hrec => [Hre3392 Hrec].
  move: Hrec => [Hpe3455 Hrec].
  move: Hrec => [Hre3455 [Hpeout Hreout]].

  have [Hp0 Hr0] := Hnonneg 0 _; first done.
  have [Hp1 Hr1] := Hnonneg 1 _; first done.
  have [Hp2 Hr2] := Hnonneg 2 _; first done.
  have [Hp3 Hr3] := Hnonneg 3 _; first done.
  have [Hp4 Hr4] := Hnonneg 4 _; first done.
  have [Hp5 Hr5] := Hnonneg 5 _; first done.
  have [Hp6 Hr6] := Hnonneg 6 _; first done.
  have [Hp7 Hr7] := Hnonneg 7 _; first done.
  have [Hp8 Hr8] := Hnonneg 8 _; first done.
  have [Hp9 Hr9] := Hnonneg 9 _; first done.
  have [Hp10 Hr10] := Hnonneg 10 _; first done.
  have [Hp11 Hr11] := Hnonneg 11 _; first done.
  have [Hp12 Hr12] := Hnonneg 12 _; first done.
  have [Hp13 Hr13] := Hnonneg 13 _; first done.
  have [Hp14 Hr14] := Hnonneg 14 _; first done.
  have [Hp15 Hr15] := Hnonneg 15 _; first done.

  have He2 : fqmul_word_spec (fqinv_word_left a state 0)
      (fqinv_word_right a state 0) = state 0.
  + exact (Hsteps 0 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He2.
  have H2 : in_qrange (state 0) /\ power_relation a (state 0) (p 0) (r 0).
  + exact (fqmul_power_step_as_named a a a (state 0)
      1 0 1 0 (p 0) (r 0) _ _ _ _ Ha Ha
      (initial_power_relation a) (initial_power_relation a)
      He2 Hpe2 Hre2); done.
  move: H2 => [H2r H2p].

  have He4 : fqmul_word_spec (fqinv_word_left a state 1)
      (fqinv_word_right a state 1) = state 1.
  + exact (Hsteps 1 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He4.
  have H4 : in_qrange (state 1) /\ power_relation a (state 1) (p 1) (r 1).
  + exact (fqmul_power_step_as_named a (state 0) (state 0) (state 1)
      (p 0) (r 0) (p 0) (r 0) (p 1) (r 1)
      Hp0 Hr0 Hp0 Hr0 H2r H2r H2p H2p He4 Hpe4 Hre4).
  move: H4 => [H4r H4p].

  have He8 : fqmul_word_spec (fqinv_word_left a state 2)
      (fqinv_word_right a state 2) = state 2.
  + exact (Hsteps 2 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He8.
  have H8 : in_qrange (state 2) /\ power_relation a (state 2) (p 2) (r 2).
  + exact (fqmul_power_step_as_named a (state 1) (state 1) (state 2)
      (p 1) (r 1) (p 1) (r 1) (p 2) (r 2)
      Hp1 Hr1 Hp1 Hr1 H4r H4r H4p H4p He8 Hpe8 Hre8).
  move: H8 => [H8r H8p].

  have He16 : fqmul_word_spec (fqinv_word_left a state 3)
      (fqinv_word_right a state 3) = state 3.
  + exact (Hsteps 3 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He16.
  have H16 : in_qrange (state 3) /\ power_relation a (state 3) (p 3) (r 3).
  + exact (fqmul_power_step_as_named a (state 2) (state 2) (state 3)
      (p 2) (r 2) (p 2) (r 2) (p 3) (r 3)
      Hp2 Hr2 Hp2 Hr2 H8r H8r H8p H8p He16 Hpe16 Hre16).
  move: H16 => [H16r H16p].

  have He10 : fqmul_word_spec (fqinv_word_left a state 4)
      (fqinv_word_right a state 4) = state 4.
  + exact (Hsteps 4 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He10.
  have H10 : in_qrange (state 4) /\ power_relation a (state 4) (p 4) (r 4).
  + exact (fqmul_power_step_as_named a (state 0) (state 2) (state 4)
      (p 0) (r 0) (p 2) (r 2) (p 4) (r 4)
      Hp0 Hr0 Hp2 Hr2 H2r H8r H2p H8p He10 Hpe10 Hre10).
  move: H10 => [H10r H10p].

  have He26 : fqmul_word_spec (fqinv_word_left a state 5)
      (fqinv_word_right a state 5) = state 5.
  + exact (Hsteps 5 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He26.
  have H26 : in_qrange (state 5) /\ power_relation a (state 5) (p 5) (r 5).
  + exact (fqmul_power_step_as_named a (state 4) (state 3) (state 5)
      (p 4) (r 4) (p 3) (r 3) (p 5) (r 5)
      Hp4 Hr4 Hp3 Hr3 H10r H16r H10p H16p He26 Hpe26 Hre26).
  move: H26 => [H26r H26p].

  have He52 : fqmul_word_spec (fqinv_word_left a state 6)
      (fqinv_word_right a state 6) = state 6.
  + exact (Hsteps 6 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He52.
  have H52 : in_qrange (state 6) /\ power_relation a (state 6) (p 6) (r 6).
  + exact (fqmul_power_step_as_named a (state 5) (state 5) (state 6)
      (p 5) (r 5) (p 5) (r 5) (p 6) (r 6)
      Hp5 Hr5 Hp5 Hr5 H26r H26r H26p H26p He52 Hpe52 Hre52).
  move: H52 => [H52r H52p].

  have He53 : fqmul_word_spec (fqinv_word_left a state 7)
      (fqinv_word_right a state 7) = state 7.
  + exact (Hsteps 7 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He53.
  have H53 : in_qrange (state 7) /\ power_relation a (state 7) (p 7) (r 7).
  + exact (fqmul_power_step_as_named a (state 6) a (state 7)
      (p 6) (r 6) 1 0 (p 7) (r 7)
      Hp6 Hr6 _ _ H52r Ha H52p (initial_power_relation a)
      He53 Hpe53 Hre53); done.
  move: H53 => [H53r H53p].

  have He63 : fqmul_word_spec (fqinv_word_left a state 8)
      (fqinv_word_right a state 8) = state 8.
  + exact (Hsteps 8 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He63.
  have H63 : in_qrange (state 8) /\ power_relation a (state 8) (p 8) (r 8).
  + exact (fqmul_power_step_as_named a (state 4) (state 7) (state 8)
      (p 4) (r 4) (p 7) (r 7) (p 8) (r 8)
      Hp4 Hr4 Hp7 Hr7 H10r H53r H10p H53p He63 Hpe63 Hre63).
  move: H63 => [H63r H63p].

  have He106 : fqmul_word_spec (fqinv_word_left a state 9)
      (fqinv_word_right a state 9) = state 9.
  + exact (Hsteps 9 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He106.
  have H106 : in_qrange (state 9) /\ power_relation a (state 9) (p 9) (r 9).
  + exact (fqmul_power_step_as_named a (state 7) (state 7) (state 9)
      (p 7) (r 7) (p 7) (r 7) (p 9) (r 9)
      Hp7 Hr7 Hp7 Hr7 H53r H53r H53p H53p He106 Hpe106 Hre106).
  move: H106 => [H106r H106p].

  have He212 : fqmul_word_spec (fqinv_word_left a state 10)
      (fqinv_word_right a state 10) = state 10.
  + exact (Hsteps 10 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He212.
  have H212 : in_qrange (state 10) /\ power_relation a (state 10) (p 10) (r 10).
  + exact (fqmul_power_step_as_named a (state 9) (state 9) (state 10)
      (p 9) (r 9) (p 9) (r 9) (p 10) (r 10)
      Hp9 Hr9 Hp9 Hr9 H106r H106r H106p H106p He212 Hpe212 Hre212).
  move: H212 => [H212r H212p].

  have He424 : fqmul_word_spec (fqinv_word_left a state 11)
      (fqinv_word_right a state 11) = state 11.
  + exact (Hsteps 11 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He424.
  have H424 : in_qrange (state 11) /\ power_relation a (state 11) (p 11) (r 11).
  + exact (fqmul_power_step_as_named a (state 10) (state 10) (state 11)
      (p 10) (r 10) (p 10) (r 10) (p 11) (r 11)
      Hp10 Hr10 Hp10 Hr10 H212r H212r H212p H212p He424 Hpe424 Hre424).
  move: H424 => [H424r H424p].

  have He848 : fqmul_word_spec (fqinv_word_left a state 12)
      (fqinv_word_right a state 12) = state 12.
  + exact (Hsteps 12 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He848.
  have H848 : in_qrange (state 12) /\ power_relation a (state 12) (p 12) (r 12).
  + exact (fqmul_power_step_as_named a (state 11) (state 11) (state 12)
      (p 11) (r 11) (p 11) (r 11) (p 12) (r 12)
      Hp11 Hr11 Hp11 Hr11 H424r H424r H424p H424p He848 Hpe848 Hre848).
  move: H848 => [H848r H848p].

  have He1696 : fqmul_word_spec (fqinv_word_left a state 13)
      (fqinv_word_right a state 13) = state 13.
  + exact (Hsteps 13 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He1696.
  have H1696 :
      in_qrange (state 13) /\ power_relation a (state 13) (p 13) (r 13).
  + exact (fqmul_power_step_as_named a (state 12) (state 12) (state 13)
      (p 12) (r 12) (p 12) (r 12) (p 13) (r 13)
      Hp12 Hr12 Hp12 Hr12 H848r H848r H848p H848p He1696 Hpe1696 Hre1696).
  move: H1696 => [H1696r H1696p].

  have He3392 : fqmul_word_spec (fqinv_word_left a state 14)
      (fqinv_word_right a state 14) = state 14.
  + exact (Hsteps 14 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He3392.
  have H3392 :
      in_qrange (state 14) /\ power_relation a (state 14) (p 14) (r 14).
  + exact (fqmul_power_step_as_named a (state 13) (state 13) (state 14)
      (p 13) (r 13) (p 13) (r 13) (p 14) (r 14)
      Hp13 Hr13 Hp13 Hr13 H1696r H1696r H1696p H1696p
      He3392 Hpe3392 Hre3392).
  move: H3392 => [H3392r H3392p].

  have He3455 : fqmul_word_spec (fqinv_word_left a state 15)
      (fqinv_word_right a state 15) = state 15.
  + exact (Hsteps 15 _); done.
  rewrite /fqinv_word_left /fqinv_word_right /= in He3455.
  have H3455 :
      in_qrange (state 15) /\ power_relation a (state 15) (p 15) (r 15).
  + exact (fqmul_power_step_as_named a (state 14) (state 8) (state 15)
      (p 14) (r 14) (p 8) (r 8) (p 15) (r 15)
      Hp14 Hr14 Hp8 Hr8 H3392r H63r H3392p H63p He3455 Hpe3455 Hre3455).
  move: H3455 => [H3455r H3455p].

  exact (fqmul_power_step_as_named
    a fq_rinv_word (state 15) output
    0 1 (p 15) (r 15) pout rout _ _ Hp15 Hr15
    fq_rinv_word_qrange H3455r
    (fq_rinv_word_power_relation a) H3455p Houtput Hpeout Hreout); done.
qed.

lemma fqinv_word_spec_power_relation
    (a output : W16.t) (state : int -> W16.t) :
  in_qrange a =>
  (forall i, 0 <= i < 16 =>
    fqmul_word_spec (fqinv_word_left a state i)
      (fqinv_word_right a state i) = state i) =>
  fqmul_word_spec fq_rinv_word (state 15) = output =>
  in_qrange output /\ power_relation a output peinv reinv.
proof.
  move=> Ha Hsteps Houtput.
  exact (fqinv_word_spec_power_relation_generic
    a output state fqinv_pe fqinv_re peinv reinv
    Ha Hsteps Houtput fqinv_exponent_schedule).
qed.

lemma fqinv_word_spec_inverse
    (a output : W16.t) (base_exp rinv_exp : int) :
  in_qrange output =>
  power_relation a output base_exp rinv_exp =>
  base_exp = 3455 =>
  rinv_exp = 3456 =>
  coeff a %% q <> 0 =>
  in_qrange output /\ (coeff a * coeff output) %% q = 1.
proof.
  move=> Hrange Hpower HbaseExp HrinvExp Hnonzero.
  have HpowerE := power_relationE
    a output base_exp rinv_exp Hpower.
  clear Hpower.
  split; first exact Hrange.
  exact (inverse_output_congr
    (coeff a) (coeff output) Rinv base_exp rinv_exp
    HpowerE HbaseExp HrinvExp Hnonzero Rinv_nonzero).
qed.

lemma fqinv_word_spec_rminus3_scaling
    (a output : W16.t) (base_exp rinv_exp d : int) :
  in_qrange output =>
  power_relation a output base_exp rinv_exp =>
  base_exp = 3455 =>
  rinv_exp = 3456 =>
  coeff a %% q = (d * exp Rinv 3) %% q =>
  coeff a %% q <> 0 =>
  (d * (coeff output * exp Rinv 3)) %% q = 1.
proof.
  move=> Hrange Hpower HbaseExp HrinvExp Hencoded Hnonzero.
  have Hinverse := fqinv_word_spec_inverse
    a output base_exp rinv_exp Hrange Hpower
    HbaseExp HrinvExp Hnonzero.
  move: Hinverse => [_ Hinverse].
  have Hreplace := mul_mod_q_congr
    (coeff a) (coeff output)
    (d * exp Rinv 3) (coeff output) Hencoded _.
  + done.
  have Heq :
      d * exp Rinv 3 * coeff output =
      d * (coeff output * exp Rinv 3) by ring.
  rewrite -Heq.
  move: Hreplace Hinverse.
  smt().
qed.
