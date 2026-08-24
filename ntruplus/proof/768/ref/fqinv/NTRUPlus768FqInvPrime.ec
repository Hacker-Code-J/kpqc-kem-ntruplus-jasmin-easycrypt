require import AllCore IntDiv Ring ZModP.

require import NTRUPlus768BasemulAlgebra.

import Ring.IntID.

lemma q_prime : prime q.
proof.
  rewrite /q /prime.
  split; first done.
  move=> d Hd.
  case/dvdzP: Hd => k H.
  smt().
qed.

clone import ZModField as NTRUFq with
  op p <- q
  rename "zmod" as "fqcoeff"
  rename "ZModp" as "NTRUFq"
  proof prime_p by exact q_prime
  proof *.

lemma fqcoeff_nonzero_unit (x : fqcoeff) :
  x <> zero => unit x.
proof. by rewrite unitE. qed.

lemma exp3455_inverse (x : fqcoeff) :
  x <> zero => inv x = exp x 3455.
proof.
  move=> Hnonzero.
  have Hunit : unit x by exact (fqcoeff_nonzero_unit x Hnonzero).
  have Hgeneric := inv_exp_sub_p_2 x Hunit.
  have Hexp : 3455 = q - 2 by rewrite /q.
  have Hpow : exp x 3455 = exp x (q - 2) by congr.
  by rewrite Hgeneric Hpow.
qed.

lemma exp3456_one (x : fqcoeff) :
  x <> zero => exp x 3456 = one.
proof.
  move=> Hnonzero.
  have Hunit : unit x by exact (fqcoeff_nonzero_unit x Hnonzero).
  have Hgeneric := exp_sub_p_1 x Hunit.
  have Hexp : 3456 = q - 1 by rewrite /q.
  have Hpow : exp x 3456 = exp x (q - 1) by congr.
  by rewrite Hpow Hgeneric.
qed.

lemma int_nonzero_fqcoeff (a : int) :
  a %% q <> 0 => infqcoeff a <> zero.
proof.
  move=> Ha.
  rewrite infqcoeff_eq0P dvdzE.
  exact Ha.
qed.

lemma pow_qminus2_inverse (a e : int) :
  e = 3455 =>
  a %% q <> 0 =>
  (a * exp a e) %% q = 1.
proof.
  move=> He Ha.
  have He0 : 0 <= e by rewrite He.
  have Hnonzero := int_nonzero_fqcoeff a Ha.
  have Hexp := exp3455_inverse (infqcoeff a) Hnonzero.
  have Hfield3455 : infqcoeff a * exp (infqcoeff a) 3455 = one.
  + rewrite -Hexp.
    exact (NTRUFqField.mulrV (infqcoeff a) Hnonzero).
  have Hrev : 3455 = e by exact (eq_sym_imp e 3455 He).
  have Hfield : infqcoeff a * exp (infqcoeff a) e = one.
  + exact (eq_ind 3455 e
      (fun n => infqcoeff a * exp (infqcoeff a) n = one)
      Hrev Hfield3455).
  have Hmapped : infqcoeff (a * exp a e) = one.
  + rewrite infqcoeffM infqcoeff_exp He0 /=.
    exact Hfield.
  have Hcongr : (a * exp a e) %% q = 1 %% q.
  + rewrite eq_infqcoeff Hmapped /one.
    done.
  move: Hcongr.
  rewrite /q /=.
  done.
qed.

lemma pow_qminus1_one (a e : int) :
  e = 3456 =>
  a %% q <> 0 =>
  exp a e %% q = 1.
proof.
  move=> He Ha.
  have He0 : 0 <= e by rewrite He.
  have Hnonzero := int_nonzero_fqcoeff a Ha.
  have Hfield3456 := exp3456_one (infqcoeff a) Hnonzero.
  have Hrev : 3456 = e by exact (eq_sym_imp e 3456 He).
  have Hfield : exp (infqcoeff a) e = one.
  + exact (eq_ind 3456 e
      (fun n => exp (infqcoeff a) n = one) Hrev Hfield3456).
  have Hmapped : infqcoeff (exp a e) = one.
  + rewrite infqcoeff_exp He0 /=.
    exact Hfield.
  have Hcongr : exp a e %% q = 1 %% q.
  + rewrite eq_infqcoeff Hmapped /one.
    done.
  move: Hcongr.
  rewrite /q /=.
  done.
qed.

lemma prime_mul_mod_q_congr (x y x' y' : int) :
  x %% q = x' %% q =>
  y %% q = y' %% q =>
  (x * y) %% q = (x' * y') %% q.
proof. by move=> Hx Hy; rewrite -modzMml Hx modzMml -modzMmr Hy modzMmr. qed.

lemma inverse_times_unit_power
    (a b ea eb : int) :
  ea = 3455 =>
  eb = 3456 =>
  a %% q <> 0 =>
  b %% q <> 0 =>
  (a * (exp a ea * exp b eb)) %% q = 1.
proof.
  move=> Hea Heb Ha Hb.
  have Hainv := pow_qminus2_inverse a ea Hea Ha.
  have Hbpow := pow_qminus1_one b eb Heb Hb.
  rewrite mulrA.
  rewrite (prime_mul_mod_q_congr
    (a * exp a ea) (exp b eb) 1 1 Hainv Hbpow).
  rewrite /q /=.
  done.
qed.

lemma inverse_output_congr
    (a output unit_exp ea eb : int) :
  output %% q = (exp a ea * exp unit_exp eb) %% q =>
  ea = 3455 =>
  eb = 3456 =>
  a %% q <> 0 =>
  unit_exp %% q <> 0 =>
  (a * output) %% q = 1.
proof.
  move=> Houtput Hea Heb Ha Hunit.
  rewrite (prime_mul_mod_q_congr
    a output a (exp a ea * exp unit_exp eb) _ Houtput).
  + done.
  exact (inverse_times_unit_power
    a unit_exp ea eb Hea Heb Ha Hunit).
qed.
