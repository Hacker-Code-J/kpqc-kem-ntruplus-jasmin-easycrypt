require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord JModel_x86.

require import Array768 Array1152.
require import NTRUPlus768BasemulAlgebra.
require import NTRUPlus768PolyToBytesProof.

import Ring.IntID IntOrder.

op poly_tobytes_input_qrange (p : W16.t Array768.t) : bool =
  forall j, 0 <= j < 768 => -q <= coeff p.[j] < q.

op canonical_coeff (w : W16.t) : int =
  if coeff w < 0 then coeff w + q else coeff w.

op poly_tobytes_byte0_int (p : W16.t Array768.t) (i : int) : int =
  canonical_coeff p.[2 * i] %% 256.

op poly_tobytes_byte1_int (p : W16.t Array768.t) (i : int) : int =
  canonical_coeff p.[2 * i] %/ 256 + 16 * (canonical_coeff p.[2 * i + 1] %% 16).

op poly_tobytes_byte2_int (p : W16.t Array768.t) (i : int) : int =
  canonical_coeff p.[2 * i + 1] %/ 16.

op poly_tobytes_byte_at (p : W16.t Array768.t) (j : int) : W8.t =
  if j %% 3 = 0 then
    W8.of_int (poly_tobytes_byte0_int p (j %/ 3))
  else if j %% 3 = 1 then
    W8.of_int (poly_tobytes_byte1_int p (j %/ 3))
  else
    W8.of_int (poly_tobytes_byte2_int p (j %/ 3)).

op poly_tobytes_spec (p : W16.t Array768.t) : W8.t Array1152.t =
  Array1152.init (fun j => poly_tobytes_byte_at p j).

op poly_tobytes_canonical_spec (p : W16.t Array768.t) : W16.t Array768.t =
  Array768.init (fun j => W16.of_int (canonical_coeff p.[j])).

op poly_frombytes_even_int (a : W8.t Array1152.t) (i : int) : int =
  W8.to_uint a.[3 * i] + 256 * (W8.to_uint a.[3 * i + 1] %% 16).

op poly_frombytes_odd_int (a : W8.t Array1152.t) (i : int) : int =
  W8.to_uint a.[3 * i + 1] %/ 16 + 16 * W8.to_uint a.[3 * i + 2].

op poly_frombytes_int (a : W8.t Array1152.t) (j : int) : int =
  if j %% 2 = 0 then
    poly_frombytes_even_int a (j %/ 2)
  else
    poly_frombytes_odd_int a (j %/ 2).

op poly_frombytes_spec (a : W8.t Array1152.t) : W16.t Array768.t =
  Array768.init (fun j => W16.of_int (poly_frombytes_int a j)).

lemma poly_tobytes_procedure_input_qrangeE
    (p : W16.t Array768.t) :
  NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange p =
  poly_tobytes_input_qrange p.
proof.
  rewrite /NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange
    /poly_tobytes_input_qrange.
  done.
qed.

lemma poly_tobytes_procedure_specE (p : W16.t Array768.t) :
  NTRUPlus768PolyToBytesProof.poly_tobytes_spec p = poly_tobytes_spec p.
proof.
  rewrite /NTRUPlus768PolyToBytesProof.poly_tobytes_spec /poly_tobytes_spec
    /NTRUPlus768PolyToBytesProof.poly_tobytes_byte_at /poly_tobytes_byte_at
    /NTRUPlus768PolyToBytesProof.poly_tobytes_byte0_int
    /poly_tobytes_byte0_int
    /NTRUPlus768PolyToBytesProof.poly_tobytes_byte1_int
    /poly_tobytes_byte1_int
    /NTRUPlus768PolyToBytesProof.poly_tobytes_byte2_int
    /poly_tobytes_byte2_int
    /NTRUPlus768PolyToBytesProof.canonical_coeff /canonical_coeff.
  done.
qed.

lemma coeff_of_word_small (x : int) :
  W16.min_sint <= x <= W16.max_sint =>
  coeff (W16.of_int x) = x.
proof.
  move=> Hx.
  rewrite /coeff.
  exact (W16.to_sintK_small x Hx).
qed.

lemma canonical_coeff_range (w : W16.t) :
  -q <= coeff w < q =>
  0 <= canonical_coeff w < q.
proof.
  move=> Hw.
  rewrite /canonical_coeff.
  case (coeff w < 0).
  + move=> Hneg.
    rewrite /q /=.
    smt().
  move=> Hnonneg.
  rewrite /q /=.
  smt().
qed.

lemma poly_tobytes_canonical_coeff_range
    (p : W16.t Array768.t) (j : int) :
  poly_tobytes_input_qrange p =>
  0 <= j < 768 =>
  0 <= canonical_coeff p.[j] < q.
proof.
  move=> Hp Hj.
  exact (canonical_coeff_range p.[j] (Hp j Hj)).
qed.

lemma poly_tobytes_byte0_range (p : W16.t Array768.t) (i : int) :
  poly_tobytes_input_qrange p =>
  0 <= i < 384 =>
  0 <= poly_tobytes_byte0_int p i < 256.
proof.
  move=> Hp Hi.
  have Hcanon := poly_tobytes_canonical_coeff_range p (2 * i) Hp _.
  + smt().
  rewrite /poly_tobytes_byte0_int.
  smt().
qed.

lemma poly_tobytes_byte1_range (p : W16.t Array768.t) (i : int) :
  poly_tobytes_input_qrange p =>
  0 <= i < 384 =>
  0 <= poly_tobytes_byte1_int p i < 256.
proof.
  move=> Hp Hi.
  have Hc0 := poly_tobytes_canonical_coeff_range p (2 * i) Hp _.
  + smt().
  have Hc1 := poly_tobytes_canonical_coeff_range p (2 * i + 1) Hp _.
  + smt().
  rewrite /poly_tobytes_byte1_int.
  have Hdiv : 0 <= canonical_coeff p.[2 * i] %/ 256 < 16 by smt().
  have Hmod : 0 <= canonical_coeff p.[2 * i + 1] %% 16 < 16 by smt().
  smt().
qed.

lemma poly_tobytes_byte2_range (p : W16.t Array768.t) (i : int) :
  poly_tobytes_input_qrange p =>
  0 <= i < 384 =>
  0 <= poly_tobytes_byte2_int p i < 256.
proof.
  move=> Hp Hi.
  have Hcanon := poly_tobytes_canonical_coeff_range p (2 * i + 1) Hp _.
  + smt().
  rewrite /poly_tobytes_byte2_int.
  smt().
qed.

lemma poly_tobytes_spec_byte0E (p : W16.t Array768.t) (i : int) :
  0 <= i < 384 =>
  (poly_tobytes_spec p).[3 * i] = W8.of_int (poly_tobytes_byte0_int p i).
proof.
  move=> Hi.
  rewrite /poly_tobytes_spec Array1152.initiE 1:/# /poly_tobytes_byte_at.
  smt().
qed.

lemma poly_tobytes_spec_byte1E (p : W16.t Array768.t) (i : int) :
  0 <= i < 384 =>
  (poly_tobytes_spec p).[3 * i + 1] = W8.of_int (poly_tobytes_byte1_int p i).
proof.
  move=> Hi.
  rewrite /poly_tobytes_spec Array1152.initiE 1:/# /poly_tobytes_byte_at.
  smt().
qed.

lemma poly_tobytes_spec_byte2E (p : W16.t Array768.t) (i : int) :
  0 <= i < 384 =>
  (poly_tobytes_spec p).[3 * i + 2] = W8.of_int (poly_tobytes_byte2_int p i).
proof.
  move=> Hi.
  rewrite /poly_tobytes_spec Array1152.initiE 1:/# /poly_tobytes_byte_at.
  smt().
qed.

lemma poly_tobytes_canonical_spec_coeff
    (p : W16.t Array768.t) (j : int) :
  poly_tobytes_input_qrange p =>
  0 <= j < 768 =>
  coeff (poly_tobytes_canonical_spec p).[j] = canonical_coeff p.[j].
proof.
  move=> Hp Hj.
  rewrite /poly_tobytes_canonical_spec Array768.initiE 1:/#.
  apply coeff_of_word_small.
  have Hrange := poly_tobytes_canonical_coeff_range p j Hp Hj.
  rewrite /q /= in Hrange.
  smt().
qed.

lemma canonical_coeff_mod_q (w : W16.t) :
  -q <= coeff w < q =>
  canonical_coeff w %% q = coeff w %% q.
proof.
  move=> Hw.
  rewrite /canonical_coeff.
  case (coeff w < 0).
  + move=> Hneg.
    rewrite /q /=.
    smt().
  move=> Hnonneg.
  by [].
qed.

lemma poly_tobytes_canonical_spec_mod_q
    (p : W16.t Array768.t) (j : int) :
  poly_tobytes_input_qrange p =>
  0 <= j < 768 =>
  coeff (poly_tobytes_canonical_spec p).[j] %% q = coeff p.[j] %% q.
proof.
  move=> Hp Hj.
  have Hcoeff :
      coeff (poly_tobytes_canonical_spec p).[j] = canonical_coeff p.[j]
    by exact (poly_tobytes_canonical_spec_coeff p j Hp Hj).
  rewrite Hcoeff.
  exact (canonical_coeff_mod_q p.[j] (Hp j Hj)).
qed.

lemma poly_frombytes_spec_coeff_uint (a : W8.t Array1152.t) (j : int) :
  0 <= j < 768 =>
  W16.to_uint (poly_frombytes_spec a).[j] = poly_frombytes_int a j.
proof.
  move=> Hj.
  rewrite /poly_frombytes_spec Array768.initiE 1:/# W16.of_uintK.
  rewrite /poly_frombytes_int.
  case (j %% 2 = 0).
  + move=> _.
    rewrite /poly_frombytes_even_int.
    have Hb0 := W8.to_uint_cmp a.[3 * (j %/ 2)].
    have Hb1 := W8.to_uint_cmp a.[3 * (j %/ 2) + 1].
    have H8e : W8.modulus = 256 by done.
    have H16e : W16.modulus = 65536 by done.
    rewrite (modz_small _ 65536).
    smt(modz_cmp).
    trivial.
  move=> _.
  rewrite /poly_frombytes_odd_int.
  have Hb1 := W8.to_uint_cmp a.[3 * (j %/ 2) + 1].
  have Hb2 := W8.to_uint_cmp a.[3 * (j %/ 2) + 2].
  have H8o : W8.modulus = 256 by done.
  have H16o : W16.modulus = 65536 by done.
  rewrite (modz_small _ 65536).
  smt(modz_cmp).
  trivial.
qed.

lemma poly_frombytes_poly_tobytes_roundtrip
    (p : W16.t Array768.t) :
  poly_tobytes_input_qrange p =>
  poly_frombytes_spec (poly_tobytes_spec p) = poly_tobytes_canonical_spec p.
proof.
  move=> Hp.
  apply Array768.tP => j Hj.
  apply W16.to_uint_eq.
  rewrite poly_frombytes_spec_coeff_uint 1:Hj.
  rewrite /poly_tobytes_canonical_spec Array768.initiE 1:Hj W16.of_uintK.
  have Hcanon := poly_tobytes_canonical_coeff_range p j Hp Hj.
  have H16 : W16.modulus = 65536 by done.
  rewrite (modz_small _ 65536).
  + smt().
  rewrite /poly_frombytes_int.
  case (j %% 2 = 0).
  + move=> Heven.
    have Hi : 0 <= j %/ 2 < 384 by smt().
    rewrite /poly_frombytes_even_int.
    rewrite poly_tobytes_spec_byte0E 1:/# poly_tobytes_spec_byte1E 1:/#.
    rewrite W8.of_uintK.
    - rewrite W8.of_uintK.
      * rewrite /poly_tobytes_byte0_int /poly_tobytes_byte1_int.
        have Hc0 := poly_tobytes_canonical_coeff_range p j Hp Hj.
        have Hc1 := poly_tobytes_canonical_coeff_range p (j + 1) Hp _.
        + smt().
        have Hmod : 0 <= canonical_coeff p.[j + 1] %% 16 < 16 by smt().
        have Hdiv : 0 <= canonical_coeff p.[j] %/ 256 < 16 by smt().
        smt().
  move=> Hodd.
  have Hi : 0 <= j %/ 2 < 384 by smt().
  rewrite /poly_frombytes_odd_int.
  rewrite poly_tobytes_spec_byte1E 1:/# poly_tobytes_spec_byte2E 1:/#.
  rewrite W8.of_uintK.
  + rewrite W8.of_uintK.
    - rewrite /poly_tobytes_byte1_int /poly_tobytes_byte2_int.
      have Hc0 := poly_tobytes_canonical_coeff_range p (j - 1) Hp _.
      + smt().
      have Hc1 := poly_tobytes_canonical_coeff_range p j Hp Hj.
      have Hmid : 0 <= canonical_coeff p.[j - 1] %/ 256 < 16 by smt().
      have Hhi : 0 <= canonical_coeff p.[j] %/ 16 < 256 by smt().
      have Hmod : 0 <= canonical_coeff p.[j] %% 16 < 16 by smt().
      smt().
qed.

lemma poly_frombytes_poly_tobytes_roundtrip_coeff_range
    (p : W16.t Array768.t) (j : int) :
  poly_tobytes_input_qrange p =>
  0 <= j < 768 =>
  0 <= coeff (poly_frombytes_spec (poly_tobytes_spec p)).[j] < q.
proof.
  move=> Hp Hj.
  rewrite poly_frombytes_poly_tobytes_roundtrip 1:/#.
  have Hcoeff :
      coeff (poly_tobytes_canonical_spec p).[j] = canonical_coeff p.[j]
    by exact (poly_tobytes_canonical_spec_coeff p j Hp Hj).
  rewrite Hcoeff.
  exact (poly_tobytes_canonical_coeff_range p j Hp Hj).
qed.

lemma poly_frombytes_poly_tobytes_roundtrip_coeff_mod_q
    (p : W16.t Array768.t) (j : int) :
  poly_tobytes_input_qrange p =>
  0 <= j < 768 =>
  coeff (poly_frombytes_spec (poly_tobytes_spec p)).[j] %% q =
    coeff p.[j] %% q.
proof.
  move=> Hp Hj.
  rewrite poly_frombytes_poly_tobytes_roundtrip 1:/#.
  have Hcoeff :
      coeff (poly_tobytes_canonical_spec p).[j] = canonical_coeff p.[j]
    by exact (poly_tobytes_canonical_spec_coeff p j Hp Hj).
  rewrite Hcoeff.
  exact (canonical_coeff_mod_q p.[j] (Hp j Hj)).
qed.

lemma poly_tobytes_roundtrip_functional
    (rp0 : W8.t Array1152.t) (p : W16.t Array768.t) :
  poly_tobytes_input_qrange p =>
  hoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = rp0 /\ ap = p ==>
    poly_frombytes_spec res = poly_tobytes_canonical_spec p].
proof.
  move=> Hp.
  have Hprocedure_range :
      NTRUPlus768PolyToBytesProof.poly_tobytes_input_qrange p.
  + rewrite poly_tobytes_procedure_input_qrangeE.
    exact Hp.
  conseq
    (NTRUPlus768PolyToBytesProof.poly_tobytes_functional
      rp0 p Hprocedure_range) => /> &hr Hres.
  rewrite Hres poly_tobytes_procedure_specE.
  exact (poly_frombytes_poly_tobytes_roundtrip p Hp).
qed.

lemma poly_tobytes_roundtrip_correct
    (rp0 : W8.t Array1152.t) (p : W16.t Array768.t) :
  poly_tobytes_input_qrange p =>
  phoare [NTRUPlus768PolyToBytes.M.jade_ntruplus_ntruplus768_amd64_ref_poly_tobytes :
    rp = rp0 /\ ap = p ==>
    poly_frombytes_spec res = poly_tobytes_canonical_spec p] = 1%r.
proof.
  move=> Hp.
  have Hfunctional := poly_tobytes_roundtrip_functional rp0 p Hp.
  by conseq NTRUPlus768PolyToBytesProof.poly_tobytes_lossless Hfunctional.
qed.
