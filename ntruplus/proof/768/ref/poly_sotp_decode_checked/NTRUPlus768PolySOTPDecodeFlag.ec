require import AllCore IntDiv.
from Jasmin require import JWord JModel_x86.

(* Word-level facts for the extracted decoder's aggregate and final mask.
   The aggregate may contain any 16-bit value; no trit restriction is used. *)
lemma sotp_or_range (r s : W32.t) :
  W32.to_uint r < 65536 => W32.to_uint s < 65536 =>
  W32.to_uint (r `|` s) < 65536.
proof.
  move=> hr hs.
  have hmask : forall (w : W32.t), W32.to_uint w < 65536 =>
    w `&` W32.of_int (2^16 - 1) = w.
  + move=> w hw; apply W32.to_uint_eq.
    rewrite W32.to_uint_and_mod 1:// /= modz_small; smt(W32.to_uint_cmp).
  have hm : (r `|` s) `&` W32.of_int (2^16 - 1) = r `|` s.
  + by rewrite W32.andw_orwDl (hmask r hr) (hmask s hs).
  have hu : W32.to_uint ((r `|` s) `&` W32.of_int (2^16 - 1)) =
    W32.to_uint (r `|` s) by rewrite hm.
  rewrite W32.to_uint_and_mod 1:// /= in hu.
  smt(modz_cmp).
qed.

lemma sotp_or_valid (r s : W32.t) :
  W32.to_uint (r `|` s) <= 1 <=>
  W32.to_uint r <= 1 /\ W32.to_uint s <= 1.
proof.
  split.
  + have hr := W32.ule_orw r s.
    have hs := W32.ule_orw s r.
    rewrite W32.uleE in hr; rewrite W32.uleE W32.orwC in hs.
    smt().
  move=> [hr hs].
  have hr01 : r = W32.zero \/ r = W32.one.
  + have /= := W32.to_uint_cmp r; smt(W32.to_uint_eq W32.to_uint0 W32.to_uint1).
  have hs01 : s = W32.zero \/ s = W32.one.
  + have /= := W32.to_uint_cmp s; smt(W32.to_uint_eq W32.to_uint0 W32.to_uint1).
  case hr01 => ->; case hs01 => ->;
    by rewrite ?W32.or0w ?W32.orw0 ?W32.orwK /=.
qed.

op sotp_norm (r : W32.t) : W32.t =
  (W32.zero - (r `>>` W8.of_int 1)) `>>` W8.of_int 31.

lemma sotp_normalize (r : W32.t) : W32.to_uint r < 65536 =>
  sotp_norm r = W32.of_int (b2i (1 < W32.to_uint r)).
proof.
  move=> hr.
  have hn : W32.zero - (r `>>` W8.of_int 1) = -(r `>>` W8.of_int 1) by ring.
  apply W32.to_uint_eq.
  rewrite /sotp_norm hn.
  rewrite /W32.(`>>`) /= W32.to_uint_shr 1://
    W32.to_uintNE W32.to_uint_shr 1:// /= W32.of_uintK /=.
  have hnonneg := W32.to_uint_cmp r.
  case (1 < W32.to_uint r) => hc /=.
  + have hdiv : 0 < W32.to_uint r %/ 2 < 32768 by smt(divz_cmp divz_eqP).
    rewrite modz_small 1:/#.
    rewrite divz_eqP; smt().
  have -> : W32.to_uint r %/ 2 = 0 by rewrite divz_small; smt().
  done.
qed.

lemma sotp_mask (b : bool) :
  truncateu8 (W32.of_int (b2i b) - W32.one) =
    if b then W8.zero else W8.onew.
proof.
  case b => hb /=.
  + apply W8.to_uint_eq.
    by rewrite /truncateu8 /=.
  apply W8.to_uint_eq.
  by rewrite /truncateu8 W8.of_uintK W32.of_uintK W8.to_uint_onew /=.
qed.
