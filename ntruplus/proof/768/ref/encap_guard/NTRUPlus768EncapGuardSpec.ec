require import AllCore IntDiv List.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array32 NTRUPlus768CanonicalDecoder.

op encap_key_canonical (pk : W8.t Array1152.t) : bool =
  forall j, 0 <= j < 768 => W16.to_uint (decoded_poly pk).[j] < 3457.

op encap_zero_ct : W8.t Array1152.t = Array1152.init (fun _ => W8.zero).
op encap_zero_ss : W8.t Array32.t = Array32.init (fun _ => W8.zero).

op encap_status (pk : W8.t Array1152.t) : W32.t =
  if encap_key_canonical pk then W32.zero else W32.one.

op encap_guard_spec (ct : W8.t Array1152.t) (ss : W8.t Array32.t)
    (pk : W8.t Array1152.t) : W16.t Array768.t * W8.t Array1152.t * W8.t Array32.t * W32.t =
  (decoded_poly pk,
   if encap_key_canonical pk then ct else encap_zero_ct,
   if encap_key_canonical pk then ss else encap_zero_ss,
   encap_status pk).

lemma encap_decoder_status pk :
  canonical_acc pk 384 `>>>` 31 = encap_status pk.
proof.
  have hs := canonical_return_success_iff pk.
  have hb := canonical_return_binary pk.
  rewrite -/encap_key_canonical in hs.
  apply W32.to_uint_eq.
  rewrite /encap_status.
  case (encap_key_canonical pk) => hk /=.
  + rewrite -/canonical_return.
    exact (iffRL _ _ hs hk).
  rewrite -/canonical_return.
  smt().
qed.

lemma encap_status_zero pk : encap_status pk = W32.zero <=> encap_key_canonical pk.
proof.
  rewrite /encap_status; case (encap_key_canonical pk); smt(W32.to_uint0 W32.to_uint1).
qed.

lemma encap_zero_ct_get j : 0 <= j < 1152 => encap_zero_ct.[j] = W8.zero.
proof. by move=> hj; rewrite /encap_zero_ct Array1152.initiE. qed.

lemma encap_zero_ss_get j : 0 <= j < 32 => encap_zero_ss.[j] = W8.zero.
proof. by move=> hj; rewrite /encap_zero_ss Array32.initiE. qed.

op encap_ct_zero_prefix (ct : W8.t Array1152.t) (n : int) : bool =
  forall j, 0 <= j < n => ct.[j] = W8.zero.
op encap_ss_zero_prefix (ss : W8.t Array32.t) (n : int) : bool =
  forall j, 0 <= j < n => ss.[j] = W8.zero.

lemma encap_ct_zero_step ct i :
  0 <= i < 1152 => encap_ct_zero_prefix ct i =>
  encap_ct_zero_prefix ct.[i <- W8.zero] (i+1).
proof.
  move=> hi hp j hj.
  case (j=i) => hji; first smt(Array1152.get_setE).
  have hold := hp j _; first smt().
  smt(Array1152.get_setE).
qed.

lemma encap_ss_zero_step ss i :
  0 <= i < 32 => encap_ss_zero_prefix ss i =>
  encap_ss_zero_prefix ss.[i <- W8.zero] (i+1).
proof.
  move=> hi hp j hj.
  case (j=i) => hji; first smt(Array32.get_setE).
  have hold := hp j _; first smt().
  smt(Array32.get_setE).
qed.

lemma encap_ct_zero_full ct : encap_ct_zero_prefix ct 1152 => ct = encap_zero_ct.
proof. move=> hp; apply Array1152.tP => j hj; by rewrite (hp j hj) encap_zero_ct_get. qed.

lemma encap_ss_zero_full ss : encap_ss_zero_prefix ss 32 => ss = encap_zero_ss.
proof. move=> hp; apply Array32.tP => j hj; by rewrite (hp j hj) encap_zero_ss_get. qed.
