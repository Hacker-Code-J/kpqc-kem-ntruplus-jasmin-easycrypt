require import AllCore IntDiv List.
from Jasmin require import JWord JModel_x86.
require import Array768 Array1152 Array2304 Array32 NTRUPlus768CanonicalDecoder.
require import NTRUPlus768EncapGuardSpec.

op decap_fbytes (skpoly : W8.t Array2304.t) : W8.t Array1152.t =
  Array1152.init (fun i => skpoly.[0+i]).
op decap_hbytes (skpoly : W8.t Array2304.t) : W8.t Array1152.t =
  Array1152.init (fun i => skpoly.[1152+i]).

(* Canonical here means only byte-encoding validity, not the algebraic
   secret/public-key relation needed by message recovery or KEM security. *)
op decap_key_encoding_valid (fbytes hbytes : W8.t Array1152.t) : bool =
  encap_key_canonical fbytes /\ encap_key_canonical hbytes.

op decap_guard_accepts (ct fbytes hbytes : W8.t Array1152.t) : bool =
  encap_key_canonical ct /\ decap_key_encoding_valid fbytes hbytes.

op decap_guard_status (ct fbytes hbytes : W8.t Array1152.t) : W32.t =
  if decap_guard_accepts ct fbytes hbytes then W32.zero else W32.one.

op decap_guard_spec (fp hp : W16.t Array768.t) (ss : W8.t Array32.t)
    (ct fbytes hbytes : W8.t Array1152.t) :
    W16.t Array768.t * W16.t Array768.t * W16.t Array768.t * W8.t Array32.t * W32.t =
  (decoded_poly ct,
   if encap_key_canonical ct then decoded_poly fbytes else fp,
   if encap_key_canonical ct /\ encap_key_canonical fbytes then decoded_poly hbytes else hp,
   if decap_guard_accepts ct fbytes hbytes then ss else encap_zero_ss,
   decap_guard_status ct fbytes hbytes).

lemma decap_guard_status_zero ct fbytes hbytes :
  decap_guard_status ct fbytes hbytes = W32.zero <=> decap_guard_accepts ct fbytes hbytes.
proof.
  rewrite /decap_guard_status; case (decap_guard_accepts ct fbytes hbytes);
  smt(W32.to_uint0 W32.to_uint1).
qed.

(* The secret-key validation bits explicitly disclosed by the implementation
   are constant under the stated encoding-validity precondition. This is a
   value theorem, not a proof of the compiler's CT/SCT judgment. *)
lemma decap_key_validation_bits_zero fbytes hbytes :
  decap_key_encoding_valid fbytes hbytes =>
  encap_status fbytes = W32.zero /\ encap_status hbytes = W32.zero.
proof. rewrite /decap_key_encoding_valid !encap_status_zero; trivial. qed.

lemma decap_valid_key_guard_status_public ct fbytes hbytes :
  decap_key_encoding_valid fbytes hbytes =>
  decap_guard_status ct fbytes hbytes = encap_status ct.
proof.
  move=> hk; by rewrite /decap_guard_status /decap_guard_accepts hk /encap_status /=.
qed.

lemma decap_valid_keys_guard_status_equal ct f1 h1 f2 h2 :
  decap_key_encoding_valid f1 h1 => decap_key_encoding_valid f2 h2 =>
  decap_guard_status ct f1 h1 = decap_guard_status ct f2 h2.
proof. move=> h1v h2v; by rewrite !decap_valid_key_guard_status_public. qed.
