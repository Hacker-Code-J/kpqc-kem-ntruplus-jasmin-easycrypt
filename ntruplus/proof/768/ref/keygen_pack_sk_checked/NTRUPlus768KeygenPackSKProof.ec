require import AllCore IntDiv List Distr.
from Jasmin require import JWord JModel_x86.
require import Array32 Array1152 Array2336 NTRUPlus768KeygenPackSK.

op keygen_pack_sk_byte (fbytes hinvbytes : W8.t Array1152.t)
  (hash_f : W8.t Array32.t) (j : int) : W8.t =
  if j < 1152 then fbytes.[j]
  else if j < 2304 then hinvbytes.[j-1152] else hash_f.[j-2304].

op keygen_pack_sk_spec (fbytes hinvbytes : W8.t Array1152.t)
  (hash_f : W8.t Array32.t) : W8.t Array2336.t =
  Array2336.init (keygen_pack_sk_byte fbytes hinvbytes hash_f).

lemma keygen_pack_sk_functional sk0 f0 h0 hf0 :
  hoare [NTRUPlus768KeygenPackSK.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_pack_sk :
    sk = sk0 /\ fbytes = f0 /\ hinvbytes = h0 /\ hash_f = hf0 ==>
    res = keygen_pack_sk_spec f0 h0 hf0].
proof.
  proc.
  while (fbytes = f0 /\ hinvbytes = h0 /\ hash_f = hf0 /\
    0 <= W64.to_uint i <= 2336 /\
    forall j, 0 <= j < W64.to_uint i => sk.[j] = keygen_pack_sk_byte f0 h0 hf0 j);
    last first.
  + auto => />.
    split; first smt().
    move=> i1 sk1 hdone hlo hhi hprefix.
    rewrite W64.ultE /= in hdone.
    have hi : W64.to_uint i1 = 2336 by smt().
    apply Array2336.tP => j hj.
    rewrite /keygen_pack_sk_spec Array2336.initiE //.
    apply hprefix; smt().
  if.
  + auto => /> &hr hlo hhi hprefix hloop hfirst.
    rewrite W64.ultE /= in hloop; rewrite W64.ultE /= in hfirst.
    have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
    + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
    rewrite hn.
    split; first smt().
    move=> j hjlo hjhi.
    rewrite Array2336.get_setE 1:/# /= /keygen_pack_sk_byte; smt().
  if.
  + auto => /> &hr hlo hhi hprefix hloop hfirst hsecond.
    rewrite W64.ultE /= in hloop; rewrite W64.ultE /= in hfirst; rewrite W64.ultE /= in hsecond.
    have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
    + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
    have hs : W64.to_uint (i{hr} - W64.of_int 1152) = W64.to_uint i{hr} - 1152.
    + rewrite W64.to_uintB; first by rewrite W64.uleE /=; smt().
    by rewrite /=.
    rewrite hn hs.
    split; first smt().
    move=> j hjlo hjhi.
    rewrite Array2336.get_setE 1:/# /= /keygen_pack_sk_byte; smt().
  auto => /> &hr hlo hhi hprefix hloop hfirst hsecond.
  rewrite W64.ultE /= in hloop; rewrite W64.ultE /= in hfirst; rewrite W64.ultE /= in hsecond.
  have hn : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  have hs : W64.to_uint (i{hr} - W64.of_int 2304) = W64.to_uint i{hr} - 2304.
  + rewrite W64.to_uintB; first by rewrite W64.uleE /=; smt().
    by rewrite /=.
  rewrite hn hs.
  split; first smt().
  move=> j hjlo hjhi.
  rewrite Array2336.get_setE 1:/# /= /keygen_pack_sk_byte; smt().
qed.

lemma keygen_pack_sk_lossless : islossless
  NTRUPlus768KeygenPackSK.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_pack_sk.
proof.
  proc.
  while (0 <= W64.to_uint i <= 2336) (2336 - W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  auto => /> i hlo hhi hd; rewrite W64.ultE /=; smt().
qed.

lemma keygen_pack_sk_correct sk0 f0 h0 hf0 :
  phoare [NTRUPlus768KeygenPackSK.M.jade_ntruplus_ntruplus768_amd64_ref_keygen_pack_sk :
    sk = sk0 /\ fbytes = f0 /\ hinvbytes = h0 /\ hash_f = hf0 ==>
    res = keygen_pack_sk_spec f0 h0 hf0] = 1%r.
proof. by conseq keygen_pack_sk_lossless (keygen_pack_sk_functional sk0 f0 h0 hf0). qed.

lemma keygen_pack_sk_bytes f0 h0 hf0 j : 0 <= j < 2336 =>
  (keygen_pack_sk_spec f0 h0 hf0).[j] = keygen_pack_sk_byte f0 h0 hf0 j.
proof. by move=> hj; rewrite /keygen_pack_sk_spec Array2336.initiE. qed.

lemma keygen_pack_sk_components f0 h0 hf0 :
  Array1152.init (fun j => (keygen_pack_sk_spec f0 h0 hf0).[j]) = f0 /\
  Array1152.init (fun j => (keygen_pack_sk_spec f0 h0 hf0).[1152+j]) = h0 /\
  Array32.init (fun j => (keygen_pack_sk_spec f0 h0 hf0).[2304+j]) = hf0.
proof.
  split.
  + apply Array1152.tP => j hj; rewrite Array1152.initiE // /keygen_pack_sk_spec /keygen_pack_sk_byte.
    smt(Array2336.initiE).
  split.
  + apply Array1152.tP => j hj; rewrite Array1152.initiE // /keygen_pack_sk_spec /keygen_pack_sk_byte.
    smt(Array2336.initiE).
  apply Array32.tP => j hj; rewrite Array32.initiE // /keygen_pack_sk_spec /keygen_pack_sk_byte.
  smt(Array2336.initiE).
qed.
