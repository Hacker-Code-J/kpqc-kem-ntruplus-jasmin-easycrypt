require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.
require import NTRUPlus768PolySOTPDecodeChecked NTRUPlus768PolySOTPDecodeBitProof.

lemma poly_sotp_decode_lossless : islossless
  NTRUPlus768PolySOTPDecodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode.
proof.
  proc.
  while (0<=W64.to_uint i<=96) (96-W64.to_uint i).
  + auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  wp.
  while (0<=W64.to_uint i<=96) (96-W64.to_uint i).
  + move=> z; wp.
    do 8! call sotp_decode_bit_lossless.
    auto => /> &hr hlo hhi hloop.
    rewrite W64.ultE /= in hloop.
    rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  auto => />.
  move=> i0; split.
  + move=> hlo hhi hz; rewrite W64.ultE /=; smt().
  move=> hdone hlo hhi i1 h1lo h1hi h1z; rewrite W64.ultE /=; smt().
qed.
