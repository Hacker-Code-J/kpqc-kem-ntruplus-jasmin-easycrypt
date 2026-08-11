require import AllCore.
from Jasmin require import JWord JModel_x86.

require import Array4 NTRUPlus768Basemul.

(* The extracted array model represents the three buffers independently,
   matching the non-aliasing contract exercised by the C differential test. *)

(* Signed 16-bit multiplication lifted to the 32-bit word used by C/Jasmin. *)
op mul_i16 (a b : W16.t) : W32.t = sigextu32 a * sigextu32 b.

(* Exact word-level counterpart of NTRU+/NTRU+768/ntt.c::montgomery_reduce. *)
op montgomery_reduce (a : W32.t) : W16.t =
  let t = truncateu16 (a * W32.of_int 12929) in
  truncateu16
    ((a - sigextu32 t * W32.of_int 3457) `|>>` W8.of_int 16).

(* Multiplication in the four-coefficient NTT block, including R^2 scaling. *)
op basemul_spec
    (out a b : W16.t Array4.t, z : W16.t) : W16.t Array4.t =
  let t0 = montgomery_reduce
    (mul_i16 a.[1] b.[3] + mul_i16 a.[2] b.[2] +
     mul_i16 a.[3] b.[1]) in
  let t1 = montgomery_reduce
    (mul_i16 a.[2] b.[3] + mul_i16 a.[3] b.[2]) in
  let t2 = montgomery_reduce (mul_i16 a.[3] b.[3]) in
  let r0 = montgomery_reduce (mul_i16 t0 z + mul_i16 a.[0] b.[0]) in
  let r1 = montgomery_reduce
    (mul_i16 t1 z + mul_i16 a.[0] b.[1] + mul_i16 a.[1] b.[0]) in
  let r2 = montgomery_reduce
    (mul_i16 t2 z + mul_i16 a.[0] b.[2] + mul_i16 a.[1] b.[1] +
     mul_i16 a.[2] b.[0]) in
  let r3 = montgomery_reduce
    (mul_i16 a.[0] b.[3] + mul_i16 a.[1] b.[2] +
     mul_i16 a.[2] b.[1] + mul_i16 a.[3] b.[0]) in
  out
    .[0 <- montgomery_reduce (mul_i16 r0 (W16.of_int 867))]
    .[1 <- montgomery_reduce (mul_i16 r1 (W16.of_int 867))]
    .[2 <- montgomery_reduce (mul_i16 r2 (W16.of_int 867))]
    .[3 <- montgomery_reduce (mul_i16 r3 (W16.of_int 867))].

lemma mul_i16_functional (a0 b0 : W16.t) :
  hoare [NTRUPlus768Basemul.M.__mul_i16 :
    a = a0 /\ b = b0 ==> res = mul_i16 a0 b0].
proof.
  proc; auto => />.
qed.

lemma montgomery_reduce_functional (a0 : W32.t) :
  hoare [NTRUPlus768Basemul.M.__montgomery_reduce :
    a = a0 ==> res = montgomery_reduce a0].
proof.
  proc; auto => />.
qed.

lemma basemul_functional
    (out0 a0 b0 : W16.t Array4.t) (z0 : W16.t) :
  hoare [NTRUPlus768Basemul.M.jade_ntruplus_ntruplus768_amd64_ref_basemul :
    rp = out0 /\ ap = a0 /\ bp = b0 /\ zeta_0 = z0 ==>
    res = basemul_spec out0 a0 b0 z0].
proof.
  proc; inline NTRUPlus768Basemul.M.__mul_i16
               NTRUPlus768Basemul.M.__montgomery_reduce;
  wp; skip => &hr [#] /= -> -> -> ->.
  by rewrite /basemul_spec /mul_i16 /montgomery_reduce.
qed.

lemma basemul_lossless :
  islossless
    NTRUPlus768Basemul.M.jade_ntruplus_ntruplus768_amd64_ref_basemul.
proof.
  proc; inline NTRUPlus768Basemul.M.__mul_i16
               NTRUPlus768Basemul.M.__montgomery_reduce;
  islossless.
qed.

lemma basemul_correct
    (out0 a0 b0 : W16.t Array4.t) (z0 : W16.t) :
  phoare [NTRUPlus768Basemul.M.jade_ntruplus_ntruplus768_amd64_ref_basemul :
    rp = out0 /\ ap = a0 /\ bp = b0 /\ zeta_0 = z0 ==>
    res = basemul_spec out0 a0 b0 z0] = 1%r.
proof.
  by conseq basemul_lossless (basemul_functional out0 a0 b0 z0).
qed.
