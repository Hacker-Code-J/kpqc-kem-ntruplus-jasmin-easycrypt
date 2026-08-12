require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.

require import Array4 Array96 Array768 WArray8 WArray192 WArray1536.
require import NTRUPlus768PolyBasemul NTRUPlus768BasemulProof.

op block4 (p : W16.t Array768.t) (k : int) : W16.t Array4.t =
  Array4.init (fun j => p.[4 * k + j]).

op block_zeta (k : int) : W16.t =
  if k %% 2 = 0 then
    nTRUPLUS_ZETAS96.[k %/ 2]
  else
    -nTRUPLUS_ZETAS96.[k %/ 2].

op basemul_block_spec
    (ap bp : W16.t Array768.t) (k : int) : W16.t Array4.t =
  basemul_spec witness (block4 ap k) (block4 bp k) (block_zeta k).

op load4 (p : W16.t Array768.t) (off : int) : W16.t Array4.t =
  Array4.init (fun j => p.[off + j]).

op is_poly_basemul
    (ap bp rp : W16.t Array768.t) (upto : int) : bool =
  forall k, 0 <= k < upto =>
    block4 rp k = basemul_block_spec ap bp k.

op write_block4
    (p : W16.t Array768.t) (k : int) (v : W16.t Array4.t)
    : W16.t Array768.t =
  p.[4 * k <- v.[0]]
   .[4 * k + 1 <- v.[1]]
   .[4 * k + 2 <- v.[2]]
   .[4 * k + 3 <- v.[3]].

lemma load4_eq_block4
    (p : W16.t Array768.t) (k : int) :
  0 <= k < 192 =>
  load4 p (4 * k) = block4 p k.
proof.
  move=> Hk.
  apply Array4.tP => j Hj.
  by rewrite /load4 /block4 !Array4.initiE 1,2:/#.
qed.

lemma load4_updates
    (dst : W16.t Array4.t) (p : W16.t Array768.t) (off : int) :
  dst.[0 <- p.[off]]
     .[1 <- p.[off + 1]]
     .[2 <- p.[off + 2]]
     .[3 <- p.[off + 3]] = load4 p off.
proof.
  apply Array4.tP => j Hj.
  have Hcases : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
  elim Hcases => [-> | [-> | [-> | ->]]];
    by rewrite /load4 Array4.initiE 1:/# !Array4.get_setE.
qed.

lemma basemul_spec_out_irrelevant
    (out1 out2 a b : W16.t Array4.t) (z : W16.t) :
  basemul_spec out1 a b z = basemul_spec out2 a b z.
proof.
  apply Array4.tP => j Hj.
  have Hcases : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
  elim Hcases => [-> | [-> | [-> | ->]]];
    by rewrite /basemul_spec.
qed.

lemma basemul_spec_to_witness
    (out a b : W16.t Array4.t) (z : W16.t) :
  basemul_spec out a b z = basemul_spec witness a b z.
proof.
  exact (basemul_spec_out_irrelevant out witness a b z).
qed.

lemma basemul4_functional_local
    (r0 a0 b0 : W16.t Array4.t) (z0 : W16.t) :
  hoare [NTRUPlus768PolyBasemul.M.__basemul4 :
    r = r0 /\ a = a0 /\ b = b0 /\ zeta_0 = z0 ==>
    res = basemul_spec r0 a0 b0 z0].
proof.
  proc; inline NTRUPlus768PolyBasemul.M.__mul_i16
               NTRUPlus768PolyBasemul.M.__montgomery_reduce;
  wp; skip => &hr [#] /= -> -> -> ->.
  apply Array4.tP => k Hk.
  have Hcases : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 by smt().
  elim Hcases => [-> | [-> | [-> | ->]]];
    by rewrite /basemul_spec /mul_i16 /montgomery_reduce !Array4.get_setE.
qed.

lemma basemul4_lossless_local :
  islossless NTRUPlus768PolyBasemul.M.__basemul4.
proof.
  proc; inline NTRUPlus768PolyBasemul.M.__mul_i16
               NTRUPlus768PolyBasemul.M.__montgomery_reduce;
  islossless.
qed.

lemma block4_write_same
    (p : W16.t Array768.t) (k : int) (v : W16.t Array4.t) :
  0 <= k < 192 =>
  block4 (write_block4 p k v) k = v.
proof.
  move=> Hk.
  apply Array4.tP => j Hj.
  smt(Array4.initiE Array768.get_setE).
qed.

lemma block4_write_other
    (p : W16.t Array768.t) (k1 k2 : int) (v : W16.t Array4.t) :
  0 <= k1 < 192 =>
  0 <= k2 < 192 =>
  k1 <> k2 =>
  block4 (write_block4 p k1 v) k2 = block4 p k2.
proof.
  move=> Hk1 Hk2 Hneq.
  apply Array4.tP => j Hj.
  smt(Array4.initiE Array768.get_setE).
qed.

lemma block_zeta_even (i : int) :
  0 <= i < 96 =>
  block_zeta (2 * i) = nTRUPLUS_ZETAS96.[i].
proof.
  move=> Hi.
  rewrite /block_zeta /=.
  have -> : (2 * i) %% 2 = 0 by smt().
  have -> : (2 * i) %/ 2 = i by smt().
  done.
qed.

lemma block_zeta_odd (i : int) :
  0 <= i < 96 =>
  block_zeta (2 * i + 1) = -nTRUPLUS_ZETAS96.[i].
proof.
  move=> Hi.
  rewrite /block_zeta /=.
  have -> : (2 * i + 1) %% 2 = 1 by smt().
  have -> : (2 * i + 1) %/ 2 = i by smt().
  done.
qed.

lemma is_poly_basemul_extend
    (ap bp rp : W16.t Array768.t) (k : int) (v : W16.t Array4.t) :
  0 <= k < 192 =>
  is_poly_basemul ap bp rp k =>
  v = basemul_block_spec ap bp k =>
  is_poly_basemul ap bp (write_block4 rp k v) (k + 1).
proof.
  move=> Hk Hrp Hv k' Hk'.
  case (k' = k) => [-> | Hneq].
  + rewrite block4_write_same 1:Hk.
    exact Hv.
  have Hlt : 0 <= k' < k by smt().
  have Hsame :
      block4 (write_block4 rp k v) k' = block4 rp k'.
  + apply block4_write_other; smt().
  have Hcurr := Hrp k' Hlt.
  rewrite Hsame.
  exact Hcurr.
qed.

lemma poly_basemul_functional
    (rp0 ap0 bp0 : W16.t Array768.t) :
  hoare [NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==>
    is_poly_basemul ap0 bp0 res 192].
proof.
  proc.
  seq 7 :
    (ap = ap0 /\ bp = bp0 /\
     zetasp = Array96.init (fun j => nTRUPLUS_ZETAS96.[0 + j]) /\
     i = W64.of_int 0 /\
     is_poly_basemul ap0 bp0 rp 0).
  + auto => />; smt(Array96.initiE).
  while (0 <= W64.to_uint i <= 96 /\
         ap = ap0 /\ bp = bp0 /\
         zetasp = Array96.init (fun j => nTRUPLUS_ZETAS96.[0 + j]) /\
         is_poly_basemul ap0 bp0 rp (2 * W64.to_uint i)); last first.
  + skip => &hr [Hap [Hbp [Hzet [Hi0 Hspec0]]]].
    split.
    - split; first by rewrite Hi0 W64.to_uint0; smt().
      split; first exact Hap.
      split; first exact Hbp.
      split; first exact Hzet.
      by rewrite Hi0 W64.to_uint0 /=.
    move=> i1 rp1 Hexit [Hi [Hap1 [Hbp1 [Hzet1 Hspec1]]]].
    rewrite W64.ultE /= in Hexit.
    smt().
  wp.
  ecall (basemul4_functional_local tr ta tb (-zeta_0)).
  wp.
  ecall (basemul4_functional_local tr ta tb zeta_0).
  auto => /> &hr HiLow HiHigh Hspec Hloop.
  have Hi96 : 0 <= W64.to_uint i{hr} < 96.
  + rewrite W64.ultE /= in Hloop.
    smt().
  have Hoff :
      W64.to_uint (i{hr} `<<` W8.of_int 3) =
      8 * W64.to_uint i{hr}.
  + rewrite /(`<<`) /=.
    rewrite W64.to_uint_shl 1:/# /=.
    rewrite modz_small 1:/#.
    ring.
  have Hoff4 :
      W64.to_uint ((i{hr} `<<` W8.of_int 3) + W64.of_int 4) =
      8 * W64.to_uint i{hr} + 4.
  + rewrite W64.to_uintD_small.
    - rewrite Hoff /=; smt().
    by rewrite Hoff /=.
  have HoffN : forall n,
      0 <= n <= 7 =>
      W64.to_uint ((i{hr} `<<` W8.of_int 3) + W64.of_int n) =
      8 * W64.to_uint i{hr} + n.
  + move=> n Hn.
    rewrite W64.to_uintD_small.
    - rewrite Hoff W64.of_uintK modz_small 1:/#.
      smt().
    by rewrite Hoff W64.of_uintK modz_small 1:/#.
  have Hoff1 := HoffN 1 _; first smt().
  have Hoff2 := HoffN 2 _; first smt().
  have Hoff3 := HoffN 3 _; first smt().
  have Hoff5 := HoffN 5 _; first smt().
  have Hoff6 := HoffN 6 _; first smt().
  have Hoff7 := HoffN 7 _; first smt().
  have Hload0 : forall (dst : W16.t Array4.t) (p : W16.t Array768.t),
      dst.[0 <- p.[8 * W64.to_uint i{hr}]]
         .[1 <- p.[8 * W64.to_uint i{hr} + 1]]
         .[2 <- p.[8 * W64.to_uint i{hr} + 2]]
         .[3 <- p.[8 * W64.to_uint i{hr} + 3]] =
      block4 p (2 * W64.to_uint i{hr}).
  + move=> dst p.
    rewrite load4_updates.
    have -> : 8 * W64.to_uint i{hr} =
        4 * (2 * W64.to_uint i{hr}) by ring.
    apply load4_eq_block4; smt().
  have Hload1 : forall (dst : W16.t Array4.t) (p : W16.t Array768.t),
      dst.[0 <- p.[8 * W64.to_uint i{hr} + 4]]
         .[1 <- p.[8 * W64.to_uint i{hr} + 5]]
         .[2 <- p.[8 * W64.to_uint i{hr} + 6]]
         .[3 <- p.[8 * W64.to_uint i{hr} + 7]] =
      block4 p (2 * W64.to_uint i{hr} + 1).
  + move=> dst p.
    rewrite load4_updates.
    have -> : 8 * W64.to_uint i{hr} + 4 =
        4 * (2 * W64.to_uint i{hr} + 1) by ring.
    apply load4_eq_block4; smt().
  have Hspec0 :
      basemul_spec witness
        (block4 ap0 (2 * W64.to_uint i{hr}))
        (block4 bp0 (2 * W64.to_uint i{hr}))
        nTRUPLUS_ZETAS96.[W64.to_uint i{hr}] =
      basemul_block_spec ap0 bp0 (2 * W64.to_uint i{hr}).
  + by rewrite /basemul_block_spec block_zeta_even 1:/#.
  have Hspec1 :
      basemul_spec witness
        (block4 ap0 (2 * W64.to_uint i{hr} + 1))
        (block4 bp0 (2 * W64.to_uint i{hr} + 1))
        (-nTRUPLUS_ZETAS96.[W64.to_uint i{hr}]) =
      basemul_block_spec ap0 bp0 (2 * W64.to_uint i{hr} + 1).
  + by rewrite /basemul_block_spec block_zeta_odd 1:/#.
  have Hzeta :
      (Array96.init (fun j => nTRUPLUS_ZETAS96.[0 + j])).[
        W64.to_uint i{hr}] =
      nTRUPLUS_ZETAS96.[W64.to_uint i{hr}].
  + by rewrite Array96.initiE 1:/# /=.
  have Hcall0 :
      basemul_spec tr{hr}
        (block4 ap0 (2 * W64.to_uint i{hr}))
        (block4 bp0 (2 * W64.to_uint i{hr}))
        nTRUPLUS_ZETAS96.[W64.to_uint i{hr}] =
      basemul_block_spec ap0 bp0 (2 * W64.to_uint i{hr}).
  + by rewrite basemul_spec_to_witness Hspec0.
  have Hcall1 :
      basemul_spec
        (basemul_block_spec ap0 bp0 (2 * W64.to_uint i{hr}))
        (block4 ap0 (2 * W64.to_uint i{hr} + 1))
        (block4 bp0 (2 * W64.to_uint i{hr} + 1))
        (-nTRUPLUS_ZETAS96.[W64.to_uint i{hr}]) =
      basemul_block_spec ap0 bp0 (2 * W64.to_uint i{hr} + 1).
  + by rewrite basemul_spec_to_witness Hspec1.
  have Hnext :
      W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  split.
  + rewrite Hnext; smt().
  pose rp1 :=
    write_block4 rp{hr} (2 * W64.to_uint i{hr})
      (basemul_block_spec ap0 bp0 (2 * W64.to_uint i{hr})).
  have Hrp1 :
      is_poly_basemul ap0 bp0 rp1 (2 * W64.to_uint i{hr} + 1).
  + apply is_poly_basemul_extend.
    - smt(W64.to_uint_cmp).
    - exact Hspec.
    - done.
  rewrite Hoff Hoff1 Hoff2 Hoff3 Hoff4 Hoff5 Hoff6 Hoff7.
  rewrite !Hload0 !Hload1.
  rewrite !Hzeta.
  rewrite !Hcall0 !Hcall1.
  rewrite Hnext.
  rewrite (: 8 * W64.to_uint i{hr} =
      4 * (2 * W64.to_uint i{hr})) 1:/#.
  rewrite (: 4 * (2 * W64.to_uint i{hr}) + 4 =
      4 * (2 * W64.to_uint i{hr} + 1)) 1:/#.
  rewrite (: 4 * (2 * W64.to_uint i{hr}) + 5 =
      4 * (2 * W64.to_uint i{hr} + 1) + 1) 1:/#.
  rewrite (: 4 * (2 * W64.to_uint i{hr}) + 6 =
      4 * (2 * W64.to_uint i{hr} + 1) + 2) 1:/#.
  rewrite (: 4 * (2 * W64.to_uint i{hr}) + 7 =
      4 * (2 * W64.to_uint i{hr} + 1) + 3) 1:/#.
  rewrite (: 2 * (W64.to_uint i{hr} + 1) =
      (2 * W64.to_uint i{hr} + 1) + 1) 1:/#.
  apply is_poly_basemul_extend.
  + smt(W64.to_uint_cmp).
  + exact Hrp1.
  done.
qed.

lemma poly_basemul_lossless :
  islossless
    NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul.
proof.
  proc.
  while (0 <= W64.to_uint i <= 96) (96 - W64.to_uint i);
    last first.
  + auto => /> i0 Hi Hdone.
    rewrite W64.ultE /=.
    smt().
  move=> *.
  wp; call basemul4_lossless_local.
  wp; call basemul4_lossless_local.
  auto => /> &hr Hi Hhigh Hloop.
  rewrite W64.ultE /= in Hloop.
  rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
qed.

lemma poly_basemul_correct
    (rp0 ap0 bp0 : W16.t Array768.t) :
  phoare [NTRUPlus768PolyBasemul.M.jade_ntruplus_ntruplus768_amd64_ref_poly_basemul :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==>
    is_poly_basemul ap0 bp0 res 192] = 1%r.
proof.
  by conseq poly_basemul_lossless (poly_basemul_functional rp0 ap0 bp0).
qed.
