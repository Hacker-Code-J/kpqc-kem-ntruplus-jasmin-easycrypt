require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.

require import Array768 WArray1536 NTRUPlus768InvNTT.
require import NTRUPlus768InvNTTRadix2_4 NTRUPlus768InvNTTRadix2_8.
require import NTRUPlus768InvNTTRadix2_16 NTRUPlus768InvNTTRadix2_32.
require import NTRUPlus768InvNTTRadix2_64 NTRUPlus768InvNTTRadix3.
require import NTRUPlus768InvNTTFinal.
require import NTRUPlus768InvNTTRadix2_4Proof NTRUPlus768InvNTTRadix2_8Proof.
require import NTRUPlus768InvNTTRadix2_16Proof NTRUPlus768InvNTTRadix2_32Proof.
require import NTRUPlus768InvNTTRadix2_64Proof NTRUPlus768InvNTTRadix3Proof.
require import NTRUPlus768InvNTTFinalProof.

op n : int = 768.

op copy_prefix_spec
    (rp0 ap0 : W16.t Array768.t) (upto : int) : W16.t Array768.t =
  Array768.init (fun j => if 0 <= j < upto then ap0.[j] else rp0.[j]).

op invntt_spec (ap : W16.t Array768.t) : W16.t Array768.t =
  invntt_final_spec
    (invntt_radix3_spec
      (invntt_radix2_64_spec
        (invntt_radix2_32_spec
          (invntt_radix2_16_spec
            (invntt_radix2_8_spec
              (invntt_radix2_4_spec ap)))))).

lemma radix2_4_eq :
  equiv [NTRUPlus768InvNTT.M.radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 ~
         NTRUPlus768InvNTTRadix2_4.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 :
    ={rp} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma radix2_8_eq :
  equiv [NTRUPlus768InvNTT.M.radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 ~
         NTRUPlus768InvNTTRadix2_8.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 :
    ={rp} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma radix2_16_eq :
  equiv [NTRUPlus768InvNTT.M.radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 ~
         NTRUPlus768InvNTTRadix2_16.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 :
    ={rp} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma radix2_32_eq :
  equiv [NTRUPlus768InvNTT.M.radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32 ~
         NTRUPlus768InvNTTRadix2_32.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32 :
    ={rp} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma radix2_64_eq :
  equiv [NTRUPlus768InvNTT.M.radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 ~
         NTRUPlus768InvNTTRadix2_64.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 :
    ={rp} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma radix3_eq :
  equiv [NTRUPlus768InvNTT.M.radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 ~
         NTRUPlus768InvNTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 :
    ={rp} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma final_eq :
  equiv [NTRUPlus768InvNTT.M.final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final ~
         NTRUPlus768InvNTTFinal.M.jade_ntruplus_ntruplus768_amd64_ref_invntt_final :
    ={rp} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma copy_prefix_zero (rp0 ap0 : W16.t Array768.t) :
  copy_prefix_spec rp0 ap0 0 = rp0.
proof.
  apply Array768.tP => j Hj.
  rewrite /copy_prefix_spec Array768.initiE 1:Hj.
  smt().
qed.

lemma copy_prefix_step
    (rp0 ap0 : W16.t Array768.t) (upto : int) :
  0 <= upto < n =>
  (copy_prefix_spec rp0 ap0 upto).[upto <- ap0.[upto]] =
  copy_prefix_spec rp0 ap0 (upto + 1).
proof.
  move=> Hupto.
  apply Array768.tP => j Hj.
  rewrite /copy_prefix_spec Array768.initiE 1:Hj.
  case (j = upto) => [-> | Hneq].
  + by rewrite Array768.get_setE; smt().
  rewrite Array768.get_setE 1:/#.
  rewrite Array768.initiE 1:Hj.
  smt().
qed.

lemma copy_functional'
    (rp0 ap0 : W16.t Array768.t) :
  hoare [NTRUPlus768InvNTT.M.__invntt_copy :
    rp = rp0 /\ ap = ap0 ==> res = ap0].
proof.
  proc.
  seq 2 :
    (rp = copy_prefix_spec rp0 ap0 0 /\ ap = ap0 /\ i = W64.of_int 0).
  + auto => />.
    by rewrite copy_prefix_zero.
  while (0 <= W64.to_uint i <= n /\
         rp = copy_prefix_spec rp0 ap0 (W64.to_uint i) /\
         ap = ap0); last first.
  + skip => &hr [Hrp0 [Hap0 Hi0]].
    split.
    + split; first by rewrite Hi0 W64.to_uint0; smt().
      split.
      + by rewrite Hi0 W64.to_uint0.
      exact Hap0.
    move=> i1 rp1 Hexit [Hi [Hrp Hap]].
    rewrite W64.ultE /= in Hexit.
    have Hiend : W64.to_uint i1 = n by smt().
    have Hfull : copy_prefix_spec rp0 ap0 n = ap0.
    + apply Array768.tP => j Hj.
      rewrite /copy_prefix_spec Array768.initiE 1:Hj.
      smt().
    rewrite -Hfull -Hiend.
    exact Hrp.
  auto => /> &hr Hi Hrp Hloop.
  rewrite W64.ultE /= in Hloop.
  have Hidx : 0 <= W64.to_uint i{hr} < n by smt().
  have Hnext : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  have Hstep :
      (copy_prefix_spec rp0 ap0 (W64.to_uint i{hr}))
        .[W64.to_uint i{hr} <- ap0.[W64.to_uint i{hr}]] =
      copy_prefix_spec rp0 ap0 (W64.to_uint i{hr} + 1).
  + apply copy_prefix_step; smt().
  split.
  + rewrite Hnext; smt(W64.to_uint_cmp).
  rewrite Hnext -Hstep /=.
  done.
qed.

lemma copy_lossless' :
  islossless NTRUPlus768InvNTT.M.__invntt_copy.
proof.
  proc.
  while (0 <= W64.to_uint i <= n) (n - W64.to_uint i); last first.
  + auto => /> i0 Hi Hdone.
    rewrite W64.ultE /= /n.
    smt().
  auto => /> &hr Hi Hhi Hloop.
  rewrite W64.ultE /= in Hloop.
  rewrite W64.to_uintD_small /= /n; smt(W64.to_uint_cmp).
qed.

lemma radix2_4_functional'
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768InvNTT.M.radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 :
    rp = rp0 ==> res = invntt_radix2_4_spec rp0].
proof.
  conseq radix2_4_eq (invntt_radix2_4_functional rp0).
  + smt().
  smt().
qed.

lemma radix2_4_lossless' :
  islossless
    NTRUPlus768InvNTT.M.radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4.
proof.
  conseq radix2_4_eq invntt_radix2_4_lossless.
  + smt().
  smt().
qed.

lemma radix2_8_functional'
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768InvNTT.M.radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 :
    rp = rp0 ==> res = invntt_radix2_8_spec rp0].
proof.
  conseq radix2_8_eq (invntt_radix2_8_functional rp0).
  + smt().
  smt().
qed.

lemma radix2_8_lossless' :
  islossless
    NTRUPlus768InvNTT.M.radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8.
proof.
  conseq radix2_8_eq invntt_radix2_8_lossless.
  + smt().
  smt().
qed.

lemma radix2_16_functional'
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768InvNTT.M.radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 :
    rp = rp0 ==> res = invntt_radix2_16_spec rp0].
proof.
  conseq radix2_16_eq (invntt_radix2_16_functional rp0).
  + smt().
  smt().
qed.

lemma radix2_16_lossless' :
  islossless
    NTRUPlus768InvNTT.M.radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16.
proof.
  conseq radix2_16_eq invntt_radix2_16_lossless.
  + smt().
  smt().
qed.

lemma radix2_32_functional'
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768InvNTT.M.radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32 :
    rp = rp0 ==> res = invntt_radix2_32_spec rp0].
proof.
  conseq radix2_32_eq (invntt_radix2_32_functional rp0).
  + smt().
  smt().
qed.

lemma radix2_32_lossless' :
  islossless
    NTRUPlus768InvNTT.M.radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32.
proof.
  conseq radix2_32_eq invntt_radix2_32_lossless.
  + smt().
  smt().
qed.

lemma radix2_64_functional'
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768InvNTT.M.radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 :
    rp = rp0 ==> res = invntt_radix2_64_spec rp0].
proof.
  conseq radix2_64_eq (invntt_radix2_64_functional rp0).
  + smt().
  smt().
qed.

lemma radix2_64_lossless' :
  islossless
    NTRUPlus768InvNTT.M.radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64.
proof.
  conseq radix2_64_eq invntt_radix2_64_lossless.
  + smt().
  smt().
qed.

lemma radix3_functional'
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768InvNTT.M.radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 :
    rp = rp0 ==> res = invntt_radix3_spec rp0].
proof.
  conseq radix3_eq (invntt_radix3_functional rp0).
  + smt().
  smt().
qed.

lemma radix3_lossless' :
  islossless
    NTRUPlus768InvNTT.M.radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3.
proof.
  conseq radix3_eq invntt_radix3_lossless.
  + smt().
  smt().
qed.

lemma final_functional'
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768InvNTT.M.final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final :
    rp = rp0 ==> res = invntt_final_spec rp0].
proof.
  conseq final_eq (invntt_final_functional rp0).
  + smt().
  smt().
qed.

lemma final_lossless' :
  islossless
    NTRUPlus768InvNTT.M.final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final.
proof.
  conseq final_eq invntt_final_lossless.
  + smt().
  smt().
qed.

lemma invntt_functional
    (rp0 ap0 : W16.t Array768.t) :
  hoare [NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt :
    rp = rp0 /\ ap = ap0 ==> res = invntt_spec ap0].
proof.
  proc.
  call (final_functional' (invntt_radix3_spec
      (invntt_radix2_64_spec
        (invntt_radix2_32_spec
          (invntt_radix2_16_spec
            (invntt_radix2_8_spec
              (invntt_radix2_4_spec ap0))))))).
  call (radix3_functional' (invntt_radix2_64_spec
      (invntt_radix2_32_spec
        (invntt_radix2_16_spec
          (invntt_radix2_8_spec
            (invntt_radix2_4_spec ap0)))))).
  call (radix2_64_functional' (invntt_radix2_32_spec
      (invntt_radix2_16_spec
        (invntt_radix2_8_spec
          (invntt_radix2_4_spec ap0))))).
  call (radix2_32_functional' (invntt_radix2_16_spec
      (invntt_radix2_8_spec
        (invntt_radix2_4_spec ap0)))).
  call (radix2_16_functional' (invntt_radix2_8_spec
      (invntt_radix2_4_spec ap0))).
  call (radix2_8_functional' (invntt_radix2_4_spec ap0)).
  call (radix2_4_functional' ap0).
  call (copy_functional' rp0 ap0).
  auto => />.
qed.

lemma invntt_lossless :
  islossless NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt.
proof.
  proc.
  call final_lossless'.
  call radix3_lossless'.
  call radix2_64_lossless'.
  call radix2_32_lossless'.
  call radix2_16_lossless'.
  call radix2_8_lossless'.
  call radix2_4_lossless'.
  call copy_lossless'.
  auto => />.
qed.

lemma invntt_correct
    (rp0 ap0 : W16.t Array768.t) :
  phoare [NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt :
    rp = rp0 /\ ap = ap0 ==> res = invntt_spec ap0] = 1%r.
proof.
  by conseq invntt_lossless (invntt_functional rp0 ap0).
qed.
