require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.

require import Array768 WArray1536 NTRUPlus768NTT.
require import NTRUPlus768NTTStage1 NTRUPlus768NTTRadix3.
require import NTRUPlus768NTTRadix2_64 NTRUPlus768NTTRadix2_32.
require import NTRUPlus768NTTRadix2_16 NTRUPlus768NTTRadix2_8.
require import NTRUPlus768NTTRadix2_4.
require import NTRUPlus768NTTStage1Proof NTRUPlus768NTTRadix3Proof.
require import NTRUPlus768NTTRadix2_64Proof NTRUPlus768NTTRadix2_32Proof.
require import NTRUPlus768NTTRadix2_16Proof NTRUPlus768NTTRadix2_8Proof.
require import NTRUPlus768NTTRadix2_4Proof.

op ntt_spec (ap : W16.t Array768.t) : W16.t Array768.t =
  radix2_4_spec
    (radix2_8_spec
      (radix2_16_spec
        (radix2_32_spec
          (radix2_64_spec
            (radix3_spec (stage1_spec ap)))))).

lemma stage1_eq :
  equiv [NTRUPlus768NTT.M.stage1__jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1 ~
         NTRUPlus768NTTStage1.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1 :
    ={rp, ap} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma radix3_eq :
  equiv [NTRUPlus768NTT.M.radix3__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 ~
         NTRUPlus768NTTRadix3.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 :
    ={rp} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma radix2_64_eq :
  equiv [NTRUPlus768NTT.M.radix2_64__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64 ~
         NTRUPlus768NTTRadix2_64.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64 :
    ={rp} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma radix2_32_eq :
  equiv [NTRUPlus768NTT.M.radix2_32__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32 ~
         NTRUPlus768NTTRadix2_32.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32 :
    ={rp} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma radix2_16_eq :
  equiv [NTRUPlus768NTT.M.radix2_16__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16 ~
         NTRUPlus768NTTRadix2_16.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16 :
    ={rp} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma radix2_8_eq :
  equiv [NTRUPlus768NTT.M.radix2_8__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8 ~
         NTRUPlus768NTTRadix2_8.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8 :
    ={rp} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma radix2_4_eq :
  equiv [NTRUPlus768NTT.M.radix2_4__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 ~
         NTRUPlus768NTTRadix2_4.M.jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 :
    ={rp} ==> ={res}].
proof.
  by proc; inline *; sim.
qed.

lemma stage1_functional'
    (rp0 ap0 : W16.t Array768.t) :
  hoare [NTRUPlus768NTT.M.stage1__jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1 :
    rp = rp0 /\ ap = ap0 ==> res = stage1_spec ap0].
proof.
  conseq stage1_eq (ntt_stage1_functional rp0 ap0).
  + smt().
  smt().
qed.

lemma stage1_correct'
    (rp0 ap0 : W16.t Array768.t) :
  phoare [NTRUPlus768NTT.M.stage1__jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1 :
    rp = rp0 /\ ap = ap0 ==> res = stage1_spec ap0] = 1%r.
proof.
  conseq stage1_eq (ntt_stage1_correct rp0 ap0).
  + smt().
  smt().
qed.

lemma stage1_lossless' :
  islossless NTRUPlus768NTT.M.stage1__jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1.
proof.
  conseq stage1_eq ntt_stage1_lossless.
  + smt().
  smt().
qed.

lemma radix3_functional'
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768NTT.M.radix3__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 :
    rp = rp0 ==> res = radix3_spec rp0].
proof.
  conseq radix3_eq (ntt_radix3_functional rp0).
  + smt().
  smt().
qed.

lemma radix3_correct'
    (rp0 : W16.t Array768.t) :
  phoare [NTRUPlus768NTT.M.radix3__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3 :
    rp = rp0 ==> res = radix3_spec rp0] = 1%r.
proof.
  conseq radix3_eq (ntt_radix3_correct rp0).
  + smt().
  smt().
qed.

lemma radix3_lossless' :
  islossless NTRUPlus768NTT.M.radix3__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3.
proof.
  conseq radix3_eq ntt_radix3_lossless.
  + smt().
  smt().
qed.

lemma radix2_64_functional'
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768NTT.M.radix2_64__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64 :
    rp = rp0 ==> res = radix2_64_spec rp0].
proof.
  conseq radix2_64_eq (ntt_radix2_64_functional rp0).
  + smt().
  smt().
qed.

lemma radix2_64_correct'
    (rp0 : W16.t Array768.t) :
  phoare [NTRUPlus768NTT.M.radix2_64__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64 :
    rp = rp0 ==> res = radix2_64_spec rp0] = 1%r.
proof.
  conseq radix2_64_eq (ntt_radix2_64_correct rp0).
  + smt().
  smt().
qed.

lemma radix2_64_lossless' :
  islossless NTRUPlus768NTT.M.radix2_64__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64.
proof.
  conseq radix2_64_eq ntt_radix2_64_lossless.
  + smt().
  smt().
qed.

lemma radix2_32_functional'
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768NTT.M.radix2_32__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32 :
    rp = rp0 ==> res = radix2_32_spec rp0].
proof.
  conseq radix2_32_eq (ntt_radix2_32_functional rp0).
  + smt().
  smt().
qed.

lemma radix2_32_correct'
    (rp0 : W16.t Array768.t) :
  phoare [NTRUPlus768NTT.M.radix2_32__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32 :
    rp = rp0 ==> res = radix2_32_spec rp0] = 1%r.
proof.
  conseq radix2_32_eq (ntt_radix2_32_correct rp0).
  + smt().
  smt().
qed.

lemma radix2_32_lossless' :
  islossless NTRUPlus768NTT.M.radix2_32__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32.
proof.
  conseq radix2_32_eq ntt_radix2_32_lossless.
  + smt().
  smt().
qed.

lemma radix2_16_functional'
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768NTT.M.radix2_16__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16 :
    rp = rp0 ==> res = radix2_16_spec rp0].
proof.
  conseq radix2_16_eq (ntt_radix2_16_functional rp0).
  + smt().
  smt().
qed.

lemma radix2_16_correct'
    (rp0 : W16.t Array768.t) :
  phoare [NTRUPlus768NTT.M.radix2_16__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16 :
    rp = rp0 ==> res = radix2_16_spec rp0] = 1%r.
proof.
  conseq radix2_16_eq (ntt_radix2_16_correct rp0).
  + smt().
  smt().
qed.

lemma radix2_16_lossless' :
  islossless NTRUPlus768NTT.M.radix2_16__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16.
proof.
  conseq radix2_16_eq ntt_radix2_16_lossless.
  + smt().
  smt().
qed.

lemma radix2_8_functional'
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768NTT.M.radix2_8__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8 :
    rp = rp0 ==> res = radix2_8_spec rp0].
proof.
  conseq radix2_8_eq (ntt_radix2_8_functional rp0).
  + smt().
  smt().
qed.

lemma radix2_8_correct'
    (rp0 : W16.t Array768.t) :
  phoare [NTRUPlus768NTT.M.radix2_8__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8 :
    rp = rp0 ==> res = radix2_8_spec rp0] = 1%r.
proof.
  conseq radix2_8_eq (ntt_radix2_8_correct rp0).
  + smt().
  smt().
qed.

lemma radix2_8_lossless' :
  islossless NTRUPlus768NTT.M.radix2_8__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8.
proof.
  conseq radix2_8_eq ntt_radix2_8_lossless.
  + smt().
  smt().
qed.

lemma radix2_4_functional'
    (rp0 : W16.t Array768.t) :
  hoare [NTRUPlus768NTT.M.radix2_4__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 :
    rp = rp0 ==> res = radix2_4_spec rp0].
proof.
  conseq radix2_4_eq (ntt_radix2_4_functional rp0).
  + smt().
  smt().
qed.

lemma radix2_4_correct'
    (rp0 : W16.t Array768.t) :
  phoare [NTRUPlus768NTT.M.radix2_4__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 :
    rp = rp0 ==> res = radix2_4_spec rp0] = 1%r.
proof.
  conseq radix2_4_eq (ntt_radix2_4_correct rp0).
  + smt().
  smt().
qed.

lemma radix2_4_lossless' :
  islossless NTRUPlus768NTT.M.radix2_4__jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4.
proof.
  conseq radix2_4_eq ntt_radix2_4_lossless.
  + smt().
  smt().
qed.

lemma ntt_functional
    (rp0 ap0 : W16.t Array768.t) :
  hoare [NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt :
    rp = rp0 /\ ap = ap0 ==> res = ntt_spec ap0].
proof.
  proc.
  call (radix2_4_functional'
          (radix2_8_spec
            (radix2_16_spec
              (radix2_32_spec
                (radix2_64_spec
                  (radix3_spec (stage1_spec ap0))))))).
  call (radix2_8_functional'
          (radix2_16_spec
            (radix2_32_spec
              (radix2_64_spec
                (radix3_spec (stage1_spec ap0)))))).
  call (radix2_16_functional'
          (radix2_32_spec
            (radix2_64_spec
              (radix3_spec (stage1_spec ap0))))).
  call (radix2_32_functional'
          (radix2_64_spec
            (radix3_spec (stage1_spec ap0)))).
  call (radix2_64_functional'
          (radix3_spec (stage1_spec ap0))).
  call (radix3_functional' (stage1_spec ap0)).
  call (stage1_functional' rp0 ap0).
  auto => />.
qed.

lemma ntt_lossless :
  islossless NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt.
proof.
  proc.
  call radix2_4_lossless'.
  call radix2_8_lossless'.
  call radix2_16_lossless'.
  call radix2_32_lossless'.
  call radix2_64_lossless'.
  call radix3_lossless'.
  call stage1_lossless'.
  auto.
qed.

lemma ntt_correct
    (rp0 ap0 : W16.t Array768.t) :
  phoare [NTRUPlus768NTT.M.jade_ntruplus_ntruplus768_amd64_ref_ntt :
    rp = rp0 /\ ap = ap0 ==> res = ntt_spec ap0] = 1%r.
proof.
  by conseq ntt_lossless (ntt_functional rp0 ap0).
qed.
