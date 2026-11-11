require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array1152 Array2336 Array14466 Array13634 Array13506.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768KeygenCompleteProof NTRUPlus768KeygenCompleteAgreement.
require import NTRUPlus768EncapCompleteRNG NTRUPlus768EncapCompleteProof NTRUPlus768EncapCompleteHash.
require import NTRUPlus768DecapMessageSpec NTRUPlus768DecapCompleteHash NTRUPlus768DecapCompleteProof.
require import NTRUPlus768EncapClearCoins.

type encap_result = W8.t Array1152.t * W8.t Array32.t * W32.t * W8.t Array13634.t * W8.t Array96.t.
type decap_result = W8.t Array32.t * W32.t * W8.t Array13506.t.

(* Failure includes either API status and shared-key disagreement. The
   generated-key theorem proves that the Encaps status is always zero. *)
op [opaque] kem_failure (er:encap_result) (dr:decap_result) =
  er.`3 <> W32.zero \/ dr.`2 <> W32.zero \/ er.`2 <> dr.`1.

(* This duplicates only the already verified random wrapper. Its private
   local copy records the actual sample before the actual coin-clear call.
   No instrumentation global is exposed to an RNG or hash module. *)
module EncapRandomInstrumented(F:EncapSHAKEF,G:MessageSHAKE,H:CompleteSHAKEH,Q:EncapRNG) = {
  proc run(pk:W8.t Array1152.t,workspace:W8.t Array13634.t) : encap_result * W8.t Array96.t = {
    var coins,original:W8.t Array96.t;
    var ct:W8.t Array1152.t; var ss:W8.t Array32.t; var status:W32.t;
    coins <@ Q.sample();
    original <- coins;
    (ct,ss,status,workspace) <@ EncapDerand(F,G,H).run(pk,coins,workspace);
    coins <@ NTRUPlus768EncapClearCoins.M.jade_ntruplus_ntruplus768_amd64_ref_encap_clear_coins(coins);
    return((ct,ss,status,workspace,coins),original);
  }
}.

(* Public correctness experiment: real KeyGen, then the existing randomized
   Encaps caller, then the existing complete Decaps caller. Only the failure
   bit is returned. R and Q may share state; independence is not assumed. *)
module KEMCorrectness(R:KeygenSeedRNG,E:KeygenExpand,F:EncapSHAKEF,G:MessageSHAKE,H:CompleteSHAKEH,Q:EncapRNG) = {
  proc run() : bool = {
    var pk:W8.t Array1152.t; var sk:W8.t Array2336.t;
    var er:encap_result; var dr:decap_result;
    (pk,sk) <@ Keygen(R,E,F).run();
    er <@ EncapRandom(F,G,H,Q).run(pk,witness);
    dr <@ CompleteDecaps(G,H).run(er.`1,sk,witness);
    return kem_failure er dr;
  }
}.

(* The private observation retains the accepted KeyGen witness and the
   actual Encaps coins only until the two flags have been computed. The bad
   flag is exactly failure of the existing integer no-wrap condition. *)
module KEMCorrectnessInstrumented(R:KeygenSeedRNG,E:KeygenExpand,F:EncapSHAKEF,G:MessageSHAKE,H:CompleteSHAKEH,Q:EncapRNG) = {
  proc run() : bool * bool = {
    var w:keygen_witness; var cleared:W8.t Array14466.t;
    var coins:W8.t Array96.t;
    var er:encap_result; var dr:decap_result;
    (w,cleared) <@ KeygenInstrumented(R,E,F).run(witness);
    (er,coins) <@ EncapRandomInstrumented(F,G,H,Q).run(w.`kg_pk,witness);
    dr <@ CompleteDecaps(G,H).run(er.`1,w.`kg_sk,witness);
    return(kem_failure er dr,!keygen_coins_no_wrap w coins);
  }
}.

(* A common RNG interface permits the seed and encapsulation draws to share
   arbitrary mutable state. These ports only adapt the existing API names. *)
module type KEMRNG = {
  proc seed32() : W8.t Array32.t
  proc coins96() : W8.t Array96.t
}.
module KeygenRNGPort(B:KEMRNG) = {
  proc sample() : W8.t Array32.t = {
    var x; x <@ B.seed32(); return x;
  }
}.
module EncapRNGPort(B:KEMRNG) = {
  proc sample() : W8.t Array96.t = {
    var x; x <@ B.coins96(); return x;
  }
}.

lemma kem_failure_characterization (er:encap_result) (dr:decap_result) :
  kem_failure er dr = (er.`3 <> W32.zero \/ dr.`2 <> W32.zero \/ er.`2 <> dr.`1).
proof. by rewrite /kem_failure. qed.
