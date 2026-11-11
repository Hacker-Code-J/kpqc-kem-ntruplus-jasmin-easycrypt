require import AllCore Distr DList.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array768.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMOracles.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768ValidKeyM1Recovery.
require import NTRUPlus768KeygenCompleteSpec NTRUPlus768FreshRetryLaw.
require import NTRUPlus768KEMFailureModel.

(* The numerical theorem specializes both random-byte ports to independent
   uniform draws. The existing arbitrary shared-state RNG theorem remains
   separate. No concrete native RNG implementation is substituted here. *)
module UniformKEMRNG = {
 proc seed32() : W8.t Array32.t = {
  var x; x <$ uniform32; return x;
 }
 proc coins96() : W8.t Array96.t = {
  var x; x <$ uniform96; return x;
 }
}.
module UniformCoins = {
 proc sample() : W8.t Array96.t = {
  var x; x <$ uniform96; return x;
 }
}.

op [opaque] dfr_bad (f g r m:W8.t Array192.t) : bool =
 !sampled_m1_no_wrap f g (poly_cbd1_spec r) (poly_cbd1_spec m).

type four_buffers = (W8.t Array192.t * W8.t Array192.t) *
                    (W8.t Array192.t * W8.t Array192.t).
op [opaque] four_buffers_bad (bs:four_buffers) =
 dfr_bad bs.`1.`1 bs.`1.`2 bs.`2.`1 bs.`2.`2.
op raw_four_law = ((uniform192 `*` uniform192) `*` (uniform192 `*` uniform192)).
op accepted_four_law = (((dcond uniform192 keygen_f_accept) `*`
                         (dcond uniform192 keygen_g_accept)) `*`
                        (uniform192 `*` uniform192)).

module RawFourBuffers = {
 proc sample() : four_buffers = {
  var f,g,r,m;
  f <$ uniform192; g <$ uniform192;
  r <$ uniform192; m <$ uniform192;
  return ((f,g),(r,m));
 }
 proc run() : bool = {
  var bs; bs <@ sample(); return four_buffers_bad bs;
 }
}.
module AcceptedFourBuffers = {
 proc sample() : four_buffers = {
  var f,g,r,m;
  f <$ dcond uniform192 keygen_f_accept;
  g <$ dcond uniform192 keygen_g_accept;
  r <$ uniform192; m <$ uniform192;
  return ((f,g),(r,m));
 }
 proc run() : bool = {
  var bs; bs <@ sample(); return four_buffers_bad bs;
 }
}.

lemma uniform_kem_seed_ll : islossless UniformKEMRNG.seed32.
proof. proc; rnd; auto=> />; exact uniform32_ll. qed.
lemma uniform_kem_coins_ll : islossless UniformKEMRNG.coins96.
proof. proc; rnd; auto=> />; exact uniform96_ll. qed.
lemma uniform_coins_ll : islossless UniformCoins.sample.
proof. proc; rnd; auto=> />; exact uniform96_ll. qed.
lemma uniform_kem_seed_port :
 equiv[KeygenRNGPort(UniformKEMRNG).sample ~ UniformSeedRNG.sample : true ==> ={res}].
proof. proc; inline UniformKEMRNG.seed32; auto. qed.
lemma uniform_kem_coins_port :
 equiv[EncapRNGPort(UniformKEMRNG).sample ~ UniformCoins.sample : true ==> ={res}].
proof. proc; inline UniformKEMRNG.coins96; auto. qed.
lemma dfr_badE f g r m :
 dfr_bad f g r m = !sampled_m1_no_wrap f g (poly_cbd1_spec r) (poly_cbd1_spec m).
proof. by rewrite /dfr_bad. qed.
lemma four_buffers_badE bs :
 four_buffers_bad bs=dfr_bad bs.`1.`1 bs.`1.`2 bs.`2.`1 bs.`2.`2.
proof. by rewrite /four_buffers_bad. qed.
