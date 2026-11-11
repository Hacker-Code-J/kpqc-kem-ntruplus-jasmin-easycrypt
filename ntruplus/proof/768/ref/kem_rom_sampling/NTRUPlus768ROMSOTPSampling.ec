require import AllCore Distr FMap.
from Jasmin require import JWord.
require import Array96 Array192 Array768 Array1152.
require import NTRUPlus768ROMSOTPMaskLaw NTRUPlus768ROMOracles.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMDomains.
require import NTRUPlus768PolySOTPEncodeAlgebra NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768PolySOTPEncodeCheckedProof NTRUPlus768PolyCBD1CheckedProof.

(* Component experiments use the existing extracted procedures. The fresh-G
   experiment follows the honest serialized-input adapter and then the actual
   encoder. It is not an entire Encaps or KeyGen distribution experiment. *)
module SOTPPadSampling = {
  proc encode(rp : W16.t Array768.t, coins : W8.t Array96.t) : W16.t Array768.t = {
    var pad;
    pad <$ uniform192;
    rp <@ NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(rp, coins, pad);
    return rp;
  }
  proc encode_spec(rp : W16.t Array768.t, coins : W8.t Array96.t) : W16.t Array768.t = {
    var pad;
    pad <$ uniform192;
    return poly_sotp_encode_spec coins pad;
  }
  proc cbd(rp : W16.t Array768.t) : W16.t Array768.t = {
    var pad;
    pad <$ uniform192;
    rp <@ NTRUPlus768PolyCBD1Checked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_cbd1(rp, pad);
    return rp;
  }
  proc cbd_spec(rp : W16.t Array768.t) : W16.t Array768.t = {
    var pad;
    pad <$ uniform192;
    return poly_cbd1_spec pad;
  }
  proc g_encode(rp : W16.t Array768.t, coins : W8.t Array96.t,
                serialized : W8.t Array1152.t) : W16.t Array768.t = {
    var pad;
    pad <@ SHAKEGROM.shake(encode_g serialized);
    rp <@ NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode(rp, coins, pad);
    return rp;
  }
}.

lemma sotp_encode_actual_spec :
  equiv [SOTPPadSampling.encode ~ SOTPPadSampling.encode_spec :
    ={rp, coins} ==> ={res}].
proof.
  proc; wp.
  ecall {1} (poly_sotp_encode_correct rp{1} coins{1} pad{1}).
  by rnd; auto.
qed.

lemma cbd_actual_spec :
  equiv [SOTPPadSampling.cbd ~ SOTPPadSampling.cbd_spec : ={rp} ==> ={res}].
proof.
  proc; wp.
  ecall {1} (poly_cbd1_correct rp{1} pad{1}).
  by rnd; auto.
qed.

lemma sotp_encode_actual_ll : islossless SOTPPadSampling.encode.
proof. proc; call poly_sotp_encode_lossless; rnd; auto=> />; exact uniform192_ll. qed.

lemma cbd_actual_ll : islossless SOTPPadSampling.cbd.
proof. proc; call poly_cbd1_lossless; rnd; auto=> />; exact uniform192_ll. qed.

lemma sotp_encode_actual_event &m rp0 coins0 (event : W16.t Array768.t -> bool) :
  Pr[SOTPPadSampling.encode(rp0, coins0) @ &m : event res] = mu cbd1_uniform event.
proof.
  have hspec : Pr[SOTPPadSampling.encode_spec(rp0, coins0) @ &m : event res] =
    mu uniform192 (fun pad => event (poly_sotp_encode_spec coins0 pad)).
  + by byphoare (_ : coins = coins0 ==> event res) => //; proc; rnd; auto.
  rewrite -(sotp_encode_uniform_event coins0 event) -hspec.
  by byequiv sotp_encode_actual_spec.
qed.

lemma cbd_actual_event &m rp0 (event : W16.t Array768.t -> bool) :
  Pr[SOTPPadSampling.cbd(rp0) @ &m : event res] = mu cbd1_uniform event.
proof.
  have hspec : Pr[SOTPPadSampling.cbd_spec(rp0) @ &m : event res] = mu cbd1_uniform event.
  + rewrite /cbd1_uniform dmapE /(\o).
    by byphoare (_ : true ==> event res) => //; proc; rnd; auto.
  rewrite -hspec; by byequiv cbd_actual_spec.
qed.

lemma sotp_encode_cbd_actual_event &m rp0 coins0 (event : W16.t Array768.t -> bool) :
  Pr[SOTPPadSampling.encode(rp0, coins0) @ &m : event res] =
  Pr[SOTPPadSampling.cbd(rp0) @ &m : event res].
proof. by rewrite sotp_encode_actual_event cbd_actual_event. qed.

lemma sotp_g_encode_ll : islossless SOTPPadSampling.g_encode.
proof. proc; call poly_sotp_encode_lossless; call ro_g_shake_ll; auto. qed.

lemma sotp_g_cached_value rp0 coins0 serialized0 pad0 m0 :
  hoare [SOTPPadSampling.g_encode :
    rp = rp0 /\ coins = coins0 /\ serialized = serialized0 /\
    ROG.m = m0 /\ m0.[serialized0] = Some pad0 ==>
    res = poly_sotp_encode_spec coins0 pad0 /\ ROG.m = m0].
proof.
  proc; call (poly_sotp_encode_functional rp0 coins0 pad0).
  call (ro_g_shake_cached m0 serialized0 pad0); auto.
qed.

lemma sotp_g_fresh_uniform serialized0 :
  equiv [SOTPPadSampling.g_encode ~ SOTPPadSampling.encode :
    ={rp, coins} /\ serialized{1} = serialized0 /\ serialized0 \notin ROG.m{1}
    ==> ={res}].
proof.
  proc; wp.
  call (_ : ={rp, msg, buf} ==> ={res}); first by sim.
  inline SHAKEGROM.shake ROG.get.
  rcondt {1} 3; first by auto=> />; rewrite peel_encode_g.
  wp; rnd; auto=> />; rewrite ?peel_encode_g /=.
  move=> &1 hf pad hpad; by rewrite FMap.get_set_sameE /=.
qed.

lemma sotp_g_fresh_event &m rp0 coins0 serialized0 (event : W16.t Array768.t -> bool) :
  serialized0 \notin ROG.m{m} =>
  Pr[SOTPPadSampling.g_encode(rp0, coins0, serialized0) @ &m : event res] =
  mu cbd1_uniform event.
proof.
  move=> hf; rewrite -(sotp_encode_actual_event &m rp0 coins0 event).
  by byequiv (sotp_g_fresh_uniform serialized0).
qed.

lemma rom_sotp_sampling_eof &m rp0 coins0 serialized0 (event : W16.t Array768.t -> bool) :
  serialized0 \notin ROG.m{m} =>
  Pr[SOTPPadSampling.g_encode(rp0, coins0, serialized0) @ &m : event res] =
  mu (dmap uniform192 poly_cbd1_spec) event.
proof. exact (sotp_g_fresh_event &m rp0 coins0 serialized0 event). qed.
