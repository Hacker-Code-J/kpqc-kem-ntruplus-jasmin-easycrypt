

lemma __spreadness_eof &m :
 E(mk(fun s=>Pr[FOSetupSource.guess(witness) @ &m:res=s]))
   (fun (s:fo_setup_observation)=>spread_cipher_max s.`1.`1(acwc2_gfun s.`3))<1%r/(2%r^352).
proof. exact (spread_weak_setup_max_352 &m). qed.
