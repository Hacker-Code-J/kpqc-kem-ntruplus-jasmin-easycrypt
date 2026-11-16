
lemma __stopped_actual_keygen_bound_eof &m qf0 qg0 ab m0
 (event:W8.t Array1152.t * W8.t Array2336.t -> bool) :
 0<=qf0 => 0<=qg0 => 0<=ab => fsize m0<=ab => ROE.m{m}=m0 =>
 0%r<fresh_f_accept_mass => 0%r<fresh_g_accept_mass =>
 `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m : event res] -
   Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m : event res]|
 <= proposal_delta ab (qf0+qg0)+fresh_retry_tail qf0 qg0.
proof. exact (keygen_public_rom_fresh_distance &m qf0 qg0 ab m0 event). qed.
