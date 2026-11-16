
lemma __stopped_actual_games_eof &mem qf qg ab m0 (event:stopped_output -> bool) :
 0<=qf => 0<=qg => 0<=ab => fsize m0<=ab =>
 `|Pr[DirectROMStopped.run(qf,qg,m0) @ &mem : event res] -
   Pr[DirectFreshStopped.run(qf,qg) @ &mem : event res]| <= proposal_delta ab (qf+qg).
proof. exact (stopped_rom_fresh_distance &mem qf qg ab m0 event). qed.
