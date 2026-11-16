

lemma __spreadness_eof m0 ct0 &mem :
 pke_domain m0=>Pr[SpreadGeneratedROM.run(m0) @ &mem:res=Some ct0]<=1%r/(2%r^768).
proof. exact (spread_generated_rom_bound m0 ct0 &mem). qed.
