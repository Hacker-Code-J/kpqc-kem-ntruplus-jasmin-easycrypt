

lemma __spreadness_eof w msg ct : pke_key_relation w=>
 E acwc2_gpads_law(fun pads=>spread_cipher_mass w msg(acwc2_gfun pads)ct)<=1%r/(2%r^768).
proof. exact (spread_cipher_pads_average_bound w msg ct). qed.
