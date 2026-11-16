

lemma __spreadness_eof p :
 mu uniform192(fun buf=>pke_cbd_field buf=p)<=1%r/(2%r^768).
proof. exact (spread_cbd_field_buffer_point_bound p). qed.
