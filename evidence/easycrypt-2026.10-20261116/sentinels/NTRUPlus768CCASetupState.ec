

lemma __cca_setup_eof_0 :
 equiv[ProgrammedFreshExpand.shake ~ FreshExpand.shake : ={seed} ==> ={res}].
proof. exact (programmed_fresh_expand_projection). qed.
