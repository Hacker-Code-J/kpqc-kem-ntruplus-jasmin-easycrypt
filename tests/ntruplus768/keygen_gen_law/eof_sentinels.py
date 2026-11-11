"""Frozen complete semantic EOF declarations and isolated unfinished-proof inventory."""
SENTINELS = {
    'keygen_gen_law/NTRUPlus768KeygenTerminalUnit.ec': r"""

lemma __keygen_gen_law_eof_0 rp0 a0 :
 in_qrange768 a0 =>
 phoare[NTRUPlus768PolyBaseInv.M.__poly_baseinv_core : rp=rp0 /\ ap=a0 ==>
   res=(keygen_inverse_value a0,keygen_inverse_status a0) /\
   (res.`2=W64.zero <=> gen_terminal_unit a0) /\
   (res.`2=W64.one <=> !gen_terminal_unit a0) /\
   (res.`2=W64.zero => poly_basemul_qring a0 res.`1 ntt_block_identity 192) /\
   (res.`2=W64.one => res.`1=poly_zero)] = 1%r.
proof. exact (gen_inverse_core_correct rp0 a0). qed.
""",
    'keygen_gen_law/NTRUPlus768KeygenGlobalUnit.ec': r"""

lemma __keygen_gen_law_eof_1 a p :
 in_qrange768 a=>terminal_represents a p=>(gen_terminal_unit a<=>pke_rq_unit p).
proof. exact (gen_terminal_unit_iff_rq a p). qed.
""",
    'keygen_gen_law/NTRUPlus768GenModel.ec': r"""

lemma __keygen_gen_law_eof_2 f g h :
 pke_rq_unit f =>gen_public_relation f g h =>gen_key_from_fg(f,g)=(h,f).
proof. exact (gen_key_from_fgE f g h). qed.
""",
    'keygen_gen_law/NTRUPlus768GenAcceptance.ec': r"""

lemma __keygen_gen_law_eof_3 buf :
 (keygen_g_attempt_result buf).`4=W64.zero <=>pke_rq_unit(pke_cbd_field buf).
proof. exact (gen_g_attempt_unit buf). qed.
""",
    'keygen_gen_law/NTRUPlus768GenKeyProjection.ec': r"""

lemma __keygen_gen_law_eof_7 w : pke_key_relation w =>
 gen_actual_core w=gen_key_from_fg(gen_shape_f(pke_cbd_field w.`kg_fbuf),pke_cbd_field w.`kg_gbuf).
proof. exact (gen_valid_key_shape_projection w). qed.
""",
    'keygen_gen_law/NTRUPlus768GenDistribution.ec': r"""

lemma __keygen_gen_law_eof_4 &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 Pr[Keygen(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run() @ &m:
 event(gen_serialized_core res.`1 res.`2)]=mu gen_key_law event.
proof. exact (gen_programmed_public_key_law &m event). qed.
""",
    'keygen_gen_law/NTRUPlus768GenProcedures.ec': r"""

lemma __keygen_gen_law_eof_5 &m (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 Pr[Keygen(UniformSeedRNG,ProgrammedFreshExpand,SHAKEFROM).run() @ &m:
  event(gen_serialized_core res.`1 res.`2)]=Pr[Figure18Gen.run() @ &m:event res].
proof. exact (figure18_programmed_public_probability &m event). qed.
""",
    'keygen_gen_law/NTRUPlus768GenROMBridge.ec': r"""

lemma __keygen_gen_law_eof_6 &m
 (event:NTRUPoly.poly*NTRUPoly.poly->bool) :
 ROE.m{m}=empty =>
 `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m:
    event(gen_serialized_core res.`1 res.`2)]-mu gen_key_law event| <
 1%r/(2%r^239).
proof. exact (gen_rom_public_key_law_239 &m event). qed.
""",
}

SEMANTIC_TARGETS = {'keygen_gen_law/NTRUPlus768GenAcceptance.ec': 'gen_g_attempt_unit',
 'keygen_gen_law/NTRUPlus768GenDistribution.ec': 'gen_programmed_public_key_law',
 'keygen_gen_law/NTRUPlus768GenKeyProjection.ec': 'gen_valid_key_shape_projection',
 'keygen_gen_law/NTRUPlus768GenModel.ec': 'gen_key_from_fgE',
 'keygen_gen_law/NTRUPlus768GenProcedures.ec': 'figure18_programmed_public_probability',
 'keygen_gen_law/NTRUPlus768GenROMBridge.ec': 'gen_rom_public_key_law_239',
 'keygen_gen_law/NTRUPlus768KeygenGlobalUnit.ec': 'gen_terminal_unit_iff_rq',
 'keygen_gen_law/NTRUPlus768KeygenTerminalUnit.ec': 'gen_inverse_core_correct'}

MODULE_BINDERS = {'keygen_gen_law/NTRUPlus768GenAcceptance.ec': (),
 'keygen_gen_law/NTRUPlus768GenDistribution.ec': (),
 'keygen_gen_law/NTRUPlus768GenKeyProjection.ec': (),
 'keygen_gen_law/NTRUPlus768GenModel.ec': (),
 'keygen_gen_law/NTRUPlus768GenProcedures.ec': (),
 'keygen_gen_law/NTRUPlus768GenROMBridge.ec': (),
 'keygen_gen_law/NTRUPlus768KeygenGlobalUnit.ec': (),
 'keygen_gen_law/NTRUPlus768KeygenTerminalUnit.ec': ()}

NEGATIVE_PROOFS = ('keygen_gen_law/NTRUPlus768KeygenTerminalUnit.ec',
 'keygen_gen_law/NTRUPlus768KeygenGlobalUnit.ec',
 'keygen_gen_law/NTRUPlus768GenModel.ec',
 'keygen_gen_law/NTRUPlus768GenAcceptance.ec',
 'keygen_gen_law/NTRUPlus768GenKeyProjection.ec',
 'keygen_gen_law/NTRUPlus768GenDistribution.ec',
 'keygen_gen_law/NTRUPlus768GenProcedures.ec',
 'keygen_gen_law/NTRUPlus768GenROMBridge.ec')
