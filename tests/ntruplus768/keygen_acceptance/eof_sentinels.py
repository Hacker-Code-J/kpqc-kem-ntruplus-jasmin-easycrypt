"""Reviewed semantic targets; literal signatures copied from their theorem declarations."""
SENTINELS = {
    'keygen_acceptance/NTRUPlus768AcceptanceRoots.ec': r'''
lemma __acceptance_0_eof j : 0<=j<384 =>
 acceptance_root j ^1728 %%3457=3456.
proof. exact (acceptance_root_euler j). qed.
''',
    'keygen_acceptance/NTRUPlus768AcceptanceSlices.ec': r'''
lemma __acceptance_1_eof j u v :
 0<=j<384 => 0<=u<32 => 0<=v<32 =>
 lift_int(slice_weighted_sum(acceptance_root j) u)=
 lift_int(slice_weighted_sum(acceptance_root j) v) => u=v.
proof. exact (acceptance_slice_field_injective j u v). qed.
''',
    'keygen_acceptance/NTRUPlus768AcceptanceAlgebra.ec': r'''
lemma __acceptance_2_eof (roots:int->CycloFq.cyclocoeff) buf :
 (forall k,0<=k<192 => terminal_root_field k=roots(2*k)*roots(2*k)) =>
 (forall k,0<=k<192 => roots(2*k+1)= -roots(2*k)) =>
 (forall j,0<=j<384 => field_nonsquare(roots j)) =>
 !keygen_g_accept buf =>
 exists j,0<=j<384 /\ quadratic_divides(roots j)(input_poly(keygen_g_pre_ntt_spec buf)).
proof. exact (keygen_g_rejected_cover roots buf). qed.
''',
    'keygen_acceptance/NTRUPlus768AcceptanceCover.ec': r'''
lemma __acceptance_3_eof (buf:W8.t Array192.t) :
 !keygen_g_accept buf =>
 exists j,0<=j<384 /\
 quadratic_divides(lift_int(acceptance_root j))(input_poly(keygen_g_pre_ntt_spec buf)).
proof. exact (keygen_g_rejected_quadratic buf). qed.
''',
    'keygen_acceptance/NTRUPlus768UniformOrbitBound.ec': r'''
lemma __acceptance_4_eof
 (accept:W8.t Array192.t -> bool) (bad:int -> W8.t Array192.t -> bool) :
 (forall i, 0<=i<384 => mu uniform192 (bad i)<=1%r/1024%r) =>
 (forall buf, !accept buf => indexed_event_union 384 bad buf) =>
 5%r/8%r<=mu uniform192 accept.
proof. exact (uniform192_acceptance_from_384_bad accept bad). qed.
''',
    'keygen_acceptance/NTRUPlus768AcceptanceInput.ec': r'''
lemma __acceptance_5_eof is_f b c :
 acceptance_same_tail b c =>
 acceptance_input is_f b-acceptance_input is_f c=
 acceptance_head_poly b-acceptance_head_poly c.
proof. exact (acceptance_input_head_difference is_f b c). qed.
''',
    'keygen_acceptance/NTRUPlus768AcceptanceHeadReduction.ec': r'''
lemma __acceptance_6_eof is_f rho b c :
 acceptance_same_tail b c =>
 (forall k,8<=k<16 => k<>2*nth 0 (slice_exponents rho) 4 =>
  k<>2*nth 0 (slice_exponents rho) 4+1 => acceptance_head_bit b k=acceptance_head_bit c k) =>
 quadratic_divides (lift_int rho) (acceptance_input is_f b) =>
 quadratic_divides (lift_int rho) (acceptance_input is_f c) =>
 forall p,0<=p<2 => acceptance_selected_weight rho b p=acceptance_selected_weight rho c p.
proof. exact (acceptance_head_divisors_equal is_f rho b c). qed.
''',
    'keygen_acceptance/NTRUPlus768AcceptanceMasks.ec': r'''
lemma __acceptance_7_eof is_f j :
 0<=j<384 => forall i k buf,
 0<=i<1024 => 0<=k<1024 =>
 quadratic_divides (lift_int(acceptance_root j))
  (acceptance_input is_f (uniform192_xor(acceptance_masks(acceptance_root j)i)buf)) =>
 quadratic_divides (lift_int(acceptance_root j))
  (acceptance_input is_f (uniform192_xor(acceptance_masks(acceptance_root j)k)buf)) => i=k.
proof. exact (acceptance_bad_translates_disjoint is_f j). qed.
''',
    'keygen_acceptance/NTRUPlus768AcceptanceProbability.ec': r'''
lemma __acceptance_8_eof : 5%r/8%r<=fresh_g_accept_mass.
proof. exact fresh_g_accept_lower. qed.
''',
    'keygen_acceptance/NTRUPlus768AcceptanceBudget.ec': r'''
lemma __acceptance_9_eof :
 130818%r/(2%r^256) < 1%r/(2%r^239).
proof. exact keygen_empty_cache_error_239. qed.
''',
    'keygen_acceptance/NTRUPlus768AcceptanceROMBound.ec': r'''
lemma __acceptance_10_eof &m
 (event:W8.t Array1152.t * W8.t Array2336.t -> bool) :
 ROE.m{m}=empty =>
 `|Pr[Keygen(UniformSeedRNG,ExpandROM,SHAKEFROM).run() @ &m : event res] -
   Pr[Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run() @ &m : event res]|
 < 1%r/(2%r^239).
proof. exact (certified_keygen_empty_cache_distance &m event). qed.
''',
}

SEMANTIC_TARGETS = {
    'keygen_acceptance/NTRUPlus768AcceptanceRoots.ec': 'acceptance_root_euler',
    'keygen_acceptance/NTRUPlus768AcceptanceSlices.ec': 'acceptance_slice_field_injective',
    'keygen_acceptance/NTRUPlus768AcceptanceAlgebra.ec': 'keygen_g_rejected_cover',
    'keygen_acceptance/NTRUPlus768AcceptanceCover.ec': 'keygen_g_rejected_quadratic',
    'keygen_acceptance/NTRUPlus768UniformOrbitBound.ec': 'uniform192_acceptance_from_384_bad',
    'keygen_acceptance/NTRUPlus768AcceptanceInput.ec': 'acceptance_input_head_difference',
    'keygen_acceptance/NTRUPlus768AcceptanceHeadReduction.ec': 'acceptance_head_divisors_equal',
    'keygen_acceptance/NTRUPlus768AcceptanceMasks.ec': 'acceptance_bad_translates_disjoint',
    'keygen_acceptance/NTRUPlus768AcceptanceProbability.ec': 'fresh_g_accept_lower',
    'keygen_acceptance/NTRUPlus768AcceptanceBudget.ec': 'keygen_empty_cache_error_239',
    'keygen_acceptance/NTRUPlus768AcceptanceROMBound.ec': 'certified_keygen_empty_cache_distance',
}

MODULE_BINDERS = {name: () for name in SENTINELS}
NEGATIVE_PROOFS = tuple(SENTINELS)
