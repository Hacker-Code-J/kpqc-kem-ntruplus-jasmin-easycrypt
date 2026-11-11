"""Unit means independent inverse existence; actual status is a proved equivalence."""
BASE='ntruplus/proof/768/ref/keygen_gen_law/'
TERMINAL=BASE+'NTRUPlus768KeygenTerminalUnit.ec'
GLOBAL=BASE+'NTRUPlus768KeygenGlobalUnit.ec'
ACCEPTANCE=BASE+'NTRUPlus768GenAcceptance.ec'
PKE_UNIT='ntruplus/proof/768/ref/pke_average_correctness/NTRUPlus768PKEKeyDistribution.ec'
RULES=(
 (PKE_UNIT,'Rq unit is independently defined by polynomial inverse existence',r'op pke_rq_unit (p:NTRUPoly.poly) : bool = exists r, eqm_global (p*r) NTRUPoly.poly1.'),
 (TERMINAL,'terminal unit is inverse existence across all 192 quartic blocks',r'op gen_terminal_unit (a:W16.t Array768.t) : bool = exists inverse, poly_basemul_qring a inverse ntt_block_identity 192.'),
 (TERMINAL,'actual inverse status iff unit retains the required input range',r'lemma gen_inverse_status_iff a : in_qrange768 a => (keygen_inverse_status a=W64.zero <=> gen_terminal_unit a).'),
 (TERMINAL,'the actual complete inverse core has precise success and full-zero rejection semantics',r'lemma gen_inverse_core_correct rp0 a0 : in_qrange768 a0 => phoare[NTRUPlus768PolyBaseInv.M.__poly_baseinv_core : rp=rp0 /\ ap=a0 ==> res=(keygen_inverse_value a0,keygen_inverse_status a0) /\ (res.`2=W64.zero <=> gen_terminal_unit a0) /\ (res.`2=W64.one <=> !gen_terminal_unit a0) /\ (res.`2=W64.zero => poly_basemul_qring a0 res.`1 ntt_block_identity 192) /\ (res.`2=W64.one => res.`1=poly_zero)] = 1%r.'),
 (GLOBAL,'finite injectivity implies surjectivity only for a closed self-map',r"lemma gen_finite_endomap_surjective ['a] (S:'a->bool) (F:'a->'a) : is_finite S =>(forall x,S x=>S(F x)) => (forall x y,S x=>S y=>F x=F y=>x=y) => forall y,S y=>exists x,S x /\ F x=y."),
 (GLOBAL,'terminal multiplication is reduced back into the canonical finite carrier',r'op gen_terminal_multiply (a b:W16.t Array768.t) = rrec_canonical(candidate_product_spec a b).'),
 (GLOBAL,'global equivalence uses representation and range without assuming global unit or CRT surjectivity',r'lemma gen_terminal_unit_iff_rq a p : in_qrange768 a=>terminal_represents a p=>(gen_terminal_unit a<=>pke_rq_unit p).'),
 (ACCEPTANCE,'all typed f buffers are tested as the shaped 1+3f0 field polynomial',r'lemma gen_f_accept_unit buf : keygen_f_accept buf= pke_rq_unit(NTRUPoly.poly1+NTRUPoly.polyC(lift_int 3)*pke_cbd_field buf).'),
 (ACCEPTANCE,'actual g acceptance is equivalent to unit of unscaled g',r'lemma gen_g_accept_unit buf : keygen_g_accept buf=pke_rq_unit(pke_cbd_field buf).'),
)
MUTATIONS=(
 ('Rq-unit-is-circularly-defined-by-implementation-status',PKE_UNIT,'exists r, eqm_global (p*r) NTRUPoly.poly1.','implementation_accepts p.'),
 ('terminal-unit-is-circularly-defined-by-inverse-status',TERMINAL,'exists inverse, poly_basemul_qring a inverse ntt_block_identity 192.','keygen_inverse_status a=W64.zero.'),
 ('terminal-unit-is-confused-with-nonzero-polynomial',TERMINAL,'exists inverse, poly_basemul_qring a inverse ntt_block_identity 192.','a<>poly_zero.'),
 ('terminal-unit-checks-only-the-first-quartic-block',TERMINAL,'exists inverse, poly_basemul_qring a inverse ntt_block_identity 192.','exists inverse, poly_basemul_qring a inverse ntt_block_identity 1.'),
 ('inverse-status-equivalence-drops-word-range',TERMINAL,'lemma gen_inverse_status_iff a : in_qrange768 a =>','lemma gen_inverse_status_iff a :'),
 ('whole-inverse-core-is-confused-with-scalar-BaseInv',TERMINAL,'phoare[NTRUPlus768PolyBaseInv.M.__poly_baseinv_core :','phoare[ScalarBaseInv.run :'),
 ('whole-inverse-core-rejection-falsely-preserves-input-output-buffer',TERMINAL,'(res.`2=W64.one => res.`1=poly_zero)] = 1%r.','(res.`2=W64.one => res.`1=rp0)] = 1%r.'),
 ('finite-surjectivity-omits-closure-in-the-same-carrier',GLOBAL,'is_finite S =>(forall x,S x=>S(F x)) =>','is_finite S =>'),
 ('finite-terminal-multiplier-skips-canonical-normalization',GLOBAL,'rrec_canonical(candidate_product_spec a b).','candidate_product_spec a b.'),
 ('unit-iff-assumes-the-unit-it-was-meant-to-characterize',GLOBAL,'lemma gen_terminal_unit_iff_rq a p :','lemma gen_terminal_unit_iff_rq a p : pke_rq_unit p =>'),
 ('f-acceptance-forgets-the-constant-one',ACCEPTANCE,'NTRUPoly.poly1+NTRUPoly.polyC(lift_int 3)*pke_cbd_field buf','NTRUPoly.polyC(lift_int 3)*pke_cbd_field buf'),
 ('g-acceptance-uses-the-shaped-f-predicate',ACCEPTANCE,'lemma gen_g_accept_unit buf : keygen_g_accept buf=pke_rq_unit(pke_cbd_field buf).','lemma gen_g_accept_unit buf : keygen_g_accept buf=pke_rq_unit(NTRUPoly.poly1+NTRUPoly.polyC(lift_int 3)*pke_cbd_field buf).'),
)
