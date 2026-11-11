"""Figure18 algebra, canonical choice, and whole-polynomial conditioning."""
BASE='ntruplus/proof/768/ref/keygen_gen_law/'
MODEL=BASE+'NTRUPlus768GenModel.ec'
PROJECTION=BASE+'NTRUPlus768GenKeyProjection.ec'
DIST=BASE+'NTRUPlus768GenDistribution.ec'
RULES=(
 (MODEL,'Figure18 f has the independent polynomial shape 1+3f0',r'op gen_shape_f (p:NTRUPoly.poly) = NTRUPoly.poly1+NTRUPoly.polyC(lift_int 3)*p.'),
 (MODEL,'public relation includes three times g and the coefficient-list degree convention',r'op gen_public_relation (f g h:NTRUPoly.poly) = NTRUPoly.deg h<=768 /\ eqm_global(h*f)(NTRUPoly.polyC(lift_int 3)*g).'),
 (MODEL,'public choice is defined by the independent algebraic relation',r'op gen_public_key (f g:NTRUPoly.poly) = choiceb (gen_public_relation f g) NTRUPoly.poly0.'),
 (MODEL,'canonical public-key uniqueness requires a unit denominator',r'lemma gen_public_relation_unique f g h1 h2 : pke_rq_unit f => gen_public_relation f g h1 => gen_public_relation f g h2 =>h1=h2.'),
 (MODEL,'choice correctness retains its existence premise',r'lemma gen_public_key_relation f g : gen_public_defined f g =>gen_public_relation f g (gen_public_key f g).'),
 (MODEL,'Gen returns the public h and private f pair',r'op gen_key_from_fg (fg:NTRUPoly.poly*NTRUPoly.poly) = (gen_public_key fg.`1 fg.`2,fg.`1).'),
 (PROJECTION,'byte-key projection decodes both pk and the actual secret f block then applies inverse NTT',r'op gen_serialized_core (pk:W8.t Array1152.t) (sk:W8.t Array2336.t) = (gen_inverse_poly(decoded_poly pk), gen_inverse_poly(decoded_poly(decap_fbytes(complete_sk_poly sk)))).'),
 (PROJECTION,'inverse-polynomial projection uses actual inverse-transform semantics',r'op gen_inverse_poly (a:W16.t Array768.t) = input_poly(inverse_invntt_spec a).'),
 (DIST,'f0 law conditions the whole polynomial on its shaped unit predicate',r'op gen_f0_law = dcond pke_field_psi1 gen_f0_accept.'),
 (DIST,'the f0 acceptance predicate tests 1+3f0 rather than f0 itself',r'op gen_f0_accept (p:NTRUPoly.poly) = pke_rq_unit(gen_shape_f p).'),
 (DIST,'g law conditions the whole unscaled polynomial on independent unit existence',r'op gen_g_law = dcond pke_field_psi1 pke_rq_unit.'),
 (DIST,'the f shape is applied after whole-polynomial conditioning',r'op gen_f_law = dmap gen_f0_law gen_shape_f.'),
 (DIST,'separate accepted polynomial laws form the f-g product',r'op gen_fg_law = gen_f_law `*` gen_g_law.'),
 (DIST,'Gen key law is the algebraic key-pair pushforward',r'op gen_key_law = dmap gen_fg_law gen_key_from_fg.'),
 (DIST,'the algebraic public choice is defined on every supported accepted pair',r'lemma gen_fg_support_defined fg : fg \in gen_fg_law => gen_public_defined fg.`1 fg.`2.'),
)
MUTATIONS=(
 ('Figure18-f-shape-drops-the-constant-one',MODEL,'NTRUPoly.poly1+NTRUPoly.polyC(lift_int 3)*p.','NTRUPoly.polyC(lift_int 3)*p.'),
 ('public-key-relation-forgets-the-three-scaling-of-g',MODEL,'eqm_global(h*f)(NTRUPoly.polyC(lift_int 3)*g).','eqm_global(h*f)g.'),
 ('degree-convention-excludes-the-highest-canonical-coefficient',MODEL,'NTRUPoly.deg h<=768','NTRUPoly.deg h<768'),
 ('public-relation-removes-canonical-degree-bound',MODEL,r'NTRUPoly.deg h<=768 /\ eqm_global','eqm_global'),
 ('public-choice-uniqueness-omits-unit-denominator',MODEL,'lemma gen_public_relation_unique f g h1 h2 : pke_rq_unit f =>','lemma gen_public_relation_unique f g h1 h2 :'),
 ('public-choice-is-treated-as-defined-without-an-existence-proof',MODEL,'lemma gen_public_key_relation f g : gen_public_defined f g =>','lemma gen_public_key_relation f g :'),
 ('Gen-returns-g-instead-of-the-secret-f-polynomial',MODEL,'(gen_public_key fg.`1 fg.`2,fg.`1).','(gen_public_key fg.`1 fg.`2,fg.`2).'),
 ('public-key-projection-skips-inverse-NTT',PROJECTION,'input_poly(inverse_invntt_spec a).','input_poly a.'),
 ('secret-key-projection-decodes-the-stored-h-inverse-instead-of-f',PROJECTION,'decoded_poly(decap_fbytes(complete_sk_poly sk))','decoded_poly(decap_hbytes(complete_sk_poly sk))'),
 ('g-law-drops-whole-polynomial-unit-conditioning',DIST,'op gen_g_law = dcond pke_field_psi1 pke_rq_unit.','op gen_g_law = pke_field_psi1.'),
 ('f0-law-tests-unshaped-polynomial-unit',DIST,'op gen_f0_accept (p:NTRUPoly.poly) = pke_rq_unit(gen_shape_f p).','op gen_f0_accept (p:NTRUPoly.poly) = pke_rq_unit p.'),
 ('f-law-shapes-unconditioned-proposals',DIST,'op gen_f_law = dmap gen_f0_law gen_shape_f.','op gen_f_law = dmap pke_field_psi1 gen_shape_f.'),
 ('accepted-key-support-assumes-public-key-existence',DIST,r'lemma gen_fg_support_defined fg : fg \in gen_fg_law =>',r'lemma gen_fg_support_defined fg : gen_public_defined fg.`1 fg.`2 => fg \in gen_fg_law =>'),
)
