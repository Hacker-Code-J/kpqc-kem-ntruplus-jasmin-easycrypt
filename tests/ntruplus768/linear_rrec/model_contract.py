"""Linear recovery and native comparison trust boundaries."""
BASE='ntruplus/proof/768/ref/linear_rrec/'
MODEL=BASE+'NTRUPlus768RRecLinearModel.ec'
PROCEDURES=BASE+'NTRUPlus768RRecLinearProcedures.ec'
TRANSFORM=BASE+'NTRUPlus768RRecTransform.ec'
CANONICAL=BASE+'NTRUPlus768RRecCanonical.ec'
RULES = (
 (TRANSFORM,'right inversion ranges over the whole proved finite terminal domain',r"lemma rrec_finite_right_inverse ['a] (S:'a->bool) (F I:'a->'a) : is_finite S => (forall x,S x=>S(F x)) => (forall x,S x=>I(F x)=x) => forall y,S y=>F(I y)=y."),
 (TRANSFORM,'every terminal word array has a proved global representative',r'lemma rrec_terminal_represented y : exists p,terminal_represents y p.'),
 (TRANSFORM,'actual inverse then forward needs only the existing terminal range',r'lemma rrec_inverse_forward_mod y : qrange_input_shape y => poly_coeff_eq_mod_q (forward_ntt_spec(inverse_invntt_spec y)) y.'),
 (TRANSFORM,'ternary inverse candidate returns the arbitrary terminal value modulo q',r'lemma rrec_inverse_forward_trit y r : qrange_input_shape y =>pke_domain r =>rrec_normalize(inverse_invntt_spec y)=r => poly_coeff_eq_mod_q (pke_rhat r) y.'),
 (CANONICAL,'canonicalization preserves the signed 16-bit coefficient meaning modulo q',r'op rrec_canonical (a:W16.t Array768.t) : W16.t Array768.t = Array768.init(fun i=>W16.of_int(coeff a.[i] %% q)).'),
 (CANONICAL,'canonical carrier contains exactly nonnegative residues below q',r'op rrec_canonical_domain (a:W16.t Array768.t) = forall i,0<=i<768=>0<=coeff a.[i]<q.'),
 (CANONICAL,'the concrete canonical carrier is proved finite without an added premise',r'lemma rrec_canonical_domain_finite : is_finite rrec_canonical_domain.'),
 (MODEL,'linear candidate keeps canonical ciphertext and message-domain guards without re-encryption',r'op rrec_linear_using_inverse_spec (pk:W8.t Array1152.t) (m:pke_poly) (ct:W8.t Array1152.t) (inverse:pke_poly) : pke_poly option = if encap_key_canonical ct /\ pke_domain m then rrec_finish_spec (decoded_poly ct) m inverse else None.'),
 (MODEL,'public linear model checks the key and obtains its own public inverse',r'op rrec_linear_spec (pk:W8.t Array1152.t) (m:pke_poly) (ct:W8.t Array1152.t) : pke_poly option = if encap_key_canonical pk then let inverse=rrec_public_inverse(decoded_poly pk) in if inverse=None then None else rrec_linear_using_inverse_spec pk m ct (oget inverse) else None.'),
 (PROCEDURES,'linear helper performs actual ciphertext decode and trit checking before the existing actual finish',r'module LinearRRecUsingInverse = { proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t,inverse:W16.t Array768.t) : W16.t Array768.t option = { var cp:W16.t Array768.t; var status:W32.t; var valid_message:bool; var result:W16.t Array768.t option; result <- None; (cp,status) <@ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,ct); if(status=W32.zero){ valid_message <@ RRecTrit.check(m); if(valid_message){ result <@ RRecFinish.run(cp,m,inverse); } } return result; } }.'),
 (PROCEDURES,'public linear entry point takes only pk/message/ciphertext and computes the public inverse',r'module LinearRRec = { proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t) : W16.t Array768.t option = { var hp:W16.t Array768.t; var status:W32.t; var inverse,result:W16.t Array768.t option; result <- None; (hp,status) <@ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes(witness,pk); if(status=W32.zero){ inverse <@ RRecPublicInverse.run(hp); if(inverse<>None){ result <@ LinearRRecUsingInverse.run(pk,m,ct,oget inverse); } } return result; } }.'),
)
MUTATIONS = (
 ('right-inverse-assumes-the-desired-terminal-identity',TRANSFORM,'(forall x,S x=>I(F x)=x) => forall y,S y=>F(I y)=y.','(forall x,S x=>I(F x)=x) => (forall y,S y=>F(I y)=y) => forall y,S y=>F(I y)=y.'),
 ('right-inverse-is-restricted-to-a-forward-image',TRANSFORM,'forall y,S y=>F(I y)=y.',r'forall y,S y=>(exists x,S x /\ F x=y)=>F(I y)=y.'),
 ('terminal-representation-existence-is-assumed',TRANSFORM,'lemma rrec_terminal_represented y : exists p,terminal_represents y p.','lemma rrec_terminal_represented y : (exists p,terminal_represents y p) => exists p,terminal_represents y p.'),
 ('inverse-forward-adds-an-honest-forward-image-premise',TRANSFORM,'lemma rrec_inverse_forward_mod y : qrange_input_shape y =>',r'lemma rrec_inverse_forward_mod y : qrange_input_shape y => (exists r,pke_domain r /\ y=pke_rhat r) =>'),
 ('inverse-forward-trit-adds-a-no-wrap-premise',TRANSFORM,'lemma rrec_inverse_forward_trit y r :','lemma rrec_inverse_forward_trit y r : (forall i,0<=i<768=>-576<coeff y.[i]<576) =>'),
 ('canonicalization-uses-unsigned-instead-of-signed-word-value',CANONICAL,'W16.of_int(coeff a.[i] %% q)','W16.of_int(W16.to_uint a.[i] %% q)'),
 ('canonicalization-uses-packing-modulus-instead-of-q',CANONICAL,'W16.of_int(coeff a.[i] %% q)','W16.of_int(coeff a.[i] %% 4096)'),
 ('canonical-domain-admits-noncanonical-q-alias',CANONICAL,'0<=coeff a.[i]<q.','0<=coeff a.[i]<=q.'),
 ('concrete-finiteness-is-assumed-rather-than-proved',CANONICAL,'lemma rrec_canonical_domain_finite : is_finite rrec_canonical_domain.','lemma rrec_canonical_domain_finite : is_finite rrec_canonical_domain => is_finite rrec_canonical_domain.'),
 ('linear-model-drops-ciphertext-canonicality',MODEL,r'if encap_key_canonical ct /\ pke_domain m then','if pke_domain m then'),
 ('linear-model-drops-message-domain',MODEL,r'if encap_key_canonical ct /\ pke_domain m then','if encap_key_canonical ct then'),
 ('linear-model-silently-keeps-reencryption-verification',MODEL,'rrec_finish_spec (decoded_poly ct) m inverse else None.','rrec_verify_spec pk m ct (rrec_finish_spec (decoded_poly ct) m inverse) else None.'),
 ('linear-public-model-drops-key-canonicality',MODEL,'if encap_key_canonical pk then','if true then'),
 ('linear-public-model-ignores-inversion-failure',MODEL,'if inverse=None then None else','if false then None else'),
 ('actual-linear-helper-keeps-extra-reencryption-call',PROCEDURES,'result <@ RRecFinish.run(cp,m,inverse);','result <@ RRecFinish.run(cp,m,inverse); result <@ RRecVerify.run(pk,m,ct,result);'),
 ('actual-linear-helper-replaces-kernel-composition-with-pure-spec',PROCEDURES,'result <@ RRecFinish.run(cp,m,inverse);','result <- rrec_finish_spec cp m inverse;'),
 ('actual-public-recovery-accepts-a-secret-inverse-input',PROCEDURES,'proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t) : W16.t Array768.t option','proc run(pk:W8.t Array1152.t,m:W16.t Array768.t,ct:W8.t Array1152.t,secret_inverse:W16.t Array768.t) : W16.t Array768.t option'),
 ('actual-public-recovery-replaces-public-inversion-with-a-witness',PROCEDURES,'inverse <@ RRecPublicInverse.run(hp);','inverse <- Some witness;'),
)

from comparison_contract import RULES as COMPARISON_RULES, MUTATIONS as COMPARISON_MUTATIONS
from proof_contract import RULES as PROOF_RULES, MUTATIONS as PROOF_MUTATIONS
from native_contract import RULES as NATIVE_RULES, MUTATIONS as NATIVE_MUTATIONS
from acwc2_contract import RULES as ACWC2_RULES, MUTATIONS as ACWC2_MUTATIONS
RULES += ACWC2_RULES
MUTATIONS += ACWC2_MUTATIONS
RULES += NATIVE_RULES
MUTATIONS += NATIVE_MUTATIONS
RULES += PROOF_RULES
MUTATIONS += PROOF_MUTATIONS
RULES += COMPARISON_RULES
MUTATIONS += COMPARISON_MUTATIONS

def check_model(read, ordered, require):
 from check_linear_rrec import compact
 for relative,label,expected in RULES:
  require(compact(expected).replace("op[opaque]","op") in read(relative).replace("op[opaque]","op"),label)
