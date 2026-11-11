require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768KeygenCompleteProof NTRUPlus768PKEModel.
require import NTRUPlus768DecapCompleteSpec NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768ACWC2Model NTRUPlus768ACWC2BaseModel.
require import NTRUPlus768ACWC2Oracle.
require import NTRUPlus768ACWC2Domains NTRUPlus768ACWC2Mean NTRUPlus768ACWC2Concentration.

type fo_h_input = W8.t Array96.t * W8.t Array32.t.

op fo_randomness (hout:W8.t Array224.t) : pke_poly =
 poly_cbd1_spec(complete_hash_tail hout).
op fo_base_bad (w:keygen_witness) (g:acwc2_g_function)
 (msg:W8.t Array96.t) (hout:W8.t Array224.t) =
 acwc2_pad_bad w msg (fo_randomness hout) (g(fo_randomness hout)).
op fo_error (w:keygen_witness) (g:acwc2_g_function) =
 acwc2_finite_max acwc2_message_enum (fun msg=>acwc2_weighted_bad w msg g).
op fo_hcache_good (w:keygen_witness) (g:acwc2_g_function)
 (excluded:fo_h_input option) (cache:(fo_h_input,W8.t Array224.t)fmap) =
 forall x y,cache.[x]=Some y=>Some x<>excluded=>!fo_base_bad w g x.`1 y.

(* Private proof data. A query-only adversary cannot read the witness,
   fixed G function, distinguished challenge entry, or monitors below. *)
module FOContext = {
 var w:keygen_witness
 var g:acwc2_g_function
 var challenge_h:fo_h_input option
 var challenge_hash:W8.t Array224.t
 var challenge_ct:W8.t Array1152.t
 proc init(w0:keygen_witness,g0:acwc2_g_function) = {
  w<-w0;g<-g0;challenge_h<-None;
  challenge_hash<-witness;challenge_ct<-witness;
 }
 proc challenge(input:fo_h_input,hout:W8.t Array224.t,ct:W8.t Array1152.t) = {
  challenge_h<-Some input;challenge_hash<-hout;challenge_ct<-ct;
 }
}.
module FOBadState = {
 var bad:bool
 var fresh:int
 proc init() = { bad<-false;fresh<-0; }
}.
module FOBudgetState = {
 var nH,nD,limit:int
 var overflow:bool
 proc configure(q:int) = {nH<-0;nD<-0;limit<-max 0 q;overflow<-false;}
}.

lemma fo_context_init_ll : islossless FOContext.init.
proof. proc; auto. qed.
lemma fo_context_challenge_ll : islossless FOContext.challenge.
proof. proc; auto. qed.
lemma fo_bad_init_ll : islossless FOBadState.init.
proof. proc; auto. qed.
lemma fo_budget_configure_ll : islossless FOBudgetState.configure.
proof. proc; auto. qed.
