require import AllCore Distr FMap PROM.
from Jasmin require import JWord.
require import Array32 Array96 Array129 Array192 Array224 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768PolySOTPEncodeAlgebra.
require import NTRUPlus768ROMDistributions NTRUPlus768FOModel.
require import NTRUPlus768FOSetupDistribution NTRUPlus768ACWC2Oracle.
require import NTRUPlus768KEMPayloadSpec.

type sim_request = {
 sr_pk:W8.t Array1152.t;
 sr_ct:W8.t Array1152.t;
 sr_code:pke_poly;
 sr_msg:W8.t Array96.t;
 sr_fail:W32.t;
 sr_suffix:W8.t Array32.t;
}.
op sim_h_input (q:sim_request) : fo_h_input = (q.`sr_msg,q.`sr_suffix).
op sim_candidate (pk:W8.t Array1152.t) (g:acwc2_g_function)
 (input:fo_h_input) (hout:W8.t Array224.t) =
 pke_enc_spec pk (poly_sotp_encode_spec input.`1 (g(fo_randomness hout))) (fo_randomness hout).
op sim_log_included (log table:(fo_h_input,W8.t Array224.t)fmap) =
 forall x y,log.[x]=Some y=>table.[x]=Some y.
op sim_h_cover (log table:(fo_h_input,W8.t Array224.t)fmap)
 (challenge:fo_h_input option) =
 forall x,x \in table=>x \in log \/ Some x=challenge.

(* This record contains public values only. It is the complete state
   available to the final decapsulation simulator besides its query ports. *)
module SimPublic = {
 var pk:W8.t Array1152.t
 var suffix:W8.t Array32.t
 var cstar:W8.t Array1152.t option
 var count:int
 proc init(pk0:W8.t Array1152.t,suffix0:W8.t Array32.t,ct:W8.t Array1152.t) = {
  pk<-pk0;suffix<-suffix0;cstar<-Some ct;count<-0;
 }
}.
(* Records are made by external typed/raw H calls, including raw length
   zero. Stored full outputs are simulator knowledge, not a claim that
   the adversary received all 224 bytes. Internal Decaps calls do not log. *)
module SimHistory = {
 var h:(fo_h_input,W8.t Array224.t)fmap
 proc init() = {h<-empty;}
 proc record(input:fo_h_input,hout:W8.t Array224.t) = {h.[input]<-hout;}
}.
module SimBad = {
 var hidden,corr:bool
 var selected_calls:int
 proc init() = {hidden<-false;corr<-false;selected_calls<-0;}
}.

module type SimHPort = {proc get(input:fo_h_input):W8.t Array224.t}.
module type SimAnswer = {proc answer(q:sim_request):W8.t Array32.t option}.

clone PROM.FullRO as SimHRO with
 type in_t <- fo_h_input,
 type out_t <- W8.t Array224.t,
 op dout <- (fun _=>uniform224),
 type d_in_t <- fo_setup_observation,
 type d_out_t <- bool.
clone PROM.FullRO as SimGRO with
 type in_t <- W8.t Array1152.t,
 type out_t <- W8.t Array192.t,
 op dout <- (fun _=>uniform192),
 type d_in_t <- fo_setup_observation,
 type d_out_t <- bool.

lemma sim_log_empty table : sim_log_included empty table.
proof. rewrite /sim_log_included; smt(emptyE). qed.
lemma sim_log_self table : sim_log_included table table.
proof. by rewrite /sim_log_included. qed.
lemma sim_public_init_ll : islossless SimPublic.init.
proof. proc;auto. qed.
lemma sim_history_init_ll : islossless SimHistory.init.
proof. proc;auto. qed.
lemma sim_history_record_ll : islossless SimHistory.record.
proof. proc;auto. qed.
lemma sim_bad_init_ll : islossless SimBad.init.
proof. proc;auto. qed.
