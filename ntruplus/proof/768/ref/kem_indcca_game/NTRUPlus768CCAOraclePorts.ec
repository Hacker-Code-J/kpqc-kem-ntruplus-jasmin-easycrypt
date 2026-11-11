require import AllCore FMap Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768ROMOracles.

(* The adversarial capability has queries only. Game module restrictions
   exclude direct access to the underlying globals and their initializers. *)
module type CCAOraclePort = {
 proc e(input : W8.t Array32.t) : W8.t Array192.t
 proc f(input : W8.t Array1152.t) : W8.t Array32.t
 proc g(input : W8.t Array1152.t) : W8.t Array192.t
 proc h(input : W8.t Array96.t * W8.t Array32.t) : W8.t Array224.t
}.
module SharedCCAOracles : CCAOraclePort = {
 proc e(input : W8.t Array32.t) : W8.t Array192.t = {
  var r; r <@ ROE.get(input); return r;
 }
 proc f(input : W8.t Array1152.t) : W8.t Array32.t = {
  var r; r <@ ROF.get(input); return r;
 }
 proc g(input : W8.t Array1152.t) : W8.t Array192.t = {
  var r; r <@ ROG.get(input); return r;
 }
 proc h(input : W8.t Array96.t * W8.t Array32.t) : W8.t Array224.t = {
  var r; r <@ ROH.get(input); return r;
 }
}.

lemma cca_e_ll : islossless SharedCCAOracles.e.
proof. by proc; call roe_get_ll; auto. qed.
lemma cca_e_identity :
 equiv[SharedCCAOracles.e ~ ROE.get :
  ={input,ROE.m,ROF.m,ROG.m,ROH.m} ==>
  ={res,ROE.m,ROF.m,ROG.m,ROH.m}].
proof. proc; inline *; sp; if; auto. qed.
lemma cca_e_value m0 x0 : hoare[SharedCCAOracles.e :
 ROE.m=m0 /\ input=x0 ==>
 ROE.m.[x0]=Some res /\ cache_extends m0 ROE.m].
proof. by proc; call (roe_get_value m0 x0); auto. qed.
lemma cca_e_cached m0 x0 y0 : hoare[SharedCCAOracles.e :
 ROE.m=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==>
 res=y0 /\ ROE.m=m0].
proof. by proc; call (roe_get_cached m0 x0 y0); auto. qed.
lemma cca_e_frame rof0 rog0 roh0 : hoare[SharedCCAOracles.e :
 ROF.m=rof0 /\ ROG.m=rog0 /\ ROH.m=roh0 ==> ROF.m=rof0 /\ ROG.m=rog0 /\ ROH.m=roh0].
proof. proc; inline *; sp; if; auto. qed.

lemma cca_f_ll : islossless SharedCCAOracles.f.
proof. by proc; call rof_get_ll; auto. qed.
lemma cca_f_identity :
 equiv[SharedCCAOracles.f ~ ROF.get :
  ={input,ROE.m,ROF.m,ROG.m,ROH.m} ==>
  ={res,ROE.m,ROF.m,ROG.m,ROH.m}].
proof. proc; inline *; sp; if; auto. qed.
lemma cca_f_value m0 x0 : hoare[SharedCCAOracles.f :
 ROF.m=m0 /\ input=x0 ==>
 ROF.m.[x0]=Some res /\ cache_extends m0 ROF.m].
proof. by proc; call (rof_get_value m0 x0); auto. qed.
lemma cca_f_cached m0 x0 y0 : hoare[SharedCCAOracles.f :
 ROF.m=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==>
 res=y0 /\ ROF.m=m0].
proof. by proc; call (rof_get_cached m0 x0 y0); auto. qed.
lemma cca_f_frame roe0 rog0 roh0 : hoare[SharedCCAOracles.f :
 ROE.m=roe0 /\ ROG.m=rog0 /\ ROH.m=roh0 ==> ROE.m=roe0 /\ ROG.m=rog0 /\ ROH.m=roh0].
proof. proc; inline *; sp; if; auto. qed.

lemma cca_g_ll : islossless SharedCCAOracles.g.
proof. by proc; call rog_get_ll; auto. qed.
lemma cca_g_identity :
 equiv[SharedCCAOracles.g ~ ROG.get :
  ={input,ROE.m,ROF.m,ROG.m,ROH.m} ==>
  ={res,ROE.m,ROF.m,ROG.m,ROH.m}].
proof. proc; inline *; sp; if; auto. qed.
lemma cca_g_value m0 x0 : hoare[SharedCCAOracles.g :
 ROG.m=m0 /\ input=x0 ==>
 ROG.m.[x0]=Some res /\ cache_extends m0 ROG.m].
proof. by proc; call (rog_get_value m0 x0); auto. qed.
lemma cca_g_cached m0 x0 y0 : hoare[SharedCCAOracles.g :
 ROG.m=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==>
 res=y0 /\ ROG.m=m0].
proof. by proc; call (rog_get_cached m0 x0 y0); auto. qed.
lemma cca_g_frame roe0 rof0 roh0 : hoare[SharedCCAOracles.g :
 ROE.m=roe0 /\ ROF.m=rof0 /\ ROH.m=roh0 ==> ROE.m=roe0 /\ ROF.m=rof0 /\ ROH.m=roh0].
proof. proc; inline *; sp; if; auto. qed.

lemma cca_h_ll : islossless SharedCCAOracles.h.
proof. by proc; call roh_get_ll; auto. qed.
lemma cca_h_identity :
 equiv[SharedCCAOracles.h ~ ROH.get :
  ={input,ROE.m,ROF.m,ROG.m,ROH.m} ==>
  ={res,ROE.m,ROF.m,ROG.m,ROH.m}].
proof. proc; inline *; sp; if; auto. qed.
lemma cca_h_value m0 x0 : hoare[SharedCCAOracles.h :
 ROH.m=m0 /\ input=x0 ==>
 ROH.m.[x0]=Some res /\ cache_extends m0 ROH.m].
proof. by proc; call (roh_get_value m0 x0); auto. qed.
lemma cca_h_cached m0 x0 y0 : hoare[SharedCCAOracles.h :
 ROH.m=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==>
 res=y0 /\ ROH.m=m0].
proof. by proc; call (roh_get_cached m0 x0 y0); auto. qed.
lemma cca_h_frame roe0 rof0 rog0 : hoare[SharedCCAOracles.h :
 ROE.m=roe0 /\ ROF.m=rof0 /\ ROG.m=rog0 ==> ROE.m=roe0 /\ ROF.m=rof0 /\ ROG.m=rog0].
proof. proc; inline *; sp; if; auto. qed.

(* A cached reply retains all four tables: repeated requests do not resample,
   and another port cannot change the stored answer. *)
lemma cca_oracle_ports_eof m0 x0 y0 : hoare[SharedCCAOracles.h :
 ROH.m=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==> res=y0 /\ ROH.m=m0].
proof. exact(cca_h_cached m0 x0 y0). qed.
