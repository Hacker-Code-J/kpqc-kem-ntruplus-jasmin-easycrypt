require import AllCore IntDiv Distr.
from Jasmin require import JWord.
require import Array768.
require import NTRUPlus768BasemulAlgebra NTRUPlus768Crepmod3Algebra.
require import NTRUPlus768PolyCBD1Algebra NTRUPlus768PKEModel.

(* Finite array-model normalization/checking glue. These procedures are not
   claimed to be new extracted or exported native entry points. *)
op [opaque] rrec_center (x:int) =
 let z=x %% 3457 in if 1728<z then z-3457 else z.
op [opaque] rrec_normalize (a:W16.t Array768.t) =
 Array768.init(fun j=>W16.of_int(rrec_center(coeff a.[j]))).
op [opaque] rrec_trit_prefix (a:W16.t Array768.t) (n:int) =
 forall j,0<=j<n => is_trit(coeff a.[j]).

module RRecNormalize = {
 proc run(ap:W16.t Array768.t) : W16.t Array768.t = {
  var output:W16.t Array768.t; var i:int;
  output <- witness; i <- 0;
  while(i<768){
   output.[i] <- W16.of_int(rrec_center(coeff ap.[i]));
   i <- i+1;
  }
  return output;
 }
}.
module RRecTrit = {
 proc check(ap:W16.t Array768.t) : bool = {
  var valid:bool; var i:int;
  valid <- true; i <- 0;
  while(i<768){
   valid <- valid /\ is_trit(coeff ap.[i]);
   i <- i+1;
  }
  return valid;
 }
}.

lemma rrec_normalize_lossless : islossless RRecNormalize.run.
proof. proc; while(0<=i<=768)(768-i); auto=> />; smt(). qed.
lemma rrec_trit_lossless : islossless RRecTrit.check.
proof. proc; while(0<=i<=768)(768-i); auto=> />; smt(). qed.

lemma rrec_normalize_functional a0 : hoare[RRecNormalize.run : ap=a0 ==>res=rrec_normalize a0].
proof.
 proc; while(ap=a0 /\ 0<=i<=768 /\ forall j,0<=j<i => output.[j]=(rrec_normalize a0).[j]).
 + auto=> /> &hr hi0 hi768 hprefix hlt; split; first smt().
   move=>j hjlo hjhi; rewrite Array768.get_setE 1:/#.
   case(j=i{hr})=>heq.
   - rewrite heq /rrec_normalize Array768.initiE 1:/# /rrec_center; smt().
   have hjold:0<=j<i{hr} by smt().
   exact(hprefix j hjold).
 auto=> />; split; first smt().
 move=>i output hexit hi0 hi768 hprefix.
 apply Array768.tP=>j hj; apply hprefix; smt().
qed.
lemma rrec_trit_functional a0 : hoare[RRecTrit.check : ap=a0 ==>res=pke_domain a0].
proof.
 proc; while(ap=a0 /\ 0<=i<=768 /\ valid=rrec_trit_prefix a0 i).
 + auto=> /> &hr hi0 hi768 hlt; split; first smt().
   rewrite /rrec_trit_prefix; smt().
 auto=> />; split; first by rewrite /rrec_trit_prefix; smt().
 move=>i hexit hi0 hi768.
 have ->:i=768 by smt().
 by rewrite /rrec_trit_prefix /pke_domain /poly_cbd1_trit_output.
qed.

lemma rrec_center_range x : -1728<=rrec_center x<=1728.
proof.
 have h:0<=x%%3457<3457 by smt(IntDiv.modz_ge0 IntDiv.ltz_pmod).
 rewrite /rrec_center /=; case(1728<x%%3457)=>hz; smt().
qed.
lemma rrec_center_mod x : rrec_center x %%3457=x%%3457.
proof.
 rewrite /rrec_center /=; case(1728<x%%3457)=>hz;
 smt(IntDiv.modz_small IntDiv.modzDm IntDiv.modzMm).
qed.
