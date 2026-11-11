require import AllCore IntDiv.
from Jasmin require import JWord.
require import Array768 NTRUPlus768BasemulAlgebra NTRUPlus768Crepmod3Algebra.
require import NTRUPlus768RRecWordChecks.

(* Coefficients are interpreted as signed 16-bit words.  The remainder,
   comparisons and subtraction below are explicit bounded-word operations;
   no opaque rrec_center/is_trit call is assigned a unit price.  rt_work is
   a local ghost charge, not an observable global counter. *)
module RTFixedWordChecks = {
 proc normalize(ap:W16.t Array768.t):(W16.t Array768.t)*int = {
  var output:W16.t Array768.t;var i,x,z,rt_work:int;
  rt_work<-2304;
  output<-witness;rt_work<-rt_work+769;
  i<-0;rt_work<-rt_work+1;
  rt_work<-rt_work+2;
  while(i<768){
   x<-coeff ap.[i];rt_work<-rt_work+2;
   z<-x%%3457;rt_work<-rt_work+2;
   rt_work<-rt_work+2;
   if(1728<z){z<-z-3457;rt_work<-rt_work+2;}
   output.[i]<-W16.of_int z;rt_work<-rt_work+2;
   i<-i+1;rt_work<-rt_work+2;
   rt_work<-rt_work+2;
  }
  rt_work<-rt_work+2305;return(output,rt_work);
 }
 proc trit(ap:W16.t Array768.t):bool*int = {
  var valid,v0,v1,v2:bool;var i,x,rt_work:int;
  rt_work<-2304;
  valid<-true;rt_work<-rt_work+1;
  i<-0;rt_work<-rt_work+1;
  rt_work<-rt_work+2;
  while(i<768){
   x<-coeff ap.[i];rt_work<-rt_work+2;
   v0<-(x = -1);rt_work<-rt_work+2;
   v1<-(x = 0);rt_work<-rt_work+2;
   v2<-(x = 1);rt_work<-rt_work+2;
   valid<-valid /\ (v0 \/ v1 \/ v2);rt_work<-rt_work+4;
   i<-i+1;rt_work<-rt_work+2;
   rt_work<-rt_work+2;
  }
  rt_work<-rt_work+1;return(valid,rt_work);
 }
}.
lemma rt_fixed_normalize_projection :
 equiv[RTFixedWordChecks.normalize ~ RRecNormalize.run : ={ap} ==>res{1}.`1=res{2}].
proof.
 proc;wp;while(={ap,i,output}).
 + case(1728<coeff ap{1}.[i{1}]%%3457).
   - rcondt{1} 6;first by auto.
     auto=> />;rewrite /rrec_center;smt().
   rcondf{1} 6;first by auto.
   auto=> />;rewrite /rrec_center;smt().
 auto.
qed.
lemma rt_fixed_normalize_cost :
 hoare[RTFixedWordChecks.normalize:true ==>0<=res.`2<=16133].
proof.
 proc;wp;while(0<=i<=768 /\ 0<=rt_work<=3076+14*i).
 + seq 5:(0<=i<768 /\ 0<=rt_work<=3082+14*i).
   - auto=> />;smt().
   if;auto=> />;smt().
 auto=> />;smt().
qed.
lemma rt_fixed_trit_projection :
 equiv[RTFixedWordChecks.trit ~ RRecTrit.check : ={ap} ==>res{1}.`1=res{2}].
proof. proc;wp;while(={ap,i,valid});auto=> />;by rewrite /is_trit. qed.
lemma rt_fixed_trit_cost :
 hoare[RTFixedWordChecks.trit:true ==>res.`2=14597].
proof. proc;wp;while(0<=i<=768 /\ rt_work=2308+16*i);auto=> />;smt(). qed.
op rt_fixed_normalize_bound:int = 16133.
op rt_fixed_trit_bound:int = 14597.
lemma rt_fixed_normalize_bound_cost :
 hoare[RTFixedWordChecks.normalize:true ==>0<=res.`2<=rt_fixed_normalize_bound].
proof. exact rt_fixed_normalize_cost. qed.
lemma rt_fixed_trit_bound_cost :
 hoare[RTFixedWordChecks.trit:true ==>0<=res.`2<=rt_fixed_trit_bound].
proof. conseq rt_fixed_trit_cost;auto=> />;smt(). qed.
