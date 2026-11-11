require import AllCore List.
module type O = {proc get():int}.
module type Adv(O:O) = {proc run():bool}.
module type Runner = {proc run():bool}.
module Zero : O = {proc get():int={return 0;}}.
module Original(A:Adv) = {
 proc run():bool={var b; b<@A(Zero).run();return b;}
}.
section.
declare module A <: Adv.
local module Fresh = {
 var rows:int list
 proc get():int={rows<-0::rows;return 0;}
}.
local module Stateful : Runner = {
 proc run():bool={var b;Fresh.rows<-[];b<@A(Fresh).run();return b;}
}.
local lemma actual_coupling :
 equiv[Stateful.run ~ Original(A).run: ={glob A} ==> ={res}].
proof.
 proc;call(_:true);first by proc;auto.
 auto.
qed.
lemma reduction_exists : exists(B<:Runner), forall &m,
 Pr[B.run()@&m:res]=Pr[Original(A).run()@&m:res].
proof. exists Stateful;move=> &m;byequiv actual_coupling=> //. qed.
end section.
print reduction_exists.
lemma same_unrestricted_A (C<:Adv) : exists(B<:Runner), forall &m,
 Pr[B.run()@&m:res]=Pr[Original(C).run()@&m:res].
proof. exact(reduction_exists C). qed.

module PublicState = {var value:int}.
module Reader(O:O) : Runner = {
 proc run():bool={var y;y<@O.get();return y=PublicState.value;}
}.
lemma reader_still_admitted : exists(B<:Runner), forall &m,
 Pr[B.run()@&m:res]=Pr[Original(Reader).run()@&m:res].
proof. exact(reduction_exists Reader). qed.
