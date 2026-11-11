require import AllCore List.
type snapshot = { rows:int list; context:int }.
op update (s:snapshot) x = {| rows=x::s.`rows; context=s.`context |}.
module type Store = {
 proc init(c:int):unit
 proc snapshot():snapshot
 proc put(x:int):unit
}.
module Algorithm(S:Store) = {
 proc run(x:int):snapshot = {
  var result:snapshot;
  S.put(x);result<@S.snapshot();return result;
 }
}.
lemma port_contract (S<:Store) (view:(glob S)->snapshot) s0 x0 :
 (forall s x,hoare[S.put:view(glob S)=s /\ arg=x ==>view(glob S)=update s x]) =>
 (forall s,hoare[S.snapshot:view(glob S)=s ==>res=s /\ view(glob S)=s]) =>
 hoare[Algorithm(S).run:view(glob S)=s0 /\ x=x0 ==>res=update s0 x0].
proof. move=>hp hs;proc;call(hs(update s0 x0));call(hp s0 x0);auto. qed.
module type Adv = {proc run():bool}.
section.
declare module A <: Adv.
local module Fresh : Store = {
 var st:snapshot
 proc init(c:int):unit = {st<-{|rows=[];context=c|};}
 proc snapshot():snapshot = {return st;}
 proc put(x:int):unit = {st<-update st x;}
}.
local lemma fresh_preserved s0 : hoare[A.run:Fresh.st=s0 ==>Fresh.st=s0].
proof. proc (Fresh.st=s0);auto. qed.
local lemma local_instantiation s0 x0 :
 hoare[Algorithm(Fresh).run:Fresh.st=s0 /\ x=x0 ==>res=update s0 x0].
proof.
 apply(port_contract Fresh (fun (s:(glob Fresh))=>s) s0 x0).
 + move=>s x;proc;auto.
 move=>s;proc;auto.
qed.
end section.
