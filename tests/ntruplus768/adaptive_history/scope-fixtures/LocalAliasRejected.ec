require import AllCore.
module type Adv = {proc run():bool}.
module PublicState = {var x:int}.
section.
declare module A <: Adv.
local module Fresh = PublicState.
local lemma alias_frame z : hoare[A.run:Fresh.x=z ==>Fresh.x=z].
proof. proc (Fresh.x=z);auto. qed.
end section.
