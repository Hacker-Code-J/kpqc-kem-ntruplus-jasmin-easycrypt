require import AllCore.
module type Adv = {proc run():bool}.
section.
local module Fresh = {var x:int}.
declare module A <: Adv.
local lemma local_frame z : hoare[A.run:Fresh.x=z ==>Fresh.x=z].
proof. proc (Fresh.x=z);auto. qed.
end section.
