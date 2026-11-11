require import AllCore.
module type Adv = {proc run():bool}.
section.
declare module A <: Adv.
local module Fresh = {var x:int}.
lemma escaped_frame z : hoare[A.run:Fresh.x=z ==>Fresh.x=z].
proof. proc (Fresh.x=z);auto. qed.
end section.
