require import AllCore.
module type Adv = {proc run():bool}.
section.
declare module A <: Adv.
module Fresh = {var x:int}.
local lemma global_frame z : hoare[A.run:Fresh.x=z ==>Fresh.x=z].
proof. proc (Fresh.x=z);auto. qed.
end section.
