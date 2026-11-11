require import AllCore.
module type Adv = {proc run():bool}.
section.
declare module A <: Adv.
local module Fresh = {var x:int}.
local lemma local_frame z : hoare[A.run:Fresh.x=z ==>Fresh.x=z].
proof. proc (Fresh.x=z);auto. qed.
lemma exported_same : equiv[A.run ~ A.run: ={glob A} ==> ={res,glob A}].
proof. proc true;auto. qed.
end section.
print exported_same.
lemma instantiate_unrestricted (B<:Adv) : equiv[B.run ~ B.run: ={glob B} ==> ={res,glob B}].
proof. exact(exported_same B). qed.
