require import AllCore.
module type Adv = {proc run():bool}.
module T : Adv = {proc run():bool={return true;}}.
lemma module_exists : exists(B<:Adv), islossless B.run.
proof. exists T;proc;auto. qed.
