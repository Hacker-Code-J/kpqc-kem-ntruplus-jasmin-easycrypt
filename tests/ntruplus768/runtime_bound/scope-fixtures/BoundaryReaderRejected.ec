require import AllCore List.
module OldPrivate = {var h:int var rows:int list}.
module type Adv = {proc run():bool}.
lemma frame (A<:Adv {-OldPrivate}) xs : hoare[A.run:OldPrivate.rows=xs ==>OldPrivate.rows=xs].
proof. proc (OldPrivate.rows=xs);auto. qed.
module Reader : Adv = {proc run():bool = {return OldPrivate.rows=[];}}.
lemma reject_reader xs : hoare[Reader.run:OldPrivate.rows=xs ==>OldPrivate.rows=xs].
proof. exact(frame Reader xs). qed.
