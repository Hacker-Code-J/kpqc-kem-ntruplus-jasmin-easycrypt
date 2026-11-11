require import AllCore List Distr.
from Jasmin require import JWord.
require import Array32 Array192 Array224.
require import NTRUPlus768ROMDistributions NTRUPlus768HashPayloadSampling.
import RField.

(* One stream contains 224 bytes. Output length selects a prefix of that
   stream; it is never part of the random-oracle input key. *)
op raw_xof_max_output = 224.
op raw_xof_output (n:int) (s:W8.t Array224.t) =
 take n (Array224.to_list s).
op raw_head192 (s:W8.t Array224.t) : W8.t Array192.t =
 Array192.init(fun i=>s.[i]).
op raw_tail32 (s:W8.t Array224.t) : W8.t Array32.t =
 Array32.init(fun i=>s.[i+192]).
op raw_split192 (s:W8.t Array224.t) = (raw_head192 s,raw_tail32 s).
op raw_join192 (p:W8.t Array192.t*W8.t Array32.t) : W8.t Array224.t =
 Array224.init(fun i=>if i<192 then p.`1.[i] else p.`2.[i-192]).

lemma raw_join192_head p : raw_head192(raw_join192 p)=p.`1.
proof.
 apply Array192.tP=>i hi.
 rewrite /raw_head192 Array192.initiE //=.
 rewrite /raw_join192 Array224.initiE 1:/#; smt().
qed.
lemma raw_join192_tail p : raw_tail32(raw_join192 p)=p.`2.
proof.
 apply Array32.tP=>i hi.
 rewrite /raw_tail32 Array32.initiE //=.
 rewrite /raw_join192 Array224.initiE 1:/#; smt().
qed.
lemma raw_split192_join p : raw_split192(raw_join192 p)=p.
proof. by rewrite /raw_split192 raw_join192_head raw_join192_tail; case p. qed.
lemma raw_join192_split s : raw_join192(raw_split192 s)=s.
proof.
 apply Array224.tP=>i hi.
 rewrite /raw_join192 /raw_split192 /= Array224.initiE //.
 case(i<192)=>hc.
 + by rewrite hc /raw_head192 Array192.initiE 1:/#.
 rewrite hc /raw_tail32 Array32.initiE 1:/#; smt().
qed.
lemma raw_uniform192_32_join :
 dmap (uniform192 `*` uniform32) raw_join192=uniform224.
proof.
 apply eq_distr=>s.
 rewrite (dmap1E_can _ _ raw_split192).
 + exact raw_join192_split.
 + move=>p _; exact(raw_split192_join p).
 rewrite /raw_split192 dprod1E uniform192_point uniform32_point uniform224_point.
 by rewrite -exprD_nneg //.
qed.
lemma raw_uniform32_192_join :
 dmap (uniform32 `*` uniform192) hash_join=uniform224.
proof. exact uniform224_join_law. qed.

lemma raw_xof_output_size n s : 0<=n<=raw_xof_max_output => size(raw_xof_output n s)=n.
proof. move=>hn; rewrite /raw_xof_output size_takel // Array224.size_to_list; exact hn. qed.
lemma raw_xof_output_prefix i j s : i<=j =>
 take i (raw_xof_output j s)=raw_xof_output i s.
proof. by move=>hij; rewrite /raw_xof_output take_take hij. qed.
lemma raw_xof_output_full s : raw_xof_output raw_xof_max_output s=Array224.to_list s.
proof. by rewrite /raw_xof_output /raw_xof_max_output take_oversize ?Array224.size_to_list. qed.
lemma raw_xof_output_head192 s : raw_xof_output 192 s=Array192.to_list(raw_head192 s).
proof.
 apply(eq_from_nth witness).
 + by rewrite raw_xof_output_size // Array192.size_to_list.
 move=>i hi; move:hi; rewrite raw_xof_output_size // =>hi.
 rewrite /raw_xof_output nth_take 1,2:/# Array224.get_to_list.
 rewrite Array192.get_to_list // /raw_head192 Array192.initiE //.
qed.
lemma raw_xof_output_head32 s : raw_xof_output 32 s=Array32.to_list(hash_head s).
proof.
 apply(eq_from_nth witness).
 + by rewrite raw_xof_output_size // Array32.size_to_list.
 move=>i hi; move:hi; rewrite raw_xof_output_size // =>hi.
 rewrite /raw_xof_output nth_take 1,2:/# Array224.get_to_list.
 rewrite Array32.get_to_list // /hash_head Array32.initiE //.
qed.
lemma raw_xof_sampling_eof i j s : 0<=i<=j<=224 =>
 size(raw_xof_output i s)=i /\ take i(raw_xof_output j s)=raw_xof_output i s.
proof. move=>h; split; [apply raw_xof_output_size|apply raw_xof_output_prefix]; smt(). qed.
