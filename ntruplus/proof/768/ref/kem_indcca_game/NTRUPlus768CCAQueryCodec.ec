require import AllCore List.
from Jasmin require import JWord.
require import Array32 Array96 Array129 Array1152 Array1153.
require import NTRUPlus768ROMDomains.

(* The entire raw input is classified: no unconditional removal of a tag.
   Every other length/tag belongs to the disjoint untyped XOF domain. *)
op decode_typed (s:W8.t list) : typed_query option =
 if size s=32 then Some (E (Array32.of_list W8.zero s)) else
 if size s=1153 /\ nth W8.zero s 0=W8.zero then
   Some (F (peel1153 (Array1153.of_list W8.zero s))) else
 if size s=1153 /\ nth W8.zero s 0=W8.one then
   Some (G (peel1153 (Array1153.of_list W8.zero s))) else
 if size s=129 /\ nth W8.zero s 0=W8.of_int 2 then
   Some (H (peel_h (Array129.of_list W8.zero s))) else None.

lemma list1153_head (a:W8.t Array1153.t) : nth W8.zero (Array1153.to_list a) 0=a.[0].
proof.
 rewrite (nth_change_dfl witness W8.zero) 1:Array1153.size_to_list 1://.
 exact Array1153.get_to_list.
qed.
lemma list129_head (a:W8.t Array129.t) : nth W8.zero (Array129.to_list a) 0=a.[0].
proof.
 rewrite (nth_change_dfl witness W8.zero) 1:Array129.size_to_list 1://.
 exact Array129.get_to_list.
qed.

lemma decode_typed_encode q : decode_typed (raw_query q)=Some q.
proof.
 case q=> x; rewrite /decode_typed /=.
 + by rewrite Array32.size_to_list /= Array32.to_listK.
 + rewrite Array1153.size_to_list /= list1153_head encode_f_tag /=.
   by rewrite Array1153.to_listK peel_encode_f.
 + rewrite Array1153.size_to_list /= list1153_head encode_g_tag /=.
   have hn : W8.one<>W8.zero by smt(tag_zero_neq_one).
   by rewrite hn /= Array1153.to_listK peel_encode_g.
 rewrite Array129.size_to_list /= list129_head encode_h_tag /=.
 by rewrite Array129.to_listK peel_encode_h; case x.
qed.

lemma decode_typed_sound s q : decode_typed s=Some q => raw_query q=s.
proof.
 rewrite /decode_typed.
 case (size s=32)=>h32.
 + move=>he.
   have hq : E (Array32.of_list W8.zero s)=q
    by exact (congr1 (fun o:typed_query option=>oget o) _ _ he).
   rewrite -hq.
   exact (Array32.of_listK W8.zero s h32).
 case (size s=1153 /\ nth W8.zero s 0=W8.zero)=>hf.
 + move=>he.
   have hq : F (peel1153 (Array1153.of_list W8.zero s))=q
    by exact (congr1 (fun o:typed_query option=>oget o) _ _ he).
   rewrite -hq /=.
   have ht : (Array1153.of_list W8.zero s).[0]=W8.zero.
   + rewrite Array1153.get_of_list 1://; by move: hf=>[_ h].
   rewrite (encode_peel_f _ ht).
   apply (Array1153.of_listK W8.zero s); smt().
 case (size s=1153 /\ nth W8.zero s 0=W8.one)=>hg.
 + move=>he.
   have hq : G (peel1153 (Array1153.of_list W8.zero s))=q
    by exact (congr1 (fun o:typed_query option=>oget o) _ _ he).
   rewrite -hq /=.
   have ht : (Array1153.of_list W8.zero s).[0]=W8.one.
   + rewrite Array1153.get_of_list 1://; by move: hg=>[_ h].
   rewrite (encode_peel_g _ ht).
   apply (Array1153.of_listK W8.zero s); smt().
 case (size s=129 /\ nth W8.zero s 0=W8.of_int 2)=>hh; last done.
 move=>he.
 have hq : H (peel_h (Array129.of_list W8.zero s))=q
  by exact (congr1 (fun o:typed_query option=>oget o) _ _ he).
 rewrite -hq /=.
 have ht : (Array129.of_list W8.zero s).[0]=W8.of_int 2.
 + rewrite Array129.get_of_list 1://; by move: hh=>[_ h].
 rewrite (encode_peel_h _ ht).
 apply (Array129.of_listK W8.zero s); smt().
qed.

lemma decode_typed_exact s q : decode_typed s=Some q <=> s=raw_query q.
proof. split; first smt(decode_typed_sound). by move=>->; exact decode_typed_encode. qed.
lemma decode_none_generic ['a 'b] (enc:'a -> 'b) (dec:'b -> 'a option) s :
 (forall q,dec (enc q)=Some q) =>
 (forall q,dec s=Some q => enc q=s) =>
 (dec s=None <=> forall q,s<>enc q).
proof.
 move=>hc hs.
 have ho : dec s<>None => dec s=Some (oget(dec s)) by exact (some_oget (dec s)).
 smt().
qed.
lemma decode_typed_none s : decode_typed s=None <=> forall q, s<>raw_query q.
proof.
 apply (decode_none_generic raw_query decode_typed s).
 + exact decode_typed_encode.
 move=>q; exact (decode_typed_sound s q).
qed.
lemma decode_typed_no_alias s t q :
 decode_typed s=Some q => decode_typed t=Some q => s=t.
proof. smt(decode_typed_sound). qed.
lemma decode_typed_wrong_length s :
 size s<>32 => size s<>1153 => size s<>129 => decode_typed s=None.
proof. by rewrite /decode_typed; smt(). qed.
lemma decode_typed_wrong_tag1153 s :
 size s=1153 => nth W8.zero s 0<>W8.zero => nth W8.zero s 0<>W8.one =>
 decode_typed s=None.
proof. by rewrite /decode_typed; smt(). qed.
lemma decode_typed_wrong_tag129 s :
 size s=129 => nth W8.zero s 0<>W8.of_int 2 => decode_typed s=None.
proof. by rewrite /decode_typed; smt(). qed.
