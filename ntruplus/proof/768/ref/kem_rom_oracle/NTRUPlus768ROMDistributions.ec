require import AllCore IntDiv List Distr DList.
from Jasmin require import JWord JArray.
require import Array32 Array96 Array192 Array224.

(* Concrete byte distributions, with no abstract output-distribution axiom. *)
lemma byte_uniform_point (x : W8.t) :
  mu1 W8.dword x = 1%r / 256%r.
proof.
  rewrite /W8.dword duniform1E W8.all_wordsP /=.
  have hu : uniq W8.all_words.
  + rewrite W8.all_wordsE map_inj_in_uniq ?iota_uniq //.
    move=> a b; rewrite !mema_iota /=.
    move=> ha hb he.
    have h := congr1 W8.to_uint _ _ he.
    move: h; rewrite !W8.of_uintK /= !modz_small //.
  by rewrite undup_id // W8.all_wordsE size_map size_iota /=.
qed.

lemma byte_list_uniform_point (xs : W8.t list) :
  mu1 (dlist W8.dword (size xs)) xs = (1%r / 256%r) ^ (size xs).
proof.
  elim xs=> [|x xs ih].
  + by rewrite dlist01E // RField.expr0.
  rewrite dlistS1E byte_uniform_point ih /=.
  smt(RField.exprS size_ge0).
qed.

op uniform32 = dmap (dlist W8.dword 32) (Array32.of_list W8.zero).
lemma uniform32_ll : is_lossless uniform32.
proof. by apply/dmap_ll/dlist_ll/W8.dword_ll. qed.
lemma uniform32_uni : is_uniform uniform32.
proof.
  apply dmap_uni_in_inj; last exact (dlist_uni W8.dword 32 W8.dword_uni).
  move=> xs ys hs ht he.
  have hxs := supp_dlist_size W8.dword 32 xs _ hs; first trivial.
  have hys := supp_dlist_size W8.dword 32 ys _ ht; first trivial.
  have := congr1 Array32.to_list _ _ he.
  by rewrite !Array32.of_listK.
qed.
lemma uniform32_point (x : W8.t Array32.t) : mu1 uniform32 x = (1%r / 256%r)^32.
proof.
  rewrite /uniform32 (dmap1E_can _ _ Array32.to_list).
  + exact (Array32.to_listK W8.zero).
  + move=> xs hs; apply Array32.of_listK.
    exact (supp_dlist_size W8.dword 32 xs _ hs).
  have hx : size (Array32.to_list x) = 32 by rewrite Array32.size_to_list.
  by rewrite -hx byte_list_uniform_point.
qed.
lemma uniform32_fu : is_full uniform32.
proof.
  move=> x; apply/supp_dmap; exists (Array32.to_list x); split.
  + rewrite supp_dlist 1://.
    rewrite Array32.size_to_list /=.
    split; first trivial.
    apply/List.allP=> b hb.
    exact (W8.dword_fu b).
  by rewrite Array32.to_listK.
qed.

op uniform96 = dmap (dlist W8.dword 96) (Array96.of_list W8.zero).
lemma uniform96_ll : is_lossless uniform96.
proof. by apply/dmap_ll/dlist_ll/W8.dword_ll. qed.
lemma uniform96_uni : is_uniform uniform96.
proof.
  apply dmap_uni_in_inj; last exact (dlist_uni W8.dword 96 W8.dword_uni).
  move=> xs ys hs ht he.
  have hxs := supp_dlist_size W8.dword 96 xs _ hs; first trivial.
  have hys := supp_dlist_size W8.dword 96 ys _ ht; first trivial.
  have := congr1 Array96.to_list _ _ he.
  by rewrite !Array96.of_listK.
qed.
lemma uniform96_point (x : W8.t Array96.t) : mu1 uniform96 x = (1%r / 256%r)^96.
proof.
  rewrite /uniform96 (dmap1E_can _ _ Array96.to_list).
  + exact (Array96.to_listK W8.zero).
  + move=> xs hs; apply Array96.of_listK.
    exact (supp_dlist_size W8.dword 96 xs _ hs).
  have hx : size (Array96.to_list x) = 96 by rewrite Array96.size_to_list.
  by rewrite -hx byte_list_uniform_point.
qed.
lemma uniform96_fu : is_full uniform96.
proof.
  move=> x; apply/supp_dmap; exists (Array96.to_list x); split.
  + rewrite supp_dlist 1://.
    rewrite Array96.size_to_list /=.
    split; first trivial.
    apply/List.allP=> b hb.
    exact (W8.dword_fu b).
  by rewrite Array96.to_listK.
qed.

op uniform192 = dmap (dlist W8.dword 192) (Array192.of_list W8.zero).
lemma uniform192_ll : is_lossless uniform192.
proof. by apply/dmap_ll/dlist_ll/W8.dword_ll. qed.
lemma uniform192_uni : is_uniform uniform192.
proof.
  apply dmap_uni_in_inj; last exact (dlist_uni W8.dword 192 W8.dword_uni).
  move=> xs ys hs ht he.
  have hxs := supp_dlist_size W8.dword 192 xs _ hs; first trivial.
  have hys := supp_dlist_size W8.dword 192 ys _ ht; first trivial.
  have := congr1 Array192.to_list _ _ he.
  by rewrite !Array192.of_listK.
qed.
lemma uniform192_point (x : W8.t Array192.t) : mu1 uniform192 x = (1%r / 256%r)^192.
proof.
  rewrite /uniform192 (dmap1E_can _ _ Array192.to_list).
  + exact (Array192.to_listK W8.zero).
  + move=> xs hs; apply Array192.of_listK.
    exact (supp_dlist_size W8.dword 192 xs _ hs).
  have hx : size (Array192.to_list x) = 192 by rewrite Array192.size_to_list.
  by rewrite -hx byte_list_uniform_point.
qed.
lemma uniform192_fu : is_full uniform192.
proof.
  move=> x; apply/supp_dmap; exists (Array192.to_list x); split.
  + rewrite supp_dlist 1://.
    rewrite Array192.size_to_list /=.
    split; first trivial.
    apply/List.allP=> b hb.
    exact (W8.dword_fu b).
  by rewrite Array192.to_listK.
qed.

op uniform224 = dmap (dlist W8.dword 224) (Array224.of_list W8.zero).
lemma uniform224_ll : is_lossless uniform224.
proof. by apply/dmap_ll/dlist_ll/W8.dword_ll. qed.
lemma uniform224_uni : is_uniform uniform224.
proof.
  apply dmap_uni_in_inj; last exact (dlist_uni W8.dword 224 W8.dword_uni).
  move=> xs ys hs ht he.
  have hxs := supp_dlist_size W8.dword 224 xs _ hs; first trivial.
  have hys := supp_dlist_size W8.dword 224 ys _ ht; first trivial.
  have := congr1 Array224.to_list _ _ he.
  by rewrite !Array224.of_listK.
qed.
lemma uniform224_point (x : W8.t Array224.t) : mu1 uniform224 x = (1%r / 256%r)^224.
proof.
  rewrite /uniform224 (dmap1E_can _ _ Array224.to_list).
  + exact (Array224.to_listK W8.zero).
  + move=> xs hs; apply Array224.of_listK.
    exact (supp_dlist_size W8.dword 224 xs _ hs).
  have hx : size (Array224.to_list x) = 224 by rewrite Array224.size_to_list.
  by rewrite -hx byte_list_uniform_point.
qed.
lemma uniform224_fu : is_full uniform224.
proof.
  move=> x; apply/supp_dmap; exists (Array224.to_list x); split.
  + rewrite supp_dlist 1://.
    rewrite Array224.size_to_list /=.
    split; first trivial.
    apply/List.allP=> b hb.
    exact (W8.dword_fu b).
  by rewrite Array224.to_listK.
qed.

lemma rom_distributions_eof (x : W8.t Array32.t) :
  mu1 uniform32 x = (1%r / 256%r)^32.
proof. exact (uniform32_point x). qed.
