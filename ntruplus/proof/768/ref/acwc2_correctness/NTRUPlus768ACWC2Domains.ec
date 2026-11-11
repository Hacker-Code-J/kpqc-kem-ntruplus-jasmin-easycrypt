require import AllCore List Distr DList Finite StdBigop StdOrder.
from Jasmin require import JWord.
require import Array96 Array192 Array768.
require import NTRUPlus768ROMDistributions NTRUPlus768CBDDistribution.
require import NTRUPlus768PKEModel NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768BasemulAlgebra NTRUPlus768Crepmod3Algebra NTRUPlus768PolyCBD1Algebra.
import RField RealOrder Bigreal.

(* These are symbolic finite lists, never an expanded enumeration of
   3^768 trit vectors or 2^768 messages. Weights are the actual unconditioned CBD law. *)
op [opaque] acwc2_r_enum : pke_poly list = to_seq(support pke_psi1).
op [opaque] acwc2_r_weight (r:pke_poly) = mu1 pke_psi1 r.
op [opaque] acwc2_message_enum : W8.t Array96.t list = to_seq(support uniform96).
op acwc2_coeff_list (r:pke_poly) = map coeff (Array768.to_list r).

lemma acwc2_dmap_finite ['a 'b] (d:'a distr) (f:'a -> 'b) :
 is_finite(support d) => is_finite(support(dmap d f)).
proof.
 move=>hd; rewrite /dmap; apply finite_dlet=> // x hx.
 exact(finite_dunit(f x)).
qed.
lemma acwc2_dlist_finite ['a] (d:'a distr) n :
 0<=n => is_finite(support d) => is_finite(support(dlist d n)).
proof.
 move=>hn hd.
 apply(finite_leq (fun xs:'a list=>size xs=max 0 n /\ all (support d) xs)).
 + move=>xs; rewrite supp_dlist // /max; smt().
 exact(finite_list n (support d) hd).
qed.
lemma acwc2_psi1_finite : is_finite(support pke_psi1).
proof.
 rewrite /pke_psi1; apply acwc2_dmap_finite.
 exact(acwc2_dlist_finite dcbd 768 _ dcbd_finite).
qed.
lemma acwc2_dcbd_support x : x \in dcbd <=> is_trit x.
proof. rewrite /support dcbd_point /is_trit; smt(). qed.
lemma acwc2_coeff_list_size r : size(acwc2_coeff_list r)=768.
proof. by rewrite /acwc2_coeff_list size_map Array768.size_to_list. qed.
lemma acwc2_coeff_list_nth r i : 0<=i<768 =>
 nth 0 (acwc2_coeff_list r) i=coeff r.[i].
proof.
 move=>hi; rewrite /acwc2_coeff_list (nth_map witness) 1:Array768.size_to_list 1:hi.
 by rewrite Array768.get_to_list.
qed.
lemma acwc2_word_arrayK r : cbd_word_array(acwc2_coeff_list r)=r.
proof.
 rewrite /cbd_word_array /acwc2_coeff_list -map_comp.
 have he:map (W16.of_int \o coeff) (Array768.to_list r)=Array768.to_list r.
 + rewrite -{2}(map_id (Array768.to_list r)); apply/eq_in_map=>w hw.
   by rewrite /(\o) /idfun -(NTRUPlus768Crepmod3Algebra.word_from_coeff w).
 by rewrite he Array768.to_listK.
qed.
lemma acwc2_coeff_listK xs : xs \in dlist dcbd 768 =>
 acwc2_coeff_list(cbd_word_array xs)=xs.
proof.
 move=>hxs.
 have hs:=supp_dlist_size dcbd 768 xs _ hxs; first done.
 have hall:all (support dcbd) xs by smt(supp_dlist).
 rewrite /acwc2_coeff_list /cbd_word_array Array768.of_listK; first by rewrite size_map hs.
 rewrite -map_comp -{2}(map_id xs); apply/eq_in_map=>x hx.
 have ht:is_trit x by rewrite -acwc2_dcbd_support; move:hall; rewrite allP=>hall; exact(hall x hx).
 rewrite /(\o) /idfun; apply coeff_of_word_small.
 move:ht; rewrite /is_trit.
 case(x= -1)=>hm; first by rewrite hm.
 case(x=0)=>hz; first by rewrite hz.
 by rewrite /= =>->.
qed.
lemma acwc2_cbd_word_array_injective xs ys :
 xs \in dlist dcbd 768 => ys \in dlist dcbd 768 =>
 cbd_word_array xs=cbd_word_array ys => xs=ys.
proof.
 move=>hx hy he; rewrite -(acwc2_coeff_listK xs hx) -(acwc2_coeff_listK ys hy) he.
 done.
qed.
lemma acwc2_domain_coeff_support r : pke_domain r => acwc2_coeff_list r \in dlist dcbd 768.
proof.
 move=>hr; rewrite supp_dlist // acwc2_coeff_list_size /=.
 apply/(all_nthP _ _ 0)=>i; rewrite acwc2_coeff_list_size=>hi.
 rewrite acwc2_coeff_list_nth // acwc2_dcbd_support.
 move:hr; rewrite /pke_domain /poly_cbd1_trit_output=>hr; exact(hr i hi).
qed.
lemma acwc2_psi1_support r : r \in pke_psi1 <=> pke_domain r.
proof.
 split=>h.
 + move:(pke_psi1_trits r h); by rewrite /pke_domain.
 rewrite /pke_psi1 supp_dmap; exists(acwc2_coeff_list r); split.
 + exact(acwc2_domain_coeff_support r h).
 by rewrite acwc2_word_arrayK.
qed.
lemma acwc2_psi1_point r :
 mu1 pke_psi1 r=mu1 (dlist dcbd 768) (acwc2_coeff_list r).
proof.
 rewrite /pke_psi1 (dmap1E_can _ _ acwc2_coeff_list).
 + exact acwc2_word_arrayK.
 + exact acwc2_coeff_listK.
 done.
qed.
lemma acwc2_psi1_weight_product r :
 acwc2_r_weight r=BRM.big predT (mu1 dcbd) (acwc2_coeff_list r).
proof.
 by rewrite /acwc2_r_weight acwc2_psi1_point dlist1E // acwc2_coeff_list_size.
qed.
lemma acwc2_r_enum_uniq : uniq acwc2_r_enum.
proof. rewrite /acwc2_r_enum; exact uniq_to_seq. qed.
lemma acwc2_r_enum_support r : r \in acwc2_r_enum <=> r \in pke_psi1.
proof. rewrite /acwc2_r_enum; exact(mem_to_seq _ r acwc2_psi1_finite). qed.
lemma acwc2_r_enum_domain r : r \in acwc2_r_enum <=> pke_domain r.
proof. by rewrite acwc2_r_enum_support acwc2_psi1_support. qed.
lemma acwc2_r_weight_nonnegative r : 0%r<=acwc2_r_weight r.
proof. rewrite /acwc2_r_weight; exact(ge0_mu1 pke_psi1 r). qed.
lemma acwc2_r_weight_sum : BRA.big predT acwc2_r_weight acwc2_r_enum=1%r.
proof.
 rewrite /acwc2_r_weight /acwc2_r_enum -(fin_muE pke_psi1 predT acwc2_psi1_finite).
 exact pke_psi1_lossless.
qed.
lemma acwc2_r_weight_law event :
 mu pke_psi1 event=BRA.big event acwc2_r_weight acwc2_r_enum.
proof. rewrite /acwc2_r_weight /acwc2_r_enum; exact(fin_muE _ _ acwc2_psi1_finite). qed.

lemma acwc2_actual_cbd_event event :
 mu uniform192 (fun buf=>event(poly_cbd1_spec buf))=
 BRA.big event acwc2_r_weight acwc2_r_enum.
proof.
 have h:=dmapE uniform192 poly_cbd1_spec event.
 rewrite pke_cbd1_uniform /(\o) /= in h.
 rewrite -h; exact(acwc2_r_weight_law event).
qed.

lemma acwc2_message_finite : is_finite(support uniform96).
proof. exact(uniform_finite uniform96 uniform96_uni). qed.
lemma acwc2_message_enum_uniq : uniq acwc2_message_enum.
proof. rewrite /acwc2_message_enum; exact uniq_to_seq. qed.
lemma acwc2_message_enum_full msg : msg \in acwc2_message_enum.
proof. rewrite /acwc2_message_enum mem_to_seq 1:acwc2_message_finite; exact(uniform96_fu msg). qed.
lemma acwc2_message_point msg : mu1 uniform96 msg=1%r/(2%r^768).
proof.
 rewrite uniform96_point !div1r exprVn //.
 have h8:2%r^8=256%r by ring.
 have hp:=exprM 2%r 8 96.
 rewrite /= h8 in hp.
 by rewrite hp.
qed.
lemma acwc2_message_cardinality : size acwc2_message_enum=2^768.
proof.
 have h:=mu1_uni_ll uniform96 witness uniform96_uni uniform96_ll.
 rewrite uniform96_fu /= acwc2_message_point !div1r in h.
 have hc:(size acwc2_message_enum)%r=2%r^768.
 + apply invr_inj; rewrite /acwc2_message_enum; apply/eq_sym; exact h.
 move:hc; by rewrite fromintXn 1:// eq_fromint.
qed.
