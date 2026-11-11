require import AllCore List Distr Ring StdOrder.
require import Array768.
require import NTRUPlus768INJCollision.
import RField.

(* A concrete symbolic index list for the union bound. It is not expanded
   or executed by an attacker: alltuples is the library's finite iteration
   of Cartesian products, followed by the actual array constructor. *)
op [opaque] sr_alphabet:int list = range (-2) 3.
op [opaque] sr_short_vectors:inj_vector list =
 map (Array768.of_list 0) (alltuples 768 sr_alphabet).
op [opaque] sr_short_pairs:inj_pair list =
 allpairs (fun v w=>(v,w)) sr_short_vectors sr_short_vectors.

lemma sr_alphabet_mem x : x \in sr_alphabet <=> -2<=x<=2.
proof. rewrite /sr_alphabet mem_range;smt(). qed.
lemma sr_alphabet_size : size sr_alphabet=5.
proof. by rewrite /sr_alphabet size_range. qed.
lemma sr_short_vectors_size : size sr_short_vectors=5^768.
proof.
 by rewrite /sr_short_vectors size_map size_alltuples sr_alphabet_size /=.
qed.
lemma sr_short_vectors_mem v : v \in sr_short_vectors <=> inj_short v.
proof.
 rewrite /sr_short_vectors mapP;split.
 + move=>[xs [hx ->]].
   move:hx;rewrite alltuplesP /=;move=>[hs hall].
   rewrite /inj_short;move=>i hi.
   rewrite Array768.get_of_list 1:hi -sr_alphabet_mem.
   have hn:=iffRL _ _ (all_nthP (mem sr_alphabet) xs 0) hall.
   apply hn;by rewrite hs.
 move=>hv;exists(Array768.to_list v);split.
 + rewrite alltuplesP Array768.size_to_list /=.
   apply/(all_nthP _ _ witness)=>i hi.
   move:hi;rewrite Array768.size_to_list /=;move=>hi.
   rewrite sr_alphabet_mem.
   exact(hv i hi).
 by rewrite Array768.to_listK.
qed.
lemma sr_short_pairs_mem z : z \in sr_short_pairs <=> inj_short z.`1 /\ inj_short z.`2.
proof.
 rewrite /sr_short_pairs allpairsP;split.
 + move=>[p [hp [hq ->]]];split.
   - exact(iffLR _ _ (sr_short_vectors_mem p.`1) hp).
   exact(iffLR _ _ (sr_short_vectors_mem p.`2) hq).
 move=>[hp hq];exists z;split.
 + exact(iffRL _ _ (sr_short_vectors_mem z.`1) hp).
 split;first exact(iffRL _ _ (sr_short_vectors_mem z.`2) hq).
 clear hp hq;by case z.
qed.
lemma sr_short_pairs_size : size sr_short_pairs=25^768.
proof.
 rewrite /sr_short_pairs size_allpairs !sr_short_vectors_size.
 by rewrite -IntID.exprMn 1:// /=.
qed.
lemma sr_short_pairs_size_real : (size sr_short_pairs)%r=25%r^768.
proof. by rewrite sr_short_pairs_size -RField.fromintXn. qed.
