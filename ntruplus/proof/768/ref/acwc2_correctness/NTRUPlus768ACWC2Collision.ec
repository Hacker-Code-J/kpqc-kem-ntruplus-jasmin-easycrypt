require import AllCore List Distr DList Finite StdBigop StdOrder.
from Jasmin require import JWord.
require import Array768.
require import NTRUPlus768CBDDistribution NTRUPlus768PKEKeyDistribution.
require import NTRUPlus768NoiseMGF NTRUPlus768ACWC2Domains.
import RField RealOrder Bigreal.

(* Finite independence gives a product of expectations. No uniform-trit
   premise is introduced: the scalar CBD masses remain 1/4, 1/2, 1/4. *)
lemma acwc2_dlist_expect_product ['a] (d:'a distr) (f:'a -> real) n :
 0<=n => is_finite(support d) =>
 E (dlist d n) (fun xs=>BRM.big predT f xs)=(E d f)^n.
proof.
 move=>hn hd; elim: n hn=>[|n hn ih].
 + by rewrite dlist0 // exp_dunit /= BRM.big_nil expr0.
 rewrite dlistS // noise_exp_dmap.
 + apply finite_dprod=> //; exact(acwc2_dlist_finite d n hn hd).
 rewrite (eq_exp _ _ (fun (z:'a * 'a list)=>f z.`1*BRM.big predT f z.`2)).
 + move=>[x xs] _ /=; by rewrite BRM.big_consT.
 rewrite (noise_exp_dprod d (dlist d n) f (fun xs=>BRM.big predT f xs)
   hd (acwc2_dlist_finite d n hn hd)) ih exprS //.
qed.

lemma acwc2_dlist_collision ['a] (d:'a distr) n :
 0<=n => is_finite(support d) =>
 E (dlist d n) (mu1 (dlist d n))=(E d (mu1 d))^n.
proof.
 move=>hn hd.
 rewrite (eq_exp _ _ (fun xs=>BRM.big predT (mu1 d) xs)).
 + move=>xs hs; have hsize:=supp_dlist_size d n xs hn hs.
   by rewrite /= dlist1E // hsize.
 exact(acwc2_dlist_expect_product d (mu1 d) n hn hd).
qed.
lemma acwc2_dcbd_collision : E dcbd (mu1 dcbd)=3%r/8%r.
proof. by rewrite noise_dcbd_expect /= !dcbd_point /=. qed.

lemma acwc2_psi1_collision_expect :
 E pke_psi1 acwc2_r_weight=(3%r/8%r)^768.
proof.
 rewrite {1}/pke_psi1 noise_exp_dmap.
 + exact(acwc2_dlist_finite dcbd 768 _ dcbd_finite).
 rewrite (eq_exp _ _ (mu1 (dlist dcbd 768))).
 + move=>xs hs /=.
   by rewrite /acwc2_r_weight acwc2_psi1_point (acwc2_coeff_listK xs hs).
 by rewrite acwc2_dlist_collision // 1:dcbd_finite acwc2_dcbd_collision.
qed.

(* Exact collision mass of two independent draws from the actual CBD
   polynomial law, expressed over the symbolic finite trit domain. *)
lemma acwc2_r_weight_collision :
 BRA.big predT (fun r=>acwc2_r_weight r^2) acwc2_r_enum=(3%r/8%r)^768.
proof.
 have he:BRA.big predT (fun r=>acwc2_r_weight r^2) acwc2_r_enum=
   E pke_psi1 acwc2_r_weight.
 + rewrite fin_expE 1:acwc2_psi1_finite /acwc2_r_enum.
   apply BRA.eq_bigr=>r hr; rewrite /= /acwc2_r_weight; ring.
 by rewrite he acwc2_psi1_collision_expect.
qed.
