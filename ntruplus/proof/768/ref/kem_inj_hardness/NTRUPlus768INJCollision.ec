require import AllCore IntDiv Ring.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768PKEModel NTRUPlus768SecModel NTRUPlus768BasemulAlgebra.
require import NTRUPlus768Crepmod3Algebra NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768CyclotomicFactorization NTRUPlus768EvaluationSemantics NTRUPlus768TerminalRepresentation.
require import NTRUPlus768CoefficientRecovery.

type inj_vector = int Array768.t.
type inj_pair = inj_vector * inj_vector.
(* Differences are taken after signed-word decoding, in unbounded integer
   arithmetic. No 16-bit subtraction or modular wraparound occurs. *)
op [opaque] inj_word_difference (x y:pke_poly) : inj_vector =
 Array768.map2(fun a b=>coeff a-coeff b)x y.
op [opaque] inj_difference_pair (z:sec_collision) : inj_pair =
 (inj_word_difference z.`3 z.`4,inj_word_difference z.`1 z.`2).
op [opaque] inj_zero : inj_vector = Array768.init(fun _=>0).
op inj_zero_pair : inj_pair = (inj_zero,inj_zero).
op inj_short (v:inj_vector) = forall i,0<=i<768=> -2<=v.[i]<=2.
op inj_pair_nonzero (v w:inj_vector) = v<>inj_zero \/ w<>inj_zero.
op inj_relation (h:NTRUPoly.poly) (v w:inj_vector) =
 eqm_global (NTRUPoly.PolyComRing.( + ) (NTRUPoly.PolyComRing.( * ) h (int_poly v)) (int_poly w)) NTRUPoly.poly0.
op inj_short_win (h:NTRUPoly.poly) (z:inj_pair) =
 inj_short z.`1 /\ inj_short z.`2 /\ inj_pair_nonzero z.`1 z.`2 /\ inj_relation h z.`1 z.`2.

lemma inj_word_difference_get x y i : 0<=i<768=>
 (inj_word_difference x y).[i]=coeff x.[i]-coeff y.[i].
proof. move=>hi;by rewrite /inj_word_difference Array768.map2iE. qed.
lemma inj_zero_get i : 0<=i<768=>inj_zero.[i]=0.
proof. move=>hi;by rewrite /inj_zero Array768.initiE. qed.
lemma inj_word_difference_zero x y : inj_word_difference x y=inj_zero <=> x=y.
proof.
 split.
 + move=>he;apply Array768.tP=>i hi.
   have /= h:=congr1(fun a:inj_vector=>a.[i]) _ _ he.
   rewrite (inj_word_difference_get x y i hi)(inj_zero_get i hi) in h.
   have hc:coeff x.[i]=coeff y.[i] by smt().
   by rewrite (word_from_coeff x.[i])(word_from_coeff y.[i]) hc.
 move=>->;apply Array768.tP=>i hi.
 by rewrite (inj_word_difference_get y y i hi)(inj_zero_get i hi);smt().
qed.
lemma inj_word_difference_short x y : pke_domain x=>pke_domain y=>inj_short(inj_word_difference x y).
proof.
 rewrite /pke_domain /poly_cbd1_trit_output=>hx hy i hi.
 have ha:=hx i hi;have hb:=hy i hi.
 rewrite /is_trit in ha;rewrite /is_trit in hb.
 rewrite(inj_word_difference_get x y i hi);smt().
qed.
lemma inj_difference_pair_nonzero (z:sec_collision) : (z.`1,z.`3)<>(z.`2,z.`4)=>
 inj_pair_nonzero (inj_difference_pair z).`1 (inj_difference_pair z).`2.
proof.
 rewrite /inj_pair_nonzero /inj_difference_pair /= !inj_word_difference_zero;smt().
qed.

lemma inj_zero_pair_loses h : !inj_short_win h inj_zero_pair.
proof. by rewrite /inj_short_win /inj_zero_pair /inj_pair_nonzero /=. qed.
