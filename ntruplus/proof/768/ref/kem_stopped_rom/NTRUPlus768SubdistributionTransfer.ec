require import AllCore Distr StdOrder.
import RealOrder.

(* Lower event mass is enough even when the actual program can diverge. *)
lemma prefix_event_lower (actual bounded_actual bounded_ideal ideal ecoll etail:real) :
 bounded_actual <= actual =>
 bounded_ideal-ecoll <= bounded_actual =>
 ideal-etail <= bounded_ideal =>
 ideal-(ecoll+etail) <= actual.
proof. smt(). qed.

lemma complementary_event_transfer (x xc y yc epsilon:real) :
 x+xc <= 1%r => y+yc=1%r =>
 y-epsilon <= x => yc-epsilon <= xc =>
 `|x-y| <= epsilon.
proof. rewrite ler_norml; smt(). qed.

lemma subdistribution_missing_mass (mass good epsilon:real) :
 mass<=1%r => good<=mass => 1%r-epsilon<=good =>
 0%r<=1%r-mass<=epsilon.
proof. smt(). qed.
