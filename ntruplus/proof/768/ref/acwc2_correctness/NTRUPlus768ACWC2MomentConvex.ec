require import AllCore Distr Finite List StdBigop StdOrder RealFun.
import RealOrder RField.

lemma acwc2_convex_square a b : convex (fun x:real=>x^2) a b.
proof.
 rewrite /convex=>t ht /=.
 have hp:0%r<=t*(1%r-t)*(a-b)^2.
 + apply mulr_ge0; last exact(ge0_sqr(a-b)).
   apply mulr_ge0; smt().
 have he:t*a^2+(1%r-t)*b^2-(t*a+(1%r-t)*b)^2=t*(1%r-t)*(a-b)^2 by ring.
 smt().
qed.

lemma acwc2_convex_cube_nonnegative a b : 0%r<=a =>0%r<=b =>
 convex (fun x:real=>x^3) a b.
proof.
 move=>ha hb; rewrite /convex=>t ht /=.
 have hp:0%r<=t*(1%r-t)*(a-b)^2*((1%r+t)*a+(2%r-t)*b).
 + apply mulr_ge0.
   - apply mulr_ge0; last exact(ge0_sqr(a-b)).
     apply mulr_ge0; smt().
   apply addr_ge0; apply mulr_ge0; smt().
 have he:t*a^3+(1%r-t)*b^3-(t*a+(1%r-t)*b)^3=
   t*(1%r-t)*(a-b)^2*((1%r+t)*a+(2%r-t)*b) by ring.
 smt().
qed.

lemma acwc2_convex_compose_power (f:real->real) n :
 (forall x,0%r<=f x) => (forall a b,convex f a b) =>
 0<=n => (forall a b,0%r<=a=>0%r<=b=>convex(fun x:real=>x^n)a b) =>
 forall a b,convex(fun x:real=>(f x)^n)a b.
proof.
 move=>hf hc hn hp a b t ht /=.
 have hu:=hc a b t ht.
 have hbnd:0%r<=f(t*a+(1%r-t)*b)<=t*f a+(1%r-t)*f b by smt().
 have hm:=ler_pexp n (f(t*a+(1%r-t)*b)) (t*f a+(1%r-t)*f b) hn hbnd.
 have hv:=hp (f a) (f b) (hf a) (hf b) t ht.
 exact(ler_trans _ _ _ hm hv).
qed.

lemma acwc2_convex_fourth a b : convex(fun x:real=>x^4)a b.
proof.
 have h:=acwc2_convex_compose_power (fun x:real=>x^2) 2
   ge0_sqr acwc2_convex_square _ _ a b; first smt().
 + move=>u v _ _; exact(acwc2_convex_square u v).
 move=>t ht; have hh:=h t ht.
 have e:forall (x:real),(x^2)^2=x^4 by move=>x; ring.
 by move:hh; rewrite /= !e.
qed.

lemma acwc2_convex_sixth a b : convex(fun x:real=>x^6)a b.
proof.
 have h:=acwc2_convex_compose_power (fun x:real=>x^2) 3
   ge0_sqr acwc2_convex_square _ acwc2_convex_cube_nonnegative a b; first smt().
 move=>t ht; have hh:=h t ht.
 have e:forall (x:real),(x^2)^3=x^6 by move=>x; ring.
 by move:hh; rewrite /= !e.
qed.

lemma acwc2_fourth_nonnegative (x:real) : 0%r<=x^4.
proof.
 have e:(x^2)^2=x^4 by ring.
 rewrite -e.
 exact(ge0_sqr(x^2)).
qed.

lemma acwc2_convex_eighth a b : convex(fun x:real=>x^8)a b.
proof.
 have h:=acwc2_convex_compose_power (fun x:real=>x^4) 2
   acwc2_fourth_nonnegative acwc2_convex_fourth _ _ a b; first smt().
 + move=>u v _ _; exact(acwc2_convex_square u v).
 move=>t ht; have hh:=h t ht.
 have e:forall (x:real),(x^4)^2=x^8 by move=>x; ring.
 by move:hh; rewrite /= !e.
qed.

(* A centered bounded variable is dominated, for convex tests, by the
   symmetric two-point distribution at the endpoints of its interval. *)
lemma acwc2_centered_chord (d:real distr) (f:real->real) w s :
 is_finite(support d) => is_lossless d =>
 E d idfun=0%r => (forall x,x \in d=>`|x|<=w) =>
 0%r<=w => (forall a b,convex f a b) =>
 E d (fun x=>f(s+x)) <= (f(s+w)+f(s-w))/2%r.
proof.
 move=>hd hl hz hb hw hc; case(w=0%r)=>hw0.
 + have he:E d(fun x=>f(s+x))=E d(fun _=>f s).
   - apply eq_exp=>x hx /=; have h:=hb x hx; rewrite hw0 in h.
     have ->:x=0%r by smt(RealOrder.normr_ge0 RealOrder.normr0_eq0).
     by rewrite addr0.
   rewrite he expC hl hw0 /=; smt().
 have hp:0%r<w by smt().
 pose A:=(f(s+w)+f(s-w))/2%r.
 pose B:=(f(s+w)-f(s-w))/(2%r*w).
 have hm:E d(fun x=>f(s+x))<=E d(fun x=>A+B*x).
 + apply in_ler_exp; first 2 by apply hasE_finite.
   move=>x hx /=.
   have hx': -w<=x<=w by move:(hb x hx); rewrite RealOrder.ler_norml.
   pose t:=(w+x)/(2%r*w).
   have ht:0%r<=t<=1%r.
   - clear hc hb hd hl hz.
     rewrite /t; split; first by apply divr_ge0; smt().
     rewrite ler_pdivr_mulr; smt().
   have h:=hc (s+w) (s-w) t ht.
   have he:t*(s+w)+(1%r-t)*(s-w)=s+x by rewrite /t; field; smt().
   have hr:t*f(s+w)+(1%r-t)*f(s-w)=A+B*x by rewrite /t /A /B; field; smt().
   by move:h; rewrite he hr.
 have he:E d(fun x=>A+B*x)=A.
 + rewrite expD; first 2 by apply hasE_finite.
   rewrite expC expZ hl (_:E d(fun x=>x)=E d idfun) 1:// hz; ring.
 by move:hm; rewrite he /A.
qed.
