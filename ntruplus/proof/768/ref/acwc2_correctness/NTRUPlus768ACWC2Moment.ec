require import AllCore Distr Finite List StdBigop StdOrder.
require import NTRUPlus768ACWC2MomentConvex NTRUPlus768NoiseMGF.
import RealOrder RField.

op acwc2_centered_bounded (d:real distr) (w:real) =
 is_finite(support d) /\ is_lossless d /\ E d idfun=0%r /\
 (forall x,x \in d=>`|x|<=w) /\ 0%r<=w.
op acwc2_sum (xs:real list) = Bigreal.BRA.big predT idfun xs.
op acwc2_moment (ds:real distr list) n = E(djoin ds)(fun xs=>(acwc2_sum xs)^n).

lemma acwc2_finite_djoin (ds:real distr list) :
 all (fun d=>is_finite(support d)) ds => is_finite(support(djoin ds)).
proof.
 elim:ds=>[|d ds ih] /=.
 + rewrite djoin_nil; exact(finite_dunit []).
 move=>[hd hds]; rewrite djoin_cons.
 apply noise_finite_dmap; apply finite_dprod=>//.
 exact(ih hds).
qed.

lemma acwc2_step_envelope S w a2 a4 a6 a8 :
 0%r<=S =>a2<=S =>a4<=3%r*S^2 =>a6<=15%r*S^3 =>a8<=105%r*S^4 =>
 a2+w^2<=S+w^2 /\
 a4+6%r*w^2*a2+w^4<=3%r*(S+w^2)^2 /\
 a6+15%r*w^2*a4+15%r*w^4*a2+w^6<=15%r*(S+w^2)^3 /\
 a8+28%r*w^2*a6+70%r*w^4*a4+28%r*w^6*a2+w^8<=105%r*(S+w^2)^4.
proof.
 move=>hS h2 h4 h6 h8.
 have w2:=ge0_sqr w.
 have w4:=acwc2_fourth_nonnegative w.
 have w6:0%r<=w^6.
 + have he:w^6=(w^3)^2 by ring.
   rewrite he; exact(ge0_sqr(w^3)).
 have w8:0%r<=w^8.
 + have he:w^8=(w^4)^2 by ring.
   rewrite he; exact(ge0_sqr(w^4)).
 have S2:=ge0_sqr S.
 have t42:6%r*w^2*a2<=6%r*w^2*S by apply ler_wpmul2l; smt().
 have t64:15%r*w^2*a4<=15%r*w^2*(3%r*S^2) by apply ler_wpmul2l; smt().
 have t62:15%r*w^4*a2<=15%r*w^4*S by apply ler_wpmul2l; smt().
 have t86:28%r*w^2*a6<=28%r*w^2*(15%r*S^3) by apply ler_wpmul2l; smt().
 have t84:70%r*w^4*a4<=70%r*w^4*(3%r*S^2) by apply ler_wpmul2l; smt().
 have t82:28%r*w^6*a2<=28%r*w^6*S by apply ler_wpmul2l; smt().
 have p64:0%r<=S*w^4 by apply mulr_ge0.
 have p84:0%r<=S^2*w^4 by apply mulr_ge0.
 have p86:0%r<=S*w^6 by apply mulr_ge0.
 have e4:3%r*(S+w^2)^2=3%r*S^2+6%r*w^2*S+w^4+2%r*w^4 by ring.
 have e6:15%r*(S+w^2)^3=15%r*S^3+15%r*w^2*(3%r*S^2)+15%r*w^4*S+w^6+
   30%r*(S*w^4)+14%r*w^6 by ring.
 have e8:105%r*(S+w^2)^4=105%r*S^4+28%r*w^2*(15%r*S^3)+70%r*w^4*(3%r*S^2)+28%r*w^6*S+w^8+
   420%r*(S^2*w^4)+392%r*(S*w^6)+104%r*w^8 by ring.
 rewrite e4 e6 e8; smt().
qed.
lemma acwc2_exp_add ['a] (d:'a distr) : is_finite(support d) =>
 forall f g,E d(fun x=>f x+g x)=E d f+E d g.
proof. move=>hd f g; exact(expD d f g (hasE_finite d f hd)(hasE_finite d g hd)). qed.
lemma acwc2_sum_rcons xs x : acwc2_sum(rcons xs x)=acwc2_sum xs+x.
proof. by rewrite /acwc2_sum Bigreal.BRA.big_rcons /predT /idfun /=. qed.

lemma acwc2_centered_shift2 d w s : acwc2_centered_bounded d w =>
 E d(fun x=>(s+x)^2)<=s^2+w^2.
proof.
 move=>[hd [hl [hz [hb hw]]]].
 have h:=acwc2_centered_chord d (fun x:real=>x^2) w s hd hl hz hb hw acwc2_convex_square.
 have he:((s+w)^2+(s-w)^2)/2%r=s^2+w^2 by field.
 by move:h; rewrite /= he.
qed.

lemma acwc2_centered_shift4 d w s : acwc2_centered_bounded d w =>
 E d(fun x=>(s+x)^4)<=s^4+6%r*w^2*s^2+w^4.
proof.
 move=>[hd [hl [hz [hb hw]]]].
 have h:=acwc2_centered_chord d (fun x:real=>x^4) w s hd hl hz hb hw acwc2_convex_fourth.
 have he:((s+w)^4+(s-w)^4)/2%r=s^4+6%r*w^2*s^2+w^4 by field.
 by move:h; rewrite /= he.
qed.

lemma acwc2_centered_shift6 d w s : acwc2_centered_bounded d w =>
 E d(fun x=>(s+x)^6)<=s^6+15%r*w^2*s^4+15%r*w^4*s^2+w^6.
proof.
 move=>[hd [hl [hz [hb hw]]]].
 have h:=acwc2_centered_chord d (fun x:real=>x^6) w s hd hl hz hb hw acwc2_convex_sixth.
 have he:((s+w)^6+(s-w)^6)/2%r=s^6+15%r*w^2*s^4+15%r*w^4*s^2+w^6 by field.
 by move:h; rewrite /= he.
qed.

lemma acwc2_centered_shift8 d w s : acwc2_centered_bounded d w =>
 E d(fun x=>(s+x)^8)<=s^8+28%r*w^2*s^6+70%r*w^4*s^4+28%r*w^6*s^2+w^8.
proof.
 move=>[hd [hl [hz [hb hw]]]].
 have h:=acwc2_centered_chord d (fun x:real=>x^8) w s hd hl hz hb hw acwc2_convex_eighth.
 have he:((s+w)^8+(s-w)^8)/2%r=s^8+28%r*w^2*s^6+70%r*w^4*s^4+28%r*w^6*s^2+w^8 by field.
 by move:h; rewrite /= he.
qed.

lemma acwc2_moment_step2 ds d w :
 all (fun e=>is_finite(support e)) ds => all is_lossless ds =>
 acwc2_centered_bounded d w =>
 acwc2_moment(rcons ds d) 2<=acwc2_moment ds 2+w^2.
proof.
 move=>hfs hls hb.
 have hf:=acwc2_finite_djoin ds hfs.
 have hll:forall e,e \in ds=>is_lossless e by move:hls; rewrite allP.
 have hl:=djoin_ll ds hll.
 have [hd _]:=hb.
 rewrite /acwc2_moment djoin_rcons noise_exp_dmap.
 + exact(finite_dprod _ _ hf hd).
 rewrite (noise_exp_product _ _ _ hf hd).
 have hm:E(djoin ds)(fun xs=>E d(fun x=>(acwc2_sum(rcons xs x))^2))<=
   E(djoin ds)(fun xs=>(acwc2_sum xs)^2+w^2).
 + apply in_ler_exp; first 2 by apply hasE_finite.
   move=>xs _ /=; rewrite (eq_exp _ _ (fun x=>(acwc2_sum xs+x)^2)).
   - by move=>x _; rewrite /= acwc2_sum_rcons.
   exact(acwc2_centered_shift2 d w (acwc2_sum xs) hb).
 have he:E(djoin ds)(fun xs=>(acwc2_sum xs)^2+w^2)=acwc2_moment ds 2+w^2.
 + rewrite !(acwc2_exp_add _ hf) ?expZ expC hl /acwc2_moment; ring.
 by move:hm; rewrite he.
qed.

lemma acwc2_moment_step4 ds d w :
 all (fun e=>is_finite(support e)) ds => all is_lossless ds =>
 acwc2_centered_bounded d w =>
 acwc2_moment(rcons ds d) 4<=acwc2_moment ds 4+6%r*w^2*acwc2_moment ds 2+w^4.
proof.
 move=>hfs hls hb.
 have hf:=acwc2_finite_djoin ds hfs.
 have hll:forall e,e \in ds=>is_lossless e by move:hls; rewrite allP.
 have hl:=djoin_ll ds hll.
 have [hd _]:=hb.
 rewrite /acwc2_moment djoin_rcons noise_exp_dmap.
 + exact(finite_dprod _ _ hf hd).
 rewrite (noise_exp_product _ _ _ hf hd).
 have hm:E(djoin ds)(fun xs=>E d(fun x=>(acwc2_sum(rcons xs x))^4))<=
   E(djoin ds)(fun xs=>(acwc2_sum xs)^4+6%r*w^2*(acwc2_sum xs)^2+w^4).
 + apply in_ler_exp; first 2 by apply hasE_finite.
   move=>xs _ /=; rewrite (eq_exp _ _ (fun x=>(acwc2_sum xs+x)^4)).
   - by move=>x _; rewrite /= acwc2_sum_rcons.
   exact(acwc2_centered_shift4 d w (acwc2_sum xs) hb).
 have he:E(djoin ds)(fun xs=>(acwc2_sum xs)^4+6%r*w^2*(acwc2_sum xs)^2+w^4)=acwc2_moment ds 4+6%r*w^2*acwc2_moment ds 2+w^4.
 + rewrite !(acwc2_exp_add _ hf) ?expZ expC hl /acwc2_moment; ring.
 by move:hm; rewrite he.
qed.

lemma acwc2_moment_step6 ds d w :
 all (fun e=>is_finite(support e)) ds => all is_lossless ds =>
 acwc2_centered_bounded d w =>
 acwc2_moment(rcons ds d) 6<=acwc2_moment ds 6+15%r*w^2*acwc2_moment ds 4+15%r*w^4*acwc2_moment ds 2+w^6.
proof.
 move=>hfs hls hb.
 have hf:=acwc2_finite_djoin ds hfs.
 have hll:forall e,e \in ds=>is_lossless e by move:hls; rewrite allP.
 have hl:=djoin_ll ds hll.
 have [hd _]:=hb.
 rewrite /acwc2_moment djoin_rcons noise_exp_dmap.
 + exact(finite_dprod _ _ hf hd).
 rewrite (noise_exp_product _ _ _ hf hd).
 have hm:E(djoin ds)(fun xs=>E d(fun x=>(acwc2_sum(rcons xs x))^6))<=
   E(djoin ds)(fun xs=>(acwc2_sum xs)^6+15%r*w^2*(acwc2_sum xs)^4+15%r*w^4*(acwc2_sum xs)^2+w^6).
 + apply in_ler_exp; first 2 by apply hasE_finite.
   move=>xs _ /=; rewrite (eq_exp _ _ (fun x=>(acwc2_sum xs+x)^6)).
   - by move=>x _; rewrite /= acwc2_sum_rcons.
   exact(acwc2_centered_shift6 d w (acwc2_sum xs) hb).
 have he:E(djoin ds)(fun xs=>(acwc2_sum xs)^6+15%r*w^2*(acwc2_sum xs)^4+15%r*w^4*(acwc2_sum xs)^2+w^6)=acwc2_moment ds 6+15%r*w^2*acwc2_moment ds 4+15%r*w^4*acwc2_moment ds 2+w^6.
 + rewrite !(acwc2_exp_add _ hf) ?expZ expC hl /acwc2_moment; ring.
 by move:hm; rewrite he.
qed.

lemma acwc2_moment_step8 ds d w :
 all (fun e=>is_finite(support e)) ds => all is_lossless ds =>
 acwc2_centered_bounded d w =>
 acwc2_moment(rcons ds d) 8<=acwc2_moment ds 8+28%r*w^2*acwc2_moment ds 6+70%r*w^4*acwc2_moment ds 4+28%r*w^6*acwc2_moment ds 2+w^8.
proof.
 move=>hfs hls hb.
 have hf:=acwc2_finite_djoin ds hfs.
 have hll:forall e,e \in ds=>is_lossless e by move:hls; rewrite allP.
 have hl:=djoin_ll ds hll.
 have [hd _]:=hb.
 rewrite /acwc2_moment djoin_rcons noise_exp_dmap.
 + exact(finite_dprod _ _ hf hd).
 rewrite (noise_exp_product _ _ _ hf hd).
 have hm:E(djoin ds)(fun xs=>E d(fun x=>(acwc2_sum(rcons xs x))^8))<=
   E(djoin ds)(fun xs=>(acwc2_sum xs)^8+28%r*w^2*(acwc2_sum xs)^6+70%r*w^4*(acwc2_sum xs)^4+28%r*w^6*(acwc2_sum xs)^2+w^8).
 + apply in_ler_exp; first 2 by apply hasE_finite.
   move=>xs _ /=; rewrite (eq_exp _ _ (fun x=>(acwc2_sum xs+x)^8)).
   - by move=>x _; rewrite /= acwc2_sum_rcons.
   exact(acwc2_centered_shift8 d w (acwc2_sum xs) hb).
 have he:E(djoin ds)(fun xs=>(acwc2_sum xs)^8+28%r*w^2*(acwc2_sum xs)^6+70%r*w^4*(acwc2_sum xs)^4+28%r*w^6*(acwc2_sum xs)^2+w^8)=acwc2_moment ds 8+28%r*w^2*acwc2_moment ds 6+70%r*w^4*acwc2_moment ds 4+28%r*w^6*acwc2_moment ds 2+w^8.
 + rewrite !(acwc2_exp_add _ hf) ?expZ expC hl /acwc2_moment; ring.
 by move:hm; rewrite he.
qed.

op acwc2_variance ['i] (rs:'i list) (w:'i->real) =
 Bigreal.BRA.big predT (fun i=>(w i)^2) rs.
lemma acwc2_variance_nonnegative ['i] (rs:'i list) w : 0%r<=acwc2_variance rs w.
proof.
 elim:rs=>[|i rs ih]; first by rewrite /acwc2_variance Bigreal.BRA.big_nil.
 rewrite /acwc2_variance Bigreal.BRA.big_consT -/acwc2_variance.
 apply addr_ge0.
 + exact(ge0_sqr(w i)).
 exact ih.
qed.

lemma acwc2_independent_even_moments ['i] (rs:'i list) (w:'i->real) (d:'i->real distr) :
 (forall i,i \in rs=>acwc2_centered_bounded(d i)(w i)) =>
 acwc2_moment(map d rs) 2<=acwc2_variance rs w /\
 acwc2_moment(map d rs) 4<=3%r*(acwc2_variance rs w)^2 /\
 acwc2_moment(map d rs) 6<=15%r*(acwc2_variance rs w)^3 /\
 acwc2_moment(map d rs) 8<=105%r*(acwc2_variance rs w)^4.
proof.
 elim/last_ind:rs=>[|rs i ih].
 + by move=>_; rewrite /= /acwc2_moment /acwc2_variance djoin_nil !exp_dunit /= /acwc2_sum
     !Bigreal.BRA.big_nil !expr0z /=.
 move=>h.
 have hsub:forall j,j \in rs=>acwc2_centered_bounded(d j)(w j).
 + move=>j hj; apply h; rewrite mem_rcons; smt().
 have hi:acwc2_centered_bounded(d i)(w i).
 + apply h; rewrite mem_rcons; smt().
 have [h2 [h4 [h6 h8]]]:=ih hsub.
 have hf:all (fun e=>is_finite(support e))(map d rs).
 + rewrite all_map allP=>j hj /=; have [hd _]:=hsub j hj; exact hd.
 have hl:all is_lossless(map d rs).
 + rewrite all_map allP=>j hj /=; have [_ [hd _]]:=hsub j hj; exact hd.
 have e2:=acwc2_moment_step2 (map d rs) (d i) (w i) hf hl hi.
 have e4:=acwc2_moment_step4 (map d rs) (d i) (w i) hf hl hi.
 have e6:=acwc2_moment_step6 (map d rs) (d i) (w i) hf hl hi.
 have e8:=acwc2_moment_step8 (map d rs) (d i) (w i) hf hl hi.
 have [b2 [b4 [b6 b8]]]:=acwc2_step_envelope (acwc2_variance rs w) (w i)
   (acwc2_moment(map d rs)2) (acwc2_moment(map d rs)4)
   (acwc2_moment(map d rs)6) (acwc2_moment(map d rs)8)
   (acwc2_variance_nonnegative rs w) h2 h4 h6 h8.
 rewrite map_rcons /acwc2_variance Bigreal.BRA.big_rcons /predT /= -/acwc2_variance.
 split; first exact(ler_trans _ _ _ e2 b2).
 split; first exact(ler_trans _ _ _ e4 b4).
 split; first exact(ler_trans _ _ _ e6 b6).
 exact(ler_trans _ _ _ e8 b8).
qed.

lemma acwc2_independent_eighth ['i] (rs:'i list) (w:'i->real) (d:'i->real distr) :
 (forall i,i \in rs=>acwc2_centered_bounded(d i)(w i)) =>
 E(djoin(map d rs))(fun xs=>(acwc2_sum xs)^8)<=
 105%r*(Bigreal.BRA.big predT(fun i=>(w i)^2)rs)^4.
proof.
 move=>h; have [_ [_ [_ h8]]]:=acwc2_independent_even_moments rs w d h.
 exact h8.
qed.
