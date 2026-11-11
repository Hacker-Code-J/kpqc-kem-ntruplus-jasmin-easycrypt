require import AllCore Distr Finite List StdBigop StdOrder.
import RealOrder RField.

op acwc2_finite_max ['m] (ms:'m list) (f:'m->real) =
 foldr (fun m v=>maxr (f m) v) 0%r ms.
op acwc2_message_bad ['m 'a] (ms:'m list) (f:'m->'a->real) c eps x =
 has (fun m=>eps<=f m x-c) ms.

lemma acwc2_eighth_nonnegative (x:real) : 0%r<=x^8.
proof.
 have he:x^8=(x^4)^2 by ring.
 rewrite he; exact(ge0_sqr(x^4)).
qed.

lemma acwc2_eighth_markov ['a] (d:'a distr) (f:'a->real) eps :
 is_finite(support d) =>0%r<eps =>
 mu d(fun x=>eps<=f x)<=E d(fun x=>(f x)^8)/(eps^8).
proof.
 move=>hd heps.
 have hp:0%r<eps^8 by apply expr_gt0.
 have h:E d(fun x=>if eps<=f x then eps^8 else 0%r)<=E d(fun x=>(f x)^8).
 + apply in_ler_exp; first 2 by apply hasE_finite.
   move=>x _ /=; case(eps<=f x)=>hx /=.
   - apply ler_pexp; smt().
   exact(acwc2_eighth_nonnegative(f x)).
 rewrite expC_cond in h.
 rewrite ler_pdivl_mulr 1:hp; smt().
qed.

lemma acwc2_max_upper ['m] (ms:'m list) f c :
 0%r<=c => (forall m,m \in ms=>f m<=c) =>acwc2_finite_max ms f<=c.
proof.
 move=>hc; elim:ms=>[|m ms ih] /=.
 + by rewrite /acwc2_finite_max /=.
 move=>hf; have hm:=hf m _; first by smt().
 have ht:=ih _; first by move=>a ha; apply hf; smt().
 rewrite /acwc2_finite_max /= -/acwc2_finite_max; smt(RealOrder.ler_maxl).
qed.
lemma acwc2_max_nonnegative ['m] (ms:'m list) f : 0%r<=acwc2_finite_max ms f.
proof.
 elim:ms=>[|m ms ih]; first by rewrite /acwc2_finite_max /=.
 rewrite /acwc2_finite_max /= -/acwc2_finite_max.
 have h:=RealOrder.maxrr (f m) (acwc2_finite_max ms f); smt().
qed.

lemma acwc2_message_union ['m 'a] (d:'a distr) (ms:'m list) (events:'m->'a->bool) B :
 0%r<=B => (forall m,m \in ms=>mu d(events m)<=B) =>
 mu d(fun x=>has(fun m=>events m x)ms)<=(size ms)%r*B.
proof.
 move=>hB; elim:ms=>[|m ms ih] /=.
 + rewrite mu0; smt().
 move=>hm.
 have hh:=hm m _; first by smt().
 have ht:=ih _; first by move=>a ha; apply hm; smt().
 have he:mu d(fun x=>events m x \/ has(fun a=>events a x)ms)=
   mu d(predU (events m)(fun x=>has(fun a=>events a x)ms)) by apply mu_eq=>x; rewrite /predU.
 rewrite he mu_or.
 have hi:=ge0_mu d(predI (events m)(fun x=>has(fun a=>events a x)ms)).
 clear he hm ih; rewrite fromintD /=.
 move:hh ht hi.
 move:(mu d(events m)) (mu d(fun x=>has(fun a=>events a x)ms))
   (mu d(predI (events m)(fun x=>has(fun a=>events a x)ms)))=>a b c.
 smt().
qed.

lemma acwc2_finite_max_concentration ['m 'a]
 (d:'a distr) (ms:'m list) (f:'m->'a->real) c eps K :
 is_finite(support d) =>is_lossless d =>0%r<=c =>0%r<eps =>0%r<=K =>
 (forall m x,m \in ms=>x \in d=>0%r<=f m x<=1%r) =>
 (forall m,m \in ms=>E d(fun x=>(f m x-c)^8)<=K) =>
 E d(fun x=>acwc2_finite_max ms(fun m=>f m x))<=
 c+eps+(size ms)%r*K/(eps^8).
proof.
 move=>hd hl hc heps hK hf hm.
 have hep:0%r<eps^8 by apply expr_gt0.
 have hfrac:0%r<=K/(eps^8) by apply divr_ge0; smt().
 have htail:mu d(acwc2_message_bad ms f c eps)<=(size ms)%r*(K/(eps^8)).
 + rewrite /acwc2_message_bad; apply acwc2_message_union; first exact hfrac.
   move=>m hmem.
   have hmark:=acwc2_eighth_markov d (fun x=>f m x-c) eps hd heps.
   have hmoment:=hm m hmem.
   have hdiv:E d(fun x=>(f m x-c)^8)/(eps^8)<=K/(eps^8).
   - apply ler_wpmul2r; first by apply invr_ge0; smt().
     exact hmoment.
   smt().
 have hpoint:forall x,x \in d=>acwc2_finite_max ms(fun m=>f m x)<=
   c+eps+(if acwc2_message_bad ms f c eps x then 1%r else 0%r).
 + move=>x hx; case(acwc2_message_bad ms f c eps x)=>hb /=.
   - have hmax:acwc2_finite_max ms(fun m=>f m x)<=1%r.
     + apply acwc2_max_upper; first smt().
       move=>m hmem; have hh:=hf m x hmem hx; smt().
     smt().
   have hmax:acwc2_finite_max ms(fun m=>f m x)<=c+eps.
   - apply acwc2_max_upper; first smt().
     move=>m hmem.
     have hh:!(eps<=f m x-c).
     + move:hb; rewrite /acwc2_message_bad hasP; smt().
     smt().
   smt().
 have he:E d(fun x=>acwc2_finite_max ms(fun m=>f m x))<=
   E d(fun x=>c+eps+(if acwc2_message_bad ms f c eps x then 1%r else 0%r)).
 + apply in_ler_exp; first 2 by apply hasE_finite.
   exact hpoint.
 rewrite expD in he; first 2 by apply hasE_finite.
 rewrite expC expC_cond hl /= in he.
 have heq:(size ms)%r*K/(eps^8)=(size ms)%r*(K/(eps^8)) by ring.
 rewrite heq.
 apply(ler_trans _ _ _ he).
 by rewrite ler_add2l.

qed.

(* This outer lifting preserves E_key E_G max_message. No interchange of
   maximum and expectation, or independence between messages, is used. *)
lemma acwc2_expected_max_concentration ['k 'm 'a]
 (dk:'k distr) (g:'k->'a distr) (ms:'m list)
 (f:'k->'m->'a->real) (c:'k->real) eps K :
 is_finite(support dk) =>is_lossless dk =>0%r<eps =>0%r<=K =>
 (forall k,k \in dk=>is_finite(support(g k)) /\ is_lossless(g k) /\ 0%r<=c k) =>
 (forall k m x,k \in dk=>m \in ms=>x \in g k=>0%r<=f k m x<=1%r) =>
 (forall k m,k \in dk=>m \in ms=>E(g k)(fun x=>(f k m x-c k)^8)<=K) =>
 E dk(fun k=>E(g k)(fun x=>acwc2_finite_max ms(fun m=>f k m x)))<=
 E dk c+eps+(size ms)%r*K/(eps^8).
proof.
 move=>hdk hll heps hK hg hf hm.
 have hb:E dk(fun k=>E(g k)(fun x=>acwc2_finite_max ms(fun m=>f k m x)))<=
   E dk(fun k=>c k+eps+(size ms)%r*K/(eps^8)).
 + apply in_ler_exp; first 2 by apply hasE_finite.
   move=>k hk /=; have [hgf [hgl hc]]:=hg k hk.
   apply acwc2_finite_max_concentration=>//.
   - move=>m x hm0 hx; exact(hf k m x hk hm0 hx).
   - move=>m hm0; exact(hm k m hk hm0).
 have he:E dk(fun k=>c k+eps+(size ms)%r*K/(eps^8))=
   E dk c+eps+(size ms)%r*K/(eps^8).
 + rewrite expD; first 2 by apply hasE_finite.
   rewrite expD; first 2 by apply hasE_finite.
   rewrite !expC hll; ring.
 by move:hb; rewrite he.
qed.
