require import AllCore Distr Finite List StdBigop StdOrder.
require import NTRUPlus768CBDDistribution.
import RealOrder RField.

op noise_mgf_base = 1237%r/1024%r.
op noise_sum (xs:int list) = Bigint.BIA.big predT idfun xs.
op noise_mgf (s:int) (d:int distr) = E d (fun x=>2%r^(s*x)).

lemma noise_finite_dmap ['a 'b] (d:'a distr) (f:'a -> 'b) :
 is_finite(support d) => is_finite(support(dmap d f)).
proof.
 move=>hd; rewrite /dmap; apply finite_dlet=> // x hx.
 exact (finite_dunit(f x)).
qed.

lemma noise_finite_djoin (ds:int distr list) :
 all (fun d=>is_finite(support d)) ds => is_finite(support(djoin ds)).
proof.
 elim:ds=>[|d ds ih] /=.
 + rewrite djoin_nil; exact (finite_dunit []).
 move=>[hd hds]; rewrite djoin_cons.
 apply noise_finite_dmap; apply finite_dprod=> //.
 exact (ih hds).
qed.

lemma noise_exp_dmap ['a 'b] (d:'a distr) (f:'a -> 'b) g :
 is_finite(support d) => E (dmap d f) g=E d (fun x=>g(f x)).
proof.
 move=>hd; rewrite exp_dmap //.
 apply hasE_finite; exact(noise_finite_dmap d f hd).
qed.

lemma noise_exp_dlet ['a 'b] (d:'a distr) (df:'a -> 'b distr) g :
 is_finite(support d) =>
 (forall x,x \in d=>is_finite(support(df x))) =>
 E (dlet d df) g=E d (fun x=>E(df x)g).
proof.
 move=>hd hf; apply exp_dlet; apply hasE_finite.
 exact(finite_dlet d df hd hf).
qed.

lemma noise_exp_dprod ['a 'b] (da:'a distr) (db:'b distr)
 (f:'a -> real) (g:'b -> real) :
 is_finite(support da) => is_finite(support db) =>
 E (da `*` db) (fun (z:'a * 'b)=>f z.`1*g z.`2)=E da f*E db g.
proof.
 move=>ha hb.
 have hinner:forall a, E (dlet db (fun b=>dunit(a,b))) (fun (z:'a * 'b)=>f z.`1*g z.`2)=
   f a*E db g.
 + move=>a; rewrite noise_exp_dlet 1:hb.
   - move=>b _; exact(finite_dunit(a,b)).
   rewrite (eq_exp _ _ (fun b=>f a*g b)); first by move=>b _ /=; rewrite exp_dunit.
   exact (expZ db (f a) g).
 rewrite dprod_dlet noise_exp_dlet 1:ha.
 + move=>a _; apply finite_dlet=> // b _; exact(finite_dunit(a,b)).
 rewrite (eq_exp _ _ (fun a=>E db g*f a)).
 + move=>a _ /=; rewrite hinner; ring.
 rewrite expZ; ring.
qed.

lemma noise_sum_nil : noise_sum []=0.
proof. by rewrite /noise_sum Bigint.BIA.big_nil. qed.
lemma noise_sum_cons x xs : noise_sum(x::xs)=x+noise_sum xs.
proof. by rewrite /noise_sum Bigint.BIA.big_consT. qed.
lemma noise_sumE xs : noise_sum xs=sumz xs.
proof. by rewrite /noise_sum Bigint.sumzE /idfun. qed.
lemma noise_negate (x:int) : (-1)*x= -x.
proof. smt(). qed.
lemma noise_exp_negate ['a] (d:'a distr) (f:'a -> int) :
 E d (fun x=>2%r^((-1)*f x))=E d (fun x=>2%r^(-f x)).
proof. apply eq_exp=>x _ /=; congr; smt(). qed.
lemma noise_power_add s x y : 2%r^(s*(x+y))=2%r^(s*x)*2%r^(s*y).
proof.
 have ->:s*(x+y)=s*x+s*y by ring.
 by rewrite exprD // unitfE.
qed.

lemma noise_exp_product ['a 'b] (da:'a distr) (db:'b distr) (f:'a * 'b -> real) :
 is_finite(support da) => is_finite(support db) =>
 E (da `*` db) f=E da (fun a=>E db(fun b=>f(a,b))).
proof.
 move=>ha hb; rewrite dprod_dlet noise_exp_dlet 1:ha.
 + move=>a _; apply finite_dlet=> // b _; exact(finite_dunit(a,b)).
 apply eq_exp=>a _ /=; rewrite noise_exp_dlet 1:hb.
 + move=>b _; exact(finite_dunit(a,b)).
 apply eq_exp=>b _ /=; by rewrite exp_dunit.
qed.

lemma noise_dcbd_expect (f:int -> real) :
 E dcbd f=(f(-1)+2%r*f 0+f 1)/4%r.
proof.
 rewrite /dcbd noise_exp_dmap.
 + exact(finite_duniform [0;1;2;3]).
 rewrite exp_duniform /= !Bigreal.BRA.big_consT Bigreal.BRA.big_nil /=.
 ring.
qed.

lemma noise_quad_expect (f:cbd_quad -> real) :
 E dcbd_quad f=E dcbd(fun a=>E dcbd(fun c=>E dcbd(fun b=>E dcbd(fun d=>f((a,c),(b,d)))))).
proof.
 have hf:=finite_dprod dcbd dcbd dcbd_finite dcbd_finite.
 rewrite /dcbd_quad (noise_exp_product _ _ _ hf hf).
 rewrite (noise_exp_product dcbd dcbd _ dcbd_finite dcbd_finite).
 apply eq_exp=>a _ /=; apply eq_exp=>c _ /=.
 exact(noise_exp_product dcbd dcbd _ dcbd_finite dcbd_finite).
qed.

op noise_kind_value (kind:int) (z:cbd_quad) : int =
 if kind=0 then z.`1.`1*z.`2.`1-z.`1.`2*z.`2.`2
 else if kind=1 then -(z.`1.`1*z.`2.`2+z.`1.`2*z.`2.`1+z.`1.`2*z.`2.`2)
 else if kind=2 then z.`1.`1*z.`2.`2+z.`1.`2*z.`2.`1+z.`1.`2*z.`2.`2
 else z.`1.`1*z.`2.`1+z.`1.`1*z.`2.`2+z.`1.`2*z.`2.`1.
op noise_kind_distr kind = dmap dcbd_quad (noise_kind_value kind).

lemma noise_kind_finite kind : is_finite(support(noise_kind_distr kind)).
proof. rewrite /noise_kind_distr; exact(noise_finite_dmap _ _ dcbd_quad_finite). qed.
lemma noise_kind_lossless kind : is_lossless(noise_kind_distr kind).
proof. rewrite /noise_kind_distr; apply dmap_ll; exact dcbd_quad_ll. qed.

lemma noise_kind_mgf_exact kind s : s=1 \/ s= -1 =>
 noise_mgf s (noise_kind_distr kind)=
   (if kind=0 then 289%r/256%r else 1237%r/1024%r).
proof.
 move=>hs.
 have p2:2%r^2=4%r by ring.
 have p3:2%r^3=8%r by ring.
 have m1:2%r^(-1)=1%r/2%r.
 + rewrite (exprN 2%r 1) expr1; field; smt().
 have m2:2%r^(-2)=1%r/4%r.
 + rewrite (exprN 2%r 2) p2; field; smt().
 have m3:2%r^(-3)=1%r/8%r.
 + rewrite (exprN 2%r 3) p3; field; smt().
 rewrite /noise_mgf /noise_kind_distr noise_exp_dmap 1:dcbd_quad_finite.
 rewrite noise_quad_expect.
 do 4!(rewrite !noise_dcbd_expect /=).
 case(kind=0)=>h0; case(kind=1)=>h1; case(kind=2)=>h2;
  case hs=>->; rewrite /noise_kind_value /= ?h0 ?h1 ?h2 /=
    ?m1 ?m2 ?m3 ?p2 ?p3 ?expr0 ?expr1; field; smt().
qed.

lemma noise_kind_mgf_bound kind :
 noise_mgf 1 (noise_kind_distr kind)<=noise_mgf_base /\
 noise_mgf (-1) (noise_kind_distr kind)<=noise_mgf_base.
proof.
 rewrite !noise_kind_mgf_exact ~-1:/# /noise_mgf_base.
 case(kind=0); smt().
qed.
lemma noise_mgf_nonnegative s d : 0%r<=noise_mgf s d.
proof. rewrite /noise_mgf; apply exp_ge0=>x _; apply expr_ge0; smt(). qed.

lemma independent_noise_mgf_product ds s :
 all (fun d=>is_finite(support d)) ds =>
 E (djoin ds) (fun xs=>2%r^(s*noise_sum xs))=
 Bigreal.BRM.big predT (noise_mgf s) ds.
proof.
 elim:ds=>[|d ds ih] /=.
 + rewrite djoin_nil exp_dunit /= noise_sum_nil /= Bigreal.BRM.big_nil.
   smt(expr0).
 move=>[hd hds]; rewrite djoin_cons noise_exp_dmap.
 + apply finite_dprod=> //; exact(noise_finite_djoin ds hds).
 rewrite (eq_exp _ _ (fun (z:int * int list)=>2%r^(s*z.`1)*2%r^(s*noise_sum z.`2))).
 + move=>[x xs] _ /=; by rewrite noise_sum_cons noise_power_add.
 rewrite (noise_exp_dprod d (djoin ds) (fun x=>2%r^(s*x))
   (fun xs=>2%r^(s*noise_sum xs)) hd (noise_finite_djoin ds hds)).
 rewrite (ih hds) Bigreal.BRM.big_consT /noise_mgf.
 done.
qed.

lemma independent_noise_mgf_bound ds s K :
 0%r<=K =>
 all (fun d=>is_finite(support d)) ds =>
 (forall d,d \in ds=>noise_mgf s d<=K) =>
 E (djoin ds) (fun xs=>2%r^(s*noise_sum xs))<=K^(size ds).
proof.
 move=>hK hfinite hbound; rewrite independent_noise_mgf_product //.
 elim:ds hfinite hbound=>[|d ds ih] /=.
 + by rewrite Bigreal.BRM.big_nil expr0.
 move=>[hd hds] hb; rewrite Bigreal.BRM.big_consT.
 rewrite (_:1+size ds=size ds+1) 1:/# exprS 1:size_ge0.
 have hd0:=noise_mgf_nonnegative s d.
 have hdl:=hb d _; first smt().
 have htail:=ih hds _; first by move=>e he; apply hb; smt().
 have htail0:0%r<=Bigreal.BRM.big predT (noise_mgf s) ds.
 + rewrite -(independent_noise_mgf_product ds s hds).
   apply exp_ge0=>xs _; apply expr_ge0; smt().
 apply ler_pmul; smt().
qed.
