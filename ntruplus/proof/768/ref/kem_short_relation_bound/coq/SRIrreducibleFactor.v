From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Definition sri_map2 (p : {poly int}) : {poly bool} :=
  map_poly (intr : int -> bool) p.
Definition sri_mapQ (p : {poly int}) : {poly rat} :=
  map_poly (intr : int -> rat) p.
Definition sri_lift2 (p : {poly bool}) : {poly int} :=
  map_poly (fun b => if b then 1 else 0) p.

Lemma sri_nat_bool n : (n%:R : bool) = odd n.
Proof. by elim: n => [|n IH] //; rewrite -natr1 oddS IH; case: (odd n). Qed.
Lemma sri_int_bool_even (z:int) : ((z%:~R : bool) == 0) = (2 %| z)%Z.
Proof.
case: z => n; rewrite dvdzE dvdn2.
- change (((n%:R : bool) == false) = ~~ odd n).
  by rewrite sri_nat_bool;case: (odd n).
- change (((- n.+1%:R : bool) == false) = ~~ odd n.+1).
  by rewrite sri_nat_bool;case: (odd n.+1).
Qed.
Lemma sri_map2_lift p : sri_map2 (sri_lift2 p) = p.
Proof.
apply/polyP=>i;rewrite /sri_map2 /sri_lift2 coef_map coef_map_id0 //.
by case: (p`_i).
Qed.
Lemma sri_map2_zero p : sri_map2 p = 0 -> exists r, p = (2:int) *: r.
Proof.
move=>hp;apply/polyOver_dvdzP/polyOverP=>i.
rewrite -sri_int_bool_even;apply/eqP.
by move/polyP/(_ i):hp;rewrite /sri_map2 coef_map coef0.
Qed.
Lemma sri_map2_divlift g p : sri_map2 g %| sri_map2 p ->
  exists q r, p = g*q+(2:int)*:r.
Proof.
move/dvdpP=>[q hq].
have hz:sri_map2 (p-g*sri_lift2 q)=0.
  rewrite /sri_map2 rmorphB rmorphM.
  change (sri_map2 p - sri_map2 g * sri_map2 (sri_lift2 q) = 0).
  rewrite sri_map2_lift hq.
  by rewrite mulrC subrr.
case:(sri_map2_zero hz)=>r hr.
exists (sri_lift2 q),r;by rewrite -hr addrC subrK.
Qed.
Lemma sri_irred_power_divisor (K:fieldType) (g p:{poly K}) m :
  irreducible_poly g -> size p != 1%N -> p %| g^+m -> g %| p.
Proof.
move=>hg hp hdiv;apply/negPn/negP=>hnd.
have hc:coprimep g p by rewrite irreducible_poly_coprime //.
have hc':coprimep p (g^+m) by apply:coprimep_expr;rewrite coprimep_sym.
have :coprimep p p by exact:(coprimep_dvdl hdiv hc').
by rewrite coprimepp (negPf hp).
Qed.

Lemma sri_map2_unit_size (p:{poly int}) :
  lead_coef p \is a GRing.unit -> size (sri_map2 p) = size p.
Proof.
move=>hp;apply:size_map_poly_id0;rewrite -unitfE.
exact:rmorph_unit.
Qed.
Lemma sri_product_ideal4 (g a b:{poly int}) :
 sri_map2 g %| sri_map2 a -> sri_map2 g %| sri_map2 b ->
 exists q r, a*b = g*q+(4:int)*:r.
Proof.
move=>ha hb.
case:(sri_map2_divlift ha)=>q [r ->].
case:(sri_map2_divlift hb)=>s [t ->].
exists (q*(g*s+2*:t)+(2*:r)*s),(r*t).
rewrite !mulrDl !mulrDr.
rewrite -!scalerAr -!scalerAl !scalerA.
rewrite !mulrA.
by rewrite -scalerAr !mulrA [r*g]mulrC addrA.
Qed.
Theorem sri_schoenemann (f g:{poly int}) (m:nat) :
 (1<size f)%N -> f \is monic ->
 irreducible_poly (sri_map2 g) ->
 sri_map2 f=(sri_map2 g)^+m ->
 (forall q r:{poly int}, f<>g*q+(4:int)*:r) ->
 irreducible_poly (sri_mapQ f).
Proof.
move=>hfsize hfmon hg hpower hnot;split.
  by rewrite /sri_mapQ size_rat_int_poly.
move=>p hp hpdiv.
case:(dvdpP_rat_int hpdiv)=>a [c hc hpc] [b hfab].
have hunit: (lead_coef a \is a GRing.unit) && (lead_coef b \is a GRing.unit).
  by rewrite -unitrM -lead_coefM -hfab (monicP hfmon) unitr1.
case/andP:hunit=>hau hbu.
have ha0:a!=0 by apply: contraTneq hau=>->;rewrite lead_coef0 unitr0.
have hb0:b!=0 by apply: contraTneq hbu=>->;rewrite lead_coef0 unitr0.
have hps:size p=size a by rewrite hpc size_scale // size_rat_int_poly.
have has:size a!=1%N by rewrite -hps.
have [hbs|hbs]:=eqVneq (size b) 1%N.
  rewrite -(dvdp_size_eqp hpdiv);apply/eqP.
  by rewrite /sri_mapQ size_rat_int_poly hfab size_mul // hbs addn1 /= hps.
have hamb:sri_map2 a*sri_map2 b=(sri_map2 g)^+m.
  by rewrite -hpower hfab /sri_map2 rmorphM.
have hga:sri_map2 g %| sri_map2 a.
  apply:(@sri_irred_power_divisor [fieldType of bool] (sri_map2 g) (sri_map2 a) m hg);first by rewrite sri_map2_unit_size.
  rewrite -hamb;exact:dvdp_mulr.
have hgb:sri_map2 g %| sri_map2 b.
  apply:(@sri_irred_power_divisor [fieldType of bool] (sri_map2 g) (sri_map2 b) m hg);first by rewrite sri_map2_unit_size.
  rewrite -hamb;exact:dvdp_mull.
case:(sri_product_ideal4 hga hgb)=>q [r hab].
by exfalso;apply:(hnot q r);rewrite hfab hab.
Qed.

Print Assumptions sri_schoenemann.
