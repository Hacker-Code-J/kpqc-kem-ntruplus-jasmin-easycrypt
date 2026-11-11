require import AllCore FMap Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array129 Array192 Array224 Array1152 Array1153.
require import NTRUPlus768ROMDistributions NTRUPlus768ROMDomains.

(* Observable classical lazy sampling: repeat queries draw no new coins.
   Honest callers receive only init/get and raw shake adapters, not table
   programming or removal procedures. The four tables are separate globals. *)
op cache_extends ['a 'b] (old new : ('a,'b) fmap) : bool =
  forall x y, old.[x] = Some y => new.[x] = Some y.
lemma cache_extends_refl ['a 'b] (m : ('a,'b) fmap) : cache_extends m m.
proof. by rewrite /cache_extends. qed.
lemma cache_extends_trans ['a 'b] (m1 m2 m3 : ('a,'b) fmap) :
  cache_extends m1 m2 => cache_extends m2 m3 => cache_extends m1 m3.
proof. by rewrite /cache_extends; smt(). qed.
lemma cache_extends_fresh ['a 'b] (m : ('a,'b) fmap) x y :
  x \notin m => cache_extends m m.[x <- y].
proof.
  move=> hx; rewrite /cache_extends=> z v hz.
  rewrite get_setE; case (z=x)=> hzx; last done.
  by move: hx; rewrite domE -hzx hz /=.
qed.

module type ROEPort = {
  proc init() : unit
  proc get(input : W8.t Array32.t) : W8.t Array192.t
}.
module ROE : ROEPort = {
  var m : (W8.t Array32.t,W8.t Array192.t) fmap
  proc init() = { m <- empty; }
  proc get(input : W8.t Array32.t) : W8.t Array192.t = {
    var r;
    if (input \notin m) {
      r <$ uniform192;
      m.[input] <- r;
    }
    return oget m.[input];
  }
}.
lemma roe_init_empty : hoare [ROE.init : true ==> ROE.m = empty].
proof. by proc; auto. qed.
lemma roe_init_ll : islossless ROE.init.
proof. by proc; auto. qed.
lemma roe_get_ll : islossless ROE.get.
proof. proc; if; auto=> /> &hr _; exact uniform192_ll. qed.
lemma roe_get_value m0 x0 : hoare [ROE.get :
  ROE.m=m0 /\ input=x0 ==> ROE.m.[x0]=Some res /\ cache_extends m0 ROE.m].
proof.
  proc; if.
  + auto=> /> hx r hr; rewrite get_set_sameE /=.
    exact (cache_extends_fresh m0 x0 r hx).
  auto=> />.
  move=> hx; apply some_oget; move: hx; by rewrite domE.
qed.
lemma roe_get_cached m0 x0 y0 : hoare [ROE.get :
  ROE.m=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==> res=y0 /\ ROE.m=m0].
proof. proc; if; auto=> />; smt(domE). qed.
lemma roe_get_preserves x0 y0 : hoare [ROE.get :
  ROE.m.[x0]=Some y0 ==> ROE.m.[x0]=Some y0].
proof.
  proc; if; auto=> /> &hr hcache hfresh r hsample.
  have hext := cache_extends_fresh ROE.m{hr} input{hr} r hfresh.
  move: hext; rewrite /cache_extends=> hext.
  exact (hext x0 y0 hcache).
qed.
lemma roe_get_fresh m0 x0 y0 : phoare [ROE.get :
  ROE.m=m0 /\ input=x0 /\ x0 \notin m0 ==> res=y0] = (mu1 uniform192 y0).
proof.
  proc; rcondt 1; first by auto.
  wp; rnd (pred1 y0); skip; auto=> />.
  move=> hx v hv; by rewrite get_set_sameE /=.
qed.

module type ROFPort = {
  proc init() : unit
  proc get(input : W8.t Array1152.t) : W8.t Array32.t
}.
module ROF : ROFPort = {
  var m : (W8.t Array1152.t,W8.t Array32.t) fmap
  proc init() = { m <- empty; }
  proc get(input : W8.t Array1152.t) : W8.t Array32.t = {
    var r;
    if (input \notin m) {
      r <$ uniform32;
      m.[input] <- r;
    }
    return oget m.[input];
  }
}.
lemma rof_init_empty : hoare [ROF.init : true ==> ROF.m = empty].
proof. by proc; auto. qed.
lemma rof_init_ll : islossless ROF.init.
proof. by proc; auto. qed.
lemma rof_get_ll : islossless ROF.get.
proof. proc; if; auto=> /> &hr _; exact uniform32_ll. qed.
lemma rof_get_value m0 x0 : hoare [ROF.get :
  ROF.m=m0 /\ input=x0 ==> ROF.m.[x0]=Some res /\ cache_extends m0 ROF.m].
proof.
  proc; if.
  + auto=> /> hx r hr; rewrite get_set_sameE /=.
    exact (cache_extends_fresh m0 x0 r hx).
  auto=> />.
  move=> hx; apply some_oget; move: hx; by rewrite domE.
qed.
lemma rof_get_cached m0 x0 y0 : hoare [ROF.get :
  ROF.m=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==> res=y0 /\ ROF.m=m0].
proof. proc; if; auto=> />; smt(domE). qed.
lemma rof_get_preserves x0 y0 : hoare [ROF.get :
  ROF.m.[x0]=Some y0 ==> ROF.m.[x0]=Some y0].
proof.
  proc; if; auto=> /> &hr hcache hfresh r hsample.
  have hext := cache_extends_fresh ROF.m{hr} input{hr} r hfresh.
  move: hext; rewrite /cache_extends=> hext.
  exact (hext x0 y0 hcache).
qed.
lemma rof_get_fresh m0 x0 y0 : phoare [ROF.get :
  ROF.m=m0 /\ input=x0 /\ x0 \notin m0 ==> res=y0] = (mu1 uniform32 y0).
proof.
  proc; rcondt 1; first by auto.
  wp; rnd (pred1 y0); skip; auto=> />.
  move=> hx v hv; by rewrite get_set_sameE /=.
qed.

module type ROGPort = {
  proc init() : unit
  proc get(input : W8.t Array1152.t) : W8.t Array192.t
}.
module ROG : ROGPort = {
  var m : (W8.t Array1152.t,W8.t Array192.t) fmap
  proc init() = { m <- empty; }
  proc get(input : W8.t Array1152.t) : W8.t Array192.t = {
    var r;
    if (input \notin m) {
      r <$ uniform192;
      m.[input] <- r;
    }
    return oget m.[input];
  }
}.
lemma rog_init_empty : hoare [ROG.init : true ==> ROG.m = empty].
proof. by proc; auto. qed.
lemma rog_init_ll : islossless ROG.init.
proof. by proc; auto. qed.
lemma rog_get_ll : islossless ROG.get.
proof. proc; if; auto=> /> &hr _; exact uniform192_ll. qed.
lemma rog_get_value m0 x0 : hoare [ROG.get :
  ROG.m=m0 /\ input=x0 ==> ROG.m.[x0]=Some res /\ cache_extends m0 ROG.m].
proof.
  proc; if.
  + auto=> /> hx r hr; rewrite get_set_sameE /=.
    exact (cache_extends_fresh m0 x0 r hx).
  auto=> />.
  move=> hx; apply some_oget; move: hx; by rewrite domE.
qed.
lemma rog_get_cached m0 x0 y0 : hoare [ROG.get :
  ROG.m=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==> res=y0 /\ ROG.m=m0].
proof. proc; if; auto=> />; smt(domE). qed.
lemma rog_get_preserves x0 y0 : hoare [ROG.get :
  ROG.m.[x0]=Some y0 ==> ROG.m.[x0]=Some y0].
proof.
  proc; if; auto=> /> &hr hcache hfresh r hsample.
  have hext := cache_extends_fresh ROG.m{hr} input{hr} r hfresh.
  move: hext; rewrite /cache_extends=> hext.
  exact (hext x0 y0 hcache).
qed.
lemma rog_get_fresh m0 x0 y0 : phoare [ROG.get :
  ROG.m=m0 /\ input=x0 /\ x0 \notin m0 ==> res=y0] = (mu1 uniform192 y0).
proof.
  proc; rcondt 1; first by auto.
  wp; rnd (pred1 y0); skip; auto=> />.
  move=> hx v hv; by rewrite get_set_sameE /=.
qed.

module type ROHPort = {
  proc init() : unit
  proc get(input : W8.t Array96.t * W8.t Array32.t) : W8.t Array224.t
}.
module ROH : ROHPort = {
  var m : (W8.t Array96.t * W8.t Array32.t,W8.t Array224.t) fmap
  proc init() = { m <- empty; }
  proc get(input : W8.t Array96.t * W8.t Array32.t) : W8.t Array224.t = {
    var r;
    if (input \notin m) {
      r <$ uniform224;
      m.[input] <- r;
    }
    return oget m.[input];
  }
}.
lemma roh_init_empty : hoare [ROH.init : true ==> ROH.m = empty].
proof. by proc; auto. qed.
lemma roh_init_ll : islossless ROH.init.
proof. by proc; auto. qed.
lemma roh_get_ll : islossless ROH.get.
proof. proc; if; auto=> /> &hr _; exact uniform224_ll. qed.
lemma roh_get_value m0 x0 : hoare [ROH.get :
  ROH.m=m0 /\ input=x0 ==> ROH.m.[x0]=Some res /\ cache_extends m0 ROH.m].
proof.
  proc; if.
  + auto=> /> hx r hr; rewrite get_set_sameE /=.
    exact (cache_extends_fresh m0 x0 r hx).
  auto=> />.
  move=> hx; apply some_oget; move: hx; by rewrite domE.
qed.
lemma roh_get_cached m0 x0 y0 : hoare [ROH.get :
  ROH.m=m0 /\ input=x0 /\ m0.[x0]=Some y0 ==> res=y0 /\ ROH.m=m0].
proof. proc; if; auto=> />; smt(domE). qed.
lemma roh_get_preserves x0 y0 : hoare [ROH.get :
  ROH.m.[x0]=Some y0 ==> ROH.m.[x0]=Some y0].
proof.
  proc; if; auto=> /> &hr hcache hfresh r hsample.
  have hext := cache_extends_fresh ROH.m{hr} input{hr} r hfresh.
  move: hext; rewrite /cache_extends=> hext.
  exact (hext x0 y0 hcache).
qed.
lemma roh_get_fresh m0 x0 y0 : phoare [ROH.get :
  ROH.m=m0 /\ input=x0 /\ x0 \notin m0 ==> res=y0] = (mu1 uniform224 y0).
proof.
  proc; rcondt 1; first by auto.
  wp; rnd (pred1 y0); skip; auto=> />.
  move=> hx v hv; by rewrite get_set_sameE /=.
qed.

module ExpandROM = {
  proc shake(seed : W8.t Array32.t) : W8.t Array192.t = {
    var r; r <@ ROE.get(seed); return r;
  }
}.
module SHAKEFROM = {
  proc shake(input : W8.t Array1153.t) : W8.t Array32.t = {
    var r; r <@ ROF.get(peel1153 input); return r;
  }
}.
module SHAKEGROM = {
  proc shake(input : W8.t Array1153.t) : W8.t Array192.t = {
    var r; r <@ ROG.get(peel1153 input); return r;
  }
}.
module SHAKEHROM = {
  proc shake(input : W8.t Array129.t) : W8.t Array224.t = {
    var r; r <@ ROH.get(peel_h input); return r;
  }
}.
module ROMInit = {
  proc init() = { ROE.init(); ROF.init(); ROG.init(); ROH.init(); }
}.
lemma rom_init_empty : hoare [ROMInit.init : true ==>
  ROE.m=empty /\ ROF.m=empty /\ ROG.m=empty /\ ROH.m=empty].
proof. by proc; inline *; auto. qed.
lemma rom_init_ll : islossless ROMInit.init.
proof. by proc; inline *; auto. qed.

lemma ro_f_shake_value m0 pk0 : hoare [SHAKEFROM.shake :
  ROF.m=m0 /\ input=encode_f pk0 ==> ROF.m.[pk0]=Some res /\ cache_extends m0 ROF.m].
proof.
  proc; call (rof_get_value m0 pk0); auto=> />; by rewrite peel_encode_f.
qed.
lemma ro_f_shake_cached m0 pk0 y0 : hoare [SHAKEFROM.shake :
  ROF.m=m0 /\ input=encode_f pk0 /\ m0.[pk0]=Some y0 ==> res=y0 /\ ROF.m=m0].
proof.
  proc; call (rof_get_cached m0 pk0 y0); auto=> />; by rewrite peel_encode_f.
qed.
lemma ro_f_shake_ll : islossless SHAKEFROM.shake.
proof. by proc; call rof_get_ll; auto. qed.

lemma ro_g_shake_value m0 serialized0 : hoare [SHAKEGROM.shake :
  ROG.m=m0 /\ input=encode_g serialized0 ==> ROG.m.[serialized0]=Some res /\ cache_extends m0 ROG.m].
proof.
  proc; call (rog_get_value m0 serialized0); auto=> />; by rewrite peel_encode_g.
qed.
lemma ro_g_shake_cached m0 serialized0 y0 : hoare [SHAKEGROM.shake :
  ROG.m=m0 /\ input=encode_g serialized0 /\ m0.[serialized0]=Some y0 ==> res=y0 /\ ROG.m=m0].
proof.
  proc; call (rog_get_cached m0 serialized0 y0); auto=> />; by rewrite peel_encode_g.
qed.
lemma ro_g_shake_ll : islossless SHAKEGROM.shake.
proof. by proc; call rog_get_ll; auto. qed.

lemma ro_h_shake_value m0 coins0 suffix0 : hoare [SHAKEHROM.shake :
  ROH.m=m0 /\ input=encode_h coins0 suffix0 ==> ROH.m.[(coins0,suffix0)]=Some res /\ cache_extends m0 ROH.m].
proof.
  proc; call (roh_get_value m0 (coins0,suffix0)); auto=> />; by rewrite peel_encode_h.
qed.
lemma ro_h_shake_cached m0 coins0 suffix0 y0 : hoare [SHAKEHROM.shake :
  ROH.m=m0 /\ input=encode_h coins0 suffix0 /\ m0.[(coins0,suffix0)]=Some y0 ==> res=y0 /\ ROH.m=m0].
proof.
  proc; call (roh_get_cached m0 (coins0,suffix0) y0); auto=> />; by rewrite peel_encode_h.
qed.
lemma ro_h_shake_ll : islossless SHAKEHROM.shake.
proof. by proc; call roh_get_ll; auto. qed.

lemma ro_e_shake_value m0 seed0 : hoare [ExpandROM.shake :
  ROE.m=m0 /\ seed=seed0 ==> ROE.m.[seed0]=Some res /\ cache_extends m0 ROE.m].
proof. by proc; call (roe_get_value m0 seed0); auto. qed.
lemma ro_e_shake_ll : islossless ExpandROM.shake.
proof. by proc; call roe_get_ll; auto. qed.

lemma rom_oracles_eof m0 pk0 y0 : hoare [SHAKEFROM.shake :
  ROF.m=m0 /\ input=encode_f pk0 /\ m0.[pk0]=Some y0 ==> res=y0 /\ ROF.m=m0].
proof. exact (ro_f_shake_cached m0 pk0 y0). qed.
