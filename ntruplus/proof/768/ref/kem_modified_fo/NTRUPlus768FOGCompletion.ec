require import AllCore List Distr DList FMap.
from Jasmin require import JWord.
require import Array192 Array1152.
require import NTRUPlus768ROMOracles NTRUPlus768ROMDistributions.
require import NTRUPlus768RRecCodec NTRUPlus768ACWC2Domains NTRUPlus768ACWC2Oracle.
require import NTRUPlus768FOEagerG.

clone DList.ParametricProgram as FOGPadLists with type t <- W8.t Array192.t.

lemma fo_g_ofassoc_nil : ofassoc [<:W8.t Array1152.t * W8.t Array192.t>]=empty.
proof. apply/fmap_eqP=>x; by rewrite ofassoc_get emptyE. qed.
lemma fo_g_ofassoc_rcons (xs:(W8.t Array1152.t * W8.t Array192.t)list) x y :
 !(List.mem (map fst xs) x) =>
 ofassoc(rcons xs (x,y))=(ofassoc xs).[x<-y].
proof.
 move=>hx; apply/fmap_eqP=>k.
 rewrite ofassoc_get get_setE ofassoc_get -cats1 assoc_cat assoc_seq1.
 smt(assocTP).
qed.
lemma fo_g_zip_keys (xs:W8.t Array1152.t list) (ys:W8.t Array192.t list) :
 size xs=size ys =>map fst (zip xs ys)=xs.
proof. move=>hs; apply unzip1_zip; smt(). qed.
lemma fo_g_prefix_fresh (xs:W8.t Array1152.t list) (ys:W8.t Array192.t list) i :
 uniq xs =>0<=i<size xs =>size ys=i =>
 nth witness xs i \notin ofassoc(zip(take i xs)ys).
proof.
 move=>hu hi hs.
 have ht:size(take i xs)=size ys by rewrite size_takel 1:/# hs.
 have hn:=uniq_take xs (i+1) hu.
 rewrite(take_nth witness i xs hi) rcons_uniq in hn.
 rewrite mem_ofassoc (fo_g_zip_keys _ _ ht); smt().
qed.
lemma fo_g_prefix_step (xs:W8.t Array1152.t list) (ys:W8.t Array192.t list) i y :
 uniq xs =>0<=i<size xs =>size ys=i =>
 (ofassoc(zip(take i xs)ys)).[nth witness xs i<-y]=
 ofassoc(zip(take(i+1)xs)(ys++[y])).
proof.
 move=>hu hi hs.
 have ht:size(take i xs)=size ys by rewrite size_takel 1:/# hs.
 have hf:=fo_g_prefix_fresh xs ys i hu hi hs.
 rewrite mem_ofassoc in hf.
 rewrite(take_nth witness i xs hi) cats1 (zip_rcons _ _ _ _ ht).
 apply/eq_sym; exact(fo_g_ofassoc_rcons _ _ _ hf).
qed.
lemma fo_g_cache_zip pads : size pads=size acwc2_r_enum =>
 ofassoc(zip fo_g_inputs pads)=acwc2_g_cache pads.
proof.
 move=>hs; rewrite /acwc2_g_cache.
 congr; apply(eq_from_nth (witness,witness)).
 + rewrite size_zip size_map fo_g_inputs_size hs /min; smt().
 move=>i hi.
 have hr:0<=i<size acwc2_r_enum by move:hi; rewrite size_zip fo_g_inputs_size hs /min; smt().
 have he:size fo_g_inputs=size pads by rewrite fo_g_inputs_size hs.
 rewrite(nth_zip witness witness _ _ i he).
 rewrite /fo_g_inputs (nth_map witness) 1:hr /=.
 rewrite(nth_map witness) 1:hr /= /acwc2_gfun.
 by rewrite(index_uniq witness i acwc2_r_enum hr acwc2_r_enum_uniq).
qed.
lemma fo_g_cache_empty_join pads : acwc2_g_cache pads+empty=acwc2_g_cache pads.
proof. apply/fmap_eqP=>x; by rewrite joinE mem_empty. qed.

(* Complete a finite injective input list by independent samples. The
   right-hand list stores them in that same order. No cache is overwritten. *)
lemma fo_g_completion_loop :
 equiv[FOGComplete(FOGRO.RO).run ~ FOGPadLists.LoopSnoc.sample:
 FOGRO.RO.m{1}=empty /\ d{2}=uniform192 /\ n{2}=size fo_g_inputs ==>
 FOGRO.RO.m{1}=ofassoc(zip fo_g_inputs res{2}) /\ size res{2}=size fo_g_inputs].
proof.
 proc.
 while(todo{1}=drop i{2} fo_g_inputs /\ d{2}=uniform192 /\ n{2}=size fo_g_inputs /\
   0<=i{2}<=n{2} /\ size l{2}=i{2} /\
   FOGRO.RO.m{1}=ofassoc(zip(take i{2} fo_g_inputs)l{2})).
 + inline FOGRO.RO.sample FOGRO.RO.get.
   rcondt{1} 4.
   - move=> &m; auto=> />; smt(fo_g_prefix_fresh fo_g_inputs_uniq head_drop).
   auto=> /> &2 h0 hle hdrop hlt y hy.
   have hi:0<=size l{2}<size fo_g_inputs by smt().
   have hs:=fo_g_prefix_step fo_g_inputs l{2} (size l{2}) y fo_g_inputs_uniq hi (eq_refl _).
   rewrite (behead_drop fo_g_inputs (size l{2}) h0)
    -(head_drop witness (size l{2}) fo_g_inputs h0) hs size_cat /=.
   have hnext:0<=size l{2}+1 by smt().
   clear hs hy hdrop.
   rewrite -!size_eq0 (size_drop (size l{2}+1) fo_g_inputs hnext) /max; smt().
 auto=> />.
 rewrite drop0 take0 /= fo_g_ofassoc_nil.
 split.
 + rewrite /= -!size_eq0.
   have hsize:=size_ge0 fo_g_inputs; smt().
 move=>ys hn hd h0 hle.
 have hs:size ys=size fo_g_inputs by smt().
 by rewrite hs take_size.
qed.

module FOGIIDSetup = {
 proc run() : W8.t Array192.t list = {
  var pads:W8.t Array192.t list;
  pads <$ acwc2_gpads_law;
  ACWC2EagerOracle.prepare(pads);
  return pads;
 }
}.
module FOGBatchSetup = {
 proc run() : W8.t Array192.t list = {
  var pads:W8.t Array192.t list;
  pads <$ dlist uniform192 (size acwc2_r_enum);
  ACWC2EagerOracle.prepare(pads);
  return pads;
 }
}.
lemma fo_g_iid_batch :
 equiv[FOGIIDSetup.run ~ FOGBatchSetup.run: ={ROG.m} ==> ={res,ROG.m}].
proof.
 proc; call(_: ={pads,ROG.m} ==> ={ROG.m}); first by sim.
 rnd; auto=> />; by rewrite /acwc2_gpads_law.
qed.

module FOGLoopSetup = {
 proc run() : W8.t Array192.t list = {
  var pads:W8.t Array192.t list;
  pads <@ FOGPadLists.LoopSnoc.sample(uniform192,size fo_g_inputs);
  ROG.m <- ofassoc(zip fo_g_inputs pads);
  return pads;
 }
}.
lemma fo_g_completion_loop_setup :
 equiv[FOGComplete(FOGRO.RO).run ~ FOGLoopSetup.run:
 FOGRO.RO.m{1}=empty ==>
 FOGRO.RO.m{1}=ROG.m{2} /\ ROG.m{2}=acwc2_g_cache res{2} /\
 size res{2}=size acwc2_r_enum].
proof.
 proc*; inline{2} FOGLoopSetup.run; wp.
 call fo_g_completion_loop; auto=> />; smt(fo_g_cache_zip fo_g_inputs_size).
qed.
lemma fo_g_batch_loop :
 equiv[FOGBatchSetup.run ~ FOGLoopSetup.run:
 ROG.m{1}=empty ==> ={res,ROG.m} /\ size res{1}=size acwc2_r_enum].
proof.
 proc; inline ACWC2EagerOracle.prepare; wp.
 outline{1} 1 ~ FOGPadLists.Sample.sample.
 conseq (_:_ ==> ={pads} /\ size pads{1}=size acwc2_r_enum).
 + auto=> />; smt(fo_g_cache_zip fo_g_cache_empty_join).
 call (_: ={d,n} /\ n{1}=size acwc2_r_enum ==> ={res} /\ size res{1}=size acwc2_r_enum).
 + conseq FOGPadLists.Sample_LoopSnoc_eq (_:n=size acwc2_r_enum ==>size res=size acwc2_r_enum) _=> //.
   proc; rnd; auto=> />; smt(supp_dlist_size size_ge0).
 auto=> />; by rewrite fo_g_inputs_size.
qed.
lemma fo_g_iid_loop :
 equiv[FOGIIDSetup.run ~ FOGLoopSetup.run:
 ROG.m{1}=empty ==> ={res,ROG.m} /\ size res{1}=size acwc2_r_enum].
proof.
 transitivity FOGBatchSetup.run
  (={ROG.m} /\ ROG.m{1}=empty ==> ={res,ROG.m})
  (ROG.m{1}=empty ==> ={res,ROG.m} /\ size res{1}=size acwc2_r_enum)=> //.
 + smt().
 + conseq fo_g_iid_batch; smt().
 exact fo_g_batch_loop.
qed.

lemma fo_g_completion_iid :
 equiv[FOGComplete(FOGRO.RO).run ~ FOGIIDSetup.run:
 FOGRO.RO.m{1}=empty /\ ROG.m{2}=empty ==>
 FOGRO.RO.m{1}=ROG.m{2} /\ ROG.m{2}=acwc2_g_cache res{2} /\
 size res{2}=size acwc2_r_enum].
proof.
 transitivity FOGLoopSetup.run
  (FOGRO.RO.m{1}=empty ==> FOGRO.RO.m{1}=ROG.m{2} /\
   ROG.m{2}=acwc2_g_cache res{2} /\ size res{2}=size acwc2_r_enum)
  (ROG.m{2}=empty ==> ={res,ROG.m} /\ size res{2}=size acwc2_r_enum)=> //.
 + exact fo_g_completion_loop_setup.
 symmetry; conseq fo_g_iid_loop; smt().
qed.
