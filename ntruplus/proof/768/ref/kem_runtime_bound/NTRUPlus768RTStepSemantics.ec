require import AllCore List StdOrder.
import IntOrder.

(* The resource model counts primitive word instructions, indexed memory
   accesses, control decisions, allocated cells, sampled bytes and ideal
   oracle invocations. It is not a native-cycle or unbounded-integer bit
   cost model. Unbounded EC integer arithmetic used by control counters and
   length guards is explicitly an abstract unit-cost primitive here. The
   ideal-oracle unit does not include a concrete finite-map implementation.
   Instrumentation counters and traces are proof observations;
   their own construction is erased. Every source expression must be
   expanded into its allowed primitive instructions before this model is
   applied. A whole polynomial, map, initializer or kernel is not one tick. *)
type rt_primitive = [ RTWordOp | RTLoad | RTStore | RTBranch |
                      RTAlloc | RTRandomByte | RTIdealOracle ].
type rt_trace = rt_primitive list.
type rt_weight = rt_primitive -> int.
type rt_counts = rt_primitive -> int.
op rt_count (tr:rt_trace) (p:rt_primitive) = count (pred1 p) tr.
op rt_zero_counts : rt_counts = fun _=>0.
op rt_add_counts (a b:rt_counts) : rt_counts = fun p=>a p+b p.
op rt_usage (w l s b a r o:int) (p:rt_primitive) : int =
 with p=RTWordOp=>w with p=RTLoad=>l with p=RTStore=>s
 with p=RTBranch=>b with p=RTAlloc=>a with p=RTRandomByte=>r
 with p=RTIdealOracle=>o.
op rt_total (u:rt_counts) = u RTWordOp+u RTLoad+u RTStore+
 u RTBranch+u RTAlloc+u RTRandomByte+u RTIdealOracle.
op rt_price (w:rt_weight) (u:rt_counts) =
 w RTWordOp*u RTWordOp+w RTLoad*u RTLoad+w RTStore*u RTStore+
 w RTBranch*u RTBranch+w RTAlloc*u RTAlloc+
 w RTRandomByte*u RTRandomByte+w RTIdealOracle*u RTIdealOracle.
op rt_nonnegative_weights (w:rt_weight) = forall p,0<=w p.
op rt_nonnegative_counts (u:rt_counts) = forall p,0<=u p.
op rt_weights_bounded (w:rt_weight) (c:int) = forall p,0<=w p<=c.
op rt_counts_le (u v:rt_counts) = forall p,0<=u p<=v p.
op rt_trace_cost (w:rt_weight) (tr:rt_trace) = rt_price w (rt_count tr).
op rt_unit_weight : rt_weight = fun _=>1.
op rt_ticks (p:rt_primitive) (n:int) : rt_trace = nseq n p.

lemma rt_count_nil p : rt_count [] p=0.
proof. by rewrite /rt_count. qed.
lemma rt_count_cat xs ys p :
 rt_count(xs++ys)p=rt_count xs p+rt_count ys p.
proof. by rewrite /rt_count count_cat. qed.
lemma rt_count_nonnegative tr : rt_nonnegative_counts(rt_count tr).
proof. rewrite /rt_nonnegative_counts /rt_count=>p;exact(count_ge0 (pred1 p)tr). qed.
lemma rt_count_ticks p n q : rt_count(rt_ticks p n)q=
 if q=p then max 0 n else 0.
proof. rewrite /rt_count /rt_ticks count_nseq /pred1;smt(). qed.
lemma rt_total_usage w l s b a r o :
 rt_total(rt_usage w l s b a r o)=w+l+s+b+a+r+o.
proof. by rewrite /rt_total /rt_usage. qed.
lemma rt_price_add w a b :
 rt_price w(rt_add_counts a b)=rt_price w a+rt_price w b.
proof. rewrite /rt_price /rt_add_counts;ring. qed.
lemma rt_trace_cost_cat w xs ys :
 rt_trace_cost w(xs++ys)=rt_trace_cost w xs+rt_trace_cost w ys.
proof. rewrite /rt_trace_cost /rt_price !rt_count_cat;ring. qed.
lemma rt_total_count tr : rt_total(rt_count tr)=size tr.
proof.
 elim tr=>[|p tr ih];first by rewrite /rt_total /rt_count.
 move:ih;rewrite /rt_total /rt_count /=.
 by case p=> /=;smt().
qed.
lemma rt_unit_price u : rt_price rt_unit_weight u=rt_total u.
proof. by rewrite /rt_price /rt_unit_weight /rt_total /=. qed.
lemma rt_unit_trace_cost tr : rt_trace_cost rt_unit_weight tr=size tr.
proof. by rewrite /rt_trace_cost rt_unit_price rt_total_count. qed.
lemma rt_price_nonnegative w u :
 rt_nonnegative_weights w=>rt_nonnegative_counts u=>0<=rt_price w u.
proof.
 rewrite /rt_nonnegative_weights /rt_nonnegative_counts /rt_price.
 move=> hw hu.
 have hw0:=hw RTWordOp;have hw1:=hw RTLoad;have hw2:=hw RTStore;
 have hw3:=hw RTBranch;have hw4:=hw RTAlloc;
 have hw5:=hw RTRandomByte;have hw6:=hw RTIdealOracle.
 have hu0:=hu RTWordOp;have hu1:=hu RTLoad;have hu2:=hu RTStore;
 have hu3:=hu RTBranch;have hu4:=hu RTAlloc;
 have hu5:=hu RTRandomByte;have hu6:=hu RTIdealOracle.
 smt().
qed.
lemma rt_price_max_bound w u c :
 rt_weights_bounded w c=>rt_nonnegative_counts u=>
 rt_price w u<=c*rt_total u.
proof.
 rewrite /rt_weights_bounded /rt_nonnegative_counts /rt_price /rt_total.
 move=> hw hu.
 have hw0:=hw RTWordOp;have hw1:=hw RTLoad;have hw2:=hw RTStore;
 have hw3:=hw RTBranch;have hw4:=hw RTAlloc;
 have hw5:=hw RTRandomByte;have hw6:=hw RTIdealOracle.
 have hu0:=hu RTWordOp;have hu1:=hu RTLoad;have hu2:=hu RTStore;
 have hu3:=hu RTBranch;have hu4:=hu RTAlloc;
 have hu5:=hu RTRandomByte;have hu6:=hu RTIdealOracle.
 smt().
qed.
lemma rt_trace_price_from_length w tr c n :
 rt_weights_bounded w c=>size tr<=n=>rt_trace_cost w tr<=c*n.
proof.
 move=> hw hn.
 have hc:0<=c by move:(hw RTWordOp);rewrite /rt_weights_bounded;smt().
 have h:=rt_price_max_bound w(rt_count tr)c hw(rt_count_nonnegative tr).
 move:h;rewrite -/rt_trace_cost rt_total_count;smt().
qed.

(* True tags are instructions executed inside the adversary. False tags
   are reduction-owned instructions, including callback bodies. The trace
   must be the calibrated trace of the actual execution; this theorem
   does not assert that an arbitrary appended list describes a program. *)
type rt_owned_trace = (bool*rt_primitive) list.
op rt_all_trace(t:rt_owned_trace) = map snd t.
op rt_self_trace(t:rt_owned_trace) = map snd(filter(fun(e:bool*rt_primitive)=>e.`1)t).
op rt_overhead_trace(t:rt_owned_trace) = map snd(filter(fun(e:bool*rt_primitive)=>!e.`1)t).
lemma rt_owned_partition_count tr p :
 rt_count(rt_all_trace tr)p=
 rt_count(rt_self_trace tr)p+rt_count(rt_overhead_trace tr)p.
proof.
 rewrite /rt_all_trace /rt_self_trace /rt_overhead_trace /rt_count
 !count_map !count_filter.
 exact(countID _ (fun(e:bool*rt_primitive)=>e.`1)tr).
qed.
lemma rt_owned_partition_cost w tr :
 rt_trace_cost w(rt_all_trace tr)=
 rt_trace_cost w(rt_self_trace tr)+rt_trace_cost w(rt_overhead_trace tr).
proof.
 have h:rt_count(rt_all_trace tr)=
 rt_add_counts(rt_count(rt_self_trace tr))(rt_count(rt_overhead_trace tr)).
 + apply fun_ext=>p;exact(rt_owned_partition_count tr p).
 by rewrite /rt_trace_cost h rt_price_add.
qed.
lemma rt_total_from_self_and_overhead w tr tA overhead :
 rt_trace_cost w(rt_self_trace tr)<=tA=>
 rt_trace_cost w(rt_overhead_trace tr)<=overhead=>
 rt_trace_cost w(rt_all_trace tr)<=tA+overhead.
proof. move=> ha ho;rewrite (rt_owned_partition_cost w tr);exact(ler_add _ _ _ _ ha ho). qed.
