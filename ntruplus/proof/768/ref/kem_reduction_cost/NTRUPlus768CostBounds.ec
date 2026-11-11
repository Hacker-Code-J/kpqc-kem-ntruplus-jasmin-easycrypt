require import AllCore List StdOrder FMap FSet.
import IntOrder.

(* A finite sequence of local lookup measurements.  This algebra does not
   manufacture a trace of an abstract adversary, assign constant cost to
   finite-map operations, or assert a whole-program running-time bound. *)
type cost_scan = {
 cs_history:int;
 cs_visits:int;
 cs_encryptions:int;
}.

op cost_scan_valid (s:cost_scan) =
 0<=s.`cs_encryptions /\ s.`cs_encryptions<=s.`cs_visits /\
 s.`cs_visits<=s.`cs_history.
op cost_sum ['a] (f:'a->int) (xs:'a list) =
 foldr (fun x acc=>f x+acc) 0 xs.
op cost_visits (xs:cost_scan list) = cost_sum (fun s=>s.`cs_visits) xs.
op cost_encryptions (xs:cost_scan list) = cost_sum (fun s=>s.`cs_encryptions) xs.
op cost_histories (xs:cost_scan list) = cost_sum (fun s=>s.`cs_history) xs.
op cost_trace_valid h (xs:cost_scan list) =
 all (fun s=>cost_scan_valid s /\ s.`cs_history<=h) xs.

lemma cost_sum_nil ['a] (f:'a->int) : cost_sum f []=0.
proof. by rewrite /cost_sum. qed.
lemma cost_sum_cons ['a] (f:'a->int) x xs :
 cost_sum f (x::xs)=f x+cost_sum f xs.
proof. by rewrite /cost_sum. qed.
lemma cost_sum_nonnegative ['a] (f:'a->int) xs :
 all (fun x=>0<=f x) xs=>0<=cost_sum f xs.
proof.
 elim:xs=>[|x xs ih];first by rewrite cost_sum_nil.
 rewrite /= cost_sum_cons; smt().
qed.
lemma cost_sum_mono ['a] (f g:'a->int) xs :
 all (fun x=>f x<=g x) xs=>cost_sum f xs<=cost_sum g xs.
proof.
 elim:xs=>[|x xs ih];first by rewrite !cost_sum_nil.
 rewrite /= !cost_sum_cons; smt().
qed.
lemma cost_sum_constant ['a] (xs:'a list) c :
 cost_sum (fun _=>c) xs=size xs*c.
proof.
 elim:xs=>[|x xs ih];first by rewrite cost_sum_nil.
 rewrite cost_sum_cons /= ih;smt().
qed.

lemma cost_trace_sums h xs : cost_trace_valid h xs=>
 0<=cost_encryptions xs /\ cost_encryptions xs<=cost_visits xs /\
 cost_visits xs<=cost_histories xs /\ cost_histories xs<=size xs*h.
proof.
 elim:xs=>[|x xs ih].
 + by rewrite /cost_encryptions /cost_visits /cost_histories !cost_sum_nil.
 move=> ht0.
 have hx: cost_scan_valid x /\ x.`cs_history<=h by move:ht0;rewrite /cost_trace_valid /=;smt().
 have ht: cost_trace_valid h xs by move:ht0;rewrite /cost_trace_valid /=;smt().
 have hb:=ih ht.
 move:hx;rewrite /cost_scan_valid=>hx.
 move:hb;rewrite /cost_encryptions /cost_visits /cost_histories.
 rewrite !cost_sum_cons /=;smt().
qed.

lemma cost_trace_call_bound h d xs :
 0<=h=>size xs<=d=>cost_trace_valid h xs=>
 0<=cost_encryptions xs<=cost_visits xs /\ cost_visits xs<=d*h.
proof.
 move=>hh hd ht;have hs:=cost_trace_sums h xs ht;smt().
qed.

(* g counts ALL direct and valid-raw G calls, including repeats and
   output-length zero.  Every lookup encryption contributes one more G
   record.  The exact local equality is proved for CostLookup, not assumed
   to follow from the distinct-H budget in the probability theorem. *)
lemma cost_trace_extraction_bound h d g e xs :
 0<=h=>0<=g=>size xs<=d=>cost_trace_valid h xs=>
 0<=e<=g+cost_encryptions xs=>
 e<=g+d*h /\ cost_visits xs+e<=g+2*d*h.
proof.
 move=>hh hg hd ht he;have hs:=cost_trace_call_bound h d xs hh hd ht;smt().
qed.

(* Weighted CALL counts only.  cenc and cext are nonnegative weights, not
   asserted CPU-cycle or bit-operation costs of the abstract operations. *)
lemma cost_trace_weighted_calls h d g e cenc cext xs :
 0<=h=>0<=g=>0<=cenc=>0<=cext=>size xs<=d=>
 cost_trace_valid h xs=>0<=e<=g+cost_encryptions xs=>
 cost_encryptions xs*cenc+e*cext<=d*h*cenc+(g+d*h)*cext.
proof.
 move=>hh hg hc hec hd ht he.
 have hs:=cost_trace_call_bound h d xs hh hd ht.
 have hb:=cost_trace_extraction_bound h d g e xs hh hg hd ht he.
 have he1:cost_encryptions xs<=d*h by smt().
 have he2:e<=g+d*h by smt().
 have h1:=ler_wpmul2r cenc hc _ _ he1.
 have h2:=ler_wpmul2r cext hec _ _ he2.
 smt().
qed.

lemma cost_trace_zero_calls xs :
 size xs<=0=>cost_visits xs=0 /\ cost_encryptions xs=0.
proof.
 move=>hn;have hx:xs=[] by smt(size_ge0 size_eq0).
 by rewrite hx /cost_visits /cost_encryptions !cost_sum_nil.
qed.

require import NTRUPlus768CostLookup NTRUPlus768CostExtract.
require import NTRUPlus768FOEagerG NTRUPlus768SimModel.

(* Each record premise above is supplied by the actual instrumented
   lookup.  The finite trace and its history cap remain explicit. *)
lemma cost_lookup_measurement (G<:FOGPort) log0 :
 hoare[CostLookup(G).decap:SimHistory.h=log0 ==>
 cost_scan_valid {|cs_history=size(elems(fdom log0));
                  cs_visits=res.`2;cs_encryptions=res.`3|}].
proof.
 conseq(cost_lookup_bounds G log0);rewrite /cost_scan_valid;smt().
qed.

lemma cost_extract_trace_budget pk0 ct0 excluded0 qs h d g xs :
 0<=h=>0<=g=>size xs<=d=>cost_trace_valid h xs=>
 size qs=g+cost_encryptions xs=>
 hoare[CostExtract.run:
 pk=pk0 /\ ct=ct0 /\ excluded=excluded0 /\ queries=qs ==>
 res.`2<=g+d*h /\ cost_visits xs+res.`2<=g+2*d*h].
proof.
 move=>hh hg hd ht hq.
 conseq(cost_extract_bounds pk0 ct0 excluded0 qs)=> //.
 move=> &hr _ result he.
 have he':0<=result.`2<=g+cost_encryptions xs by smt().
 exact(cost_trace_extraction_bound h d g result.`2 xs hh hg hd ht he').
qed.
