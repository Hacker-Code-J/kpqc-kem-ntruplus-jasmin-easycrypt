require import AllCore IntDiv List Ring StdBigop.

op sr_integer_kernel_trivial (m:int->int->int) =
 forall (a:int->int),
 (forall k,0<=k<768=>Bigint.BIA.bigi predT(fun j=>m k j*a j)0 768=0)=>
 forall j,0<=j<768=>a j=0.

op sr_matrix_rows_bounded (m:int->int->int) =
 forall k,0<=k<768=>Bigint.BIA.bigi predT(fun j=>m k j*m k j)0 768<=12288.

op sr_matrix_list_equation (m:int->int->int) (b:int->int) (xs:int list) =
 forall k,0<=k<768=>
 (Bigint.BIA.bigi predT(fun j=>m k j*nth 0 xs j)0 768+b k)%%3457=0.

lemma sr_solution_list_bound (m:int->int->int) (b:int->int) (xss:int list list) :
 sr_integer_kernel_trivial m=>sr_matrix_rows_bounded m=>
 uniq xss=>
 (forall xs,xs \in xss=>size xs=768 /\ all(fun x=>0<=x<3457)xs /\ sr_matrix_list_equation m b xs)=>
 size xss<=12288^384.
proof.
 coq check "sr_solution_list_bound" (range_geq range_ltn Ring.IntID.expr0 Ring.IntID.exprS).
qed.

lemma sr_matrix_fiber_bound (m:int->int->int) (b:int->int) (xss:int list list) :
 sr_integer_kernel_trivial m=>sr_matrix_rows_bounded m=>
 uniq xss=>
 (forall xs,xs \in xss=>size xs=768 /\ all(fun x=>0<=x<3457)xs)=>
 size(filter(sr_matrix_list_equation m b)xss)<=12288^384.
proof.
 move=>hk hr hu hc.
 apply(sr_solution_list_bound m b (filter(sr_matrix_list_equation m b)xss) hk hr).
 + exact(filter_uniq xss _ hu).
 move=>xs hx.
 have hb:sr_matrix_list_equation m b xs /\ xs \in xss by move:hx;rewrite mem_filter.
 have hm:xs \in xss by smt().
 have hs:=hc xs hm;smt().
qed.
