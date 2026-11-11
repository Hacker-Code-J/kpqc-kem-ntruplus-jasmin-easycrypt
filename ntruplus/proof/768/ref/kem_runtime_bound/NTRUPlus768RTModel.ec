require import AllCore IntDiv StdOrder.
import IntOrder.

(* Phase resource counters. H counts completed public H records, including
   cached repetitions and valid raw zero-output H. Q counts every public
   callback at entry; G counts direct typed and valid raw G, not internal
   lookup encryptions. B counts all raw request payload bytes, including
   invalid requests. Alloc counts history-list cons operations only. *)
type rt_profile = {
 rp_h:int; rp_size:int; rp_d:int; rp_g:int; rp_q:int; rp_b:int;
 rp_put_v:int; rp_put_c:int; rp_dec_v:int; rp_dec_c:int;
 rp_enc:int; rp_alloc:int; rp_xcalls:int; rp_xvisits:int;
}.
op rt_zero : rt_profile =
 {|rp_h=0;rp_size=0;rp_d=0;rp_g=0;rp_q=0;rp_b=0;
 rp_put_v=0;rp_put_c=0;rp_dec_v=0;rp_dec_c=0;
 rp_enc=0;rp_alloc=0;rp_xcalls=0;rp_xvisits=0|}.
op rt_call (p:rt_profile) (is_g:bool) (bytes:int) =
 {|p with rp_q=p.`rp_q+1;rp_g=p.`rp_g+b2i is_g;rp_b=p.`rp_b+bytes|}.
op rt_record (p:rt_profile) (visits comparisons:int) =
 {|p with rp_h=p.`rp_h+1;rp_size=1+visits-p.`rp_size;
 rp_put_v=p.`rp_put_v+visits;rp_put_c=p.`rp_put_c+comparisons;
 rp_alloc=p.`rp_alloc+2*(visits-p.`rp_size)+1|}.
op rt_decap (p:rt_profile) (visits encryptions comparisons:int) =
 {|p with rp_d=p.`rp_d+1;rp_dec_v=p.`rp_dec_v+visits;
 rp_enc=p.`rp_enc+encryptions;rp_dec_c=p.`rp_dec_c+comparisons|}.
op rt_extract (p:rt_profile) (visits:int) =
 {|p with rp_xcalls=p.`rp_xcalls+1;rp_xvisits=p.`rp_xvisits+visits|}.

op rt_nonnegative (p:rt_profile) =
 0<=p.`rp_h /\ 0<=p.`rp_size /\ 0<=p.`rp_d /\ 0<=p.`rp_g /\ 0<=p.`rp_q /\ 0<=p.`rp_b /\
 0<=p.`rp_put_v /\ 0<=p.`rp_put_c /\ 0<=p.`rp_dec_v /\ 0<=p.`rp_dec_c /\
 0<=p.`rp_enc /\ 0<=p.`rp_alloc /\ 0<=p.`rp_xcalls /\ 0<=p.`rp_xvisits.
op rt_cost_ok (p:rt_profile) =
 rt_nonnegative p /\ p.`rp_size<=p.`rp_h /\ p.`rp_g<=p.`rp_q /\
 p.`rp_put_v<=p.`rp_h*(p.`rp_h-1) /\
 p.`rp_put_c<=64*p.`rp_h*(p.`rp_h-1) /\ p.`rp_alloc<=p.`rp_h*p.`rp_h /\
 p.`rp_enc<=p.`rp_dec_v /\ p.`rp_dec_v<=p.`rp_d*p.`rp_size /\
 p.`rp_dec_c<=1152*p.`rp_d+32*p.`rp_dec_v+1152*p.`rp_enc /\
 p.`rp_xvisits<=p.`rp_xcalls*(p.`rp_g+p.`rp_enc).

op rt_visits (p:rt_profile) = p.`rp_put_v+p.`rp_dec_v+p.`rp_xvisits.
op rt_comparisons (p:rt_profile) = p.`rp_put_c+p.`rp_dec_c.
op rt_g_length (p:rt_profile) = p.`rp_g+p.`rp_enc.


lemma rt_mul_mono c a b : 0<=c=>a<=b=>c*a<=c*b.
proof. move=>hc hab;exact(ler_wpmul2l c hc a b hab). qed.
lemma rt_zero_ok : rt_cost_ok rt_zero.
proof. by rewrite /rt_cost_ok /rt_nonnegative /rt_zero. qed.
lemma rt_cost_nonnegative p : rt_cost_ok p=>rt_nonnegative p.
proof. rewrite /rt_cost_ok;smt(). qed.
lemma rt_record_growth h n kept : 0<=n<=h=>0<=kept<=n=>
 h*(h-1)+n+kept<=(h+1)*h /\
 64*h*(h-1)+128*n<=64*(h+1)*h /\ h*h+2*kept+1<=(h+1)*(h+1).
proof. smt(). qed.

lemma rt_call_ok p is_g bytes : rt_cost_ok p=>0<=bytes=>rt_cost_ok(rt_call p is_g bytes).
proof.
 move=>hp hb.
 have hx:0<=p.`rp_xcalls by move:hp;rewrite /rt_cost_ok /rt_nonnegative;smt().
 have hg:p.`rp_g+p.`rp_enc<=p.`rp_g+b2i is_g+p.`rp_enc by case is_g;smt().
 have hm:=rt_mul_mono p.`rp_xcalls _ _ hx hg.
 move:hp;rewrite /rt_cost_ok /rt_nonnegative /rt_call /=;case is_g;smt().
qed.
lemma rt_record_ok p kept : rt_cost_ok p=>0<=kept<=p.`rp_size=>p.`rp_size<=kept+1=>
 rt_cost_ok(rt_record p (p.`rp_size+kept) (128*p.`rp_size)).
proof.
 move=>hp hk hn.
 have hd:0<=p.`rp_d by move:hp;rewrite /rt_cost_ok /rt_nonnegative;smt().
 have hh:0<=p.`rp_size<=p.`rp_h by move:hp;rewrite /rt_cost_ok /rt_nonnegative;smt().
 have hm:=rt_mul_mono p.`rp_d p.`rp_size (kept+1) hd hn.
 have hb:=rt_record_growth p.`rp_h p.`rp_size kept hh hk.
 move:hp;rewrite /rt_cost_ok /rt_nonnegative /rt_record /=;smt().
qed.
lemma rt_decap_ok p v k c : rt_cost_ok p=>0<=k<=v=>v<=p.`rp_size=>
 0<=c<=1152+32*v+1152*k=>rt_cost_ok(rt_decap p v k c).
proof.
 move=>hp hk hv hc.
 have hx:0<=p.`rp_xcalls by move:hp;rewrite /rt_cost_ok /rt_nonnegative;smt().
 have hg:p.`rp_g+p.`rp_enc<=p.`rp_g+(p.`rp_enc+k) by smt().
 have hm:=rt_mul_mono p.`rp_xcalls _ _ hx hg.
 move:hp;rewrite /rt_cost_ok /rt_nonnegative /rt_decap /=;smt().
qed.
lemma rt_extract_ok p v : rt_cost_ok p=>0<=v<=rt_g_length p=>rt_cost_ok(rt_extract p v).
proof. rewrite /rt_cost_ok /rt_nonnegative /rt_extract /rt_g_length /=;smt(). qed.

lemma rt_call_g_length p is_g bytes : rt_g_length(rt_call p is_g bytes)=rt_g_length p+b2i is_g.
proof. rewrite /rt_g_length /rt_call /=;smt(). qed.
lemma rt_record_g_length p v c : rt_g_length(rt_record p v c)=rt_g_length p.
proof. by rewrite /rt_g_length /rt_record. qed.
lemma rt_decap_g_length p v k c : rt_g_length(rt_decap p v k c)=rt_g_length p+k.
proof. rewrite /rt_g_length /rt_decap /=;smt(). qed.
lemma rt_extract_g_length p v : rt_g_length(rt_extract p v)=rt_g_length p.
proof. by rewrite /rt_g_length /rt_extract. qed.

lemma rt_encryption_bound p : rt_cost_ok p=>0<=p.`rp_enc<=p.`rp_d*p.`rp_size.
proof. rewrite /rt_cost_ok /rt_nonnegative;smt(). qed.
lemma rt_extraction_bound p : rt_cost_ok p=>
 0<=p.`rp_xvisits<=p.`rp_xcalls*(p.`rp_g+p.`rp_d*p.`rp_size).
proof.
 move=>hp;have he:=rt_encryption_bound p hp.
 have hx:0<=p.`rp_xcalls by move:hp;rewrite /rt_cost_ok /rt_nonnegative;smt().
 have hg:p.`rp_g+p.`rp_enc<=p.`rp_g+p.`rp_d*p.`rp_size by smt().
 have hm:=rt_mul_mono p.`rp_xcalls _ _ hx hg.
 move:hp;rewrite /rt_cost_ok /rt_nonnegative;smt().
qed.
lemma rt_comparison_bound p : rt_cost_ok p=>
 0<=rt_comparisons p<=64*p.`rp_h*(p.`rp_h-1)+1152*p.`rp_d+1184*p.`rp_d*p.`rp_size.
proof.
 move=>hp;have he:=rt_encryption_bound p hp.
 move:hp;rewrite /rt_cost_ok /rt_nonnegative /rt_comparisons;smt().
qed.
lemma rt_one_extraction_bound p : rt_cost_ok p=>p.`rp_xcalls<=1=>
 p.`rp_xvisits<=p.`rp_g+p.`rp_d*p.`rp_size /\
 0<=rt_visits p<=p.`rp_h*(p.`rp_h-1)+p.`rp_g+2*p.`rp_d*p.`rp_size.
proof.
 move=>hp hx;have he:=rt_extraction_bound p hp.
 have hn:0<=p.`rp_g+p.`rp_d*p.`rp_size by move:hp;rewrite /rt_cost_ok /rt_nonnegative;smt().
 have hm:=rt_mul_mono _ _ _ hn hx.
 move:hp;rewrite /rt_cost_ok /rt_nonnegative /rt_visits;smt().
qed.
