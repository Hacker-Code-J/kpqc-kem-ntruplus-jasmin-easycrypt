require import AllCore List StdOrder.
from Jasmin require import JWord.
require import Array32 Array96 Array768 Array1152.
require import NTRUPlus768FOModel NTRUPlus768HistKey.
require import NTRUPlus768RTStepSemantics.
import IntOrder.

(* Source-cost convention used by the fixed-kernel frontend: one scalar
   transfer plus each word comparison/arithmetic/logical instruction;
   indexed loads and stores include addressing, while arithmetic inside an
   index is charged separately. A guard charges its comparison and branch;
   return costs one. Fixed-array arguments and results additionally charge
   three operations per copied cell (allocation, read, write). The following straight scans are instrumented copies
   of the actual comparisons. Ghost bookkeeping is erased. Integers and
   indexed accesses are abstract unit-cost primitives, not bit costs. *)
op rt_byte_compare_steps(n:int)=18*n+5.
op rt_word_compare_steps(n:int)=16*n+5.
op rt_copy_steps(n:int)=14*n+5.
op rt_key_compare_steps=2629.

module RTPrimitive = {
 proc suffix(x y:W8.t Array32.t):bool*int={
  var same,byte_equal:bool;var comparisons,work:int;
  var left_byte,right_byte:W8.t;
  same<-true;comparisons<-0;work<-194;
  work<-work+2;
  while(comparisons<32){
   left_byte<-x.[comparisons];work<-work+2;
   right_byte<-y.[comparisons];work<-work+2;
   byte_equal<-(left_byte=right_byte);work<-work+2;
   same<-same /\ byte_equal;work<-work+2;
   comparisons<-comparisons+1;work<-work+2;
   work<-work+2;
  }
  work<-work+1;return(same,work);
 }
 proc cipher(x y:W8.t Array1152.t):bool*int={
  var same,byte_equal:bool;var comparisons,work:int;
  var left_byte,right_byte:W8.t;
  same<-true;comparisons<-0;work<-6914;
  work<-work+2;
  while(comparisons<1152){
   left_byte<-x.[comparisons];work<-work+2;
   right_byte<-y.[comparisons];work<-work+2;
   byte_equal<-(left_byte=right_byte);work<-work+2;
   same<-same /\ byte_equal;work<-work+2;
   comparisons<-comparisons+1;work<-work+2;
   work<-work+2;
  }
  work<-work+1;return(same,work);
 }
 proc key(x y:fo_h_input):bool*int={
  var same,byte_equal:bool;var comparisons,work:int;
  var left_byte,right_byte:W8.t;
  same<-true;comparisons<-0;work<-770;
  work<-work+2;
  while(comparisons<128){
   work<-work+2;
   if(comparisons<96){
    left_byte<-x.`1.[comparisons];work<-work+2;
    right_byte<-y.`1.[comparisons];work<-work+2;
   }else{
    left_byte<-x.`2.[comparisons-96];work<-work+3;
    right_byte<-y.`2.[comparisons-96];work<-work+3;
   }
   byte_equal<-(left_byte=right_byte);work<-work+2;
   same<-same /\ byte_equal;work<-work+2;
   comparisons<-comparisons+1;work<-work+2;
   work<-work+2;
  }
  work<-work+1;return(same,work);
 }
 proc word_equal(x y:W16.t Array768.t):bool*int={
  var same,word_equal:bool;var i,work:int;
  same<-true;i<-0;work<-4610;
  work<-work+2;
  while(i<768){
   word_equal<-(x.[i]=y.[i]);work<-work+4;
   same<-same /\ word_equal;work<-work+2;
   i<-i+1;work<-work+2;
   work<-work+2;
  }
  work<-work+1;return(same,work);
 }
 proc copy768(x:W16.t Array768.t):W16.t Array768.t*int={
  var out:W16.t Array768.t;var i,work:int;
  out<-witness;work<-3073;
  i<-0;work<-work+1;
  work<-work+2;
  while(i<768){
   out.[i]<-x.[i];work<-work+3;
   i<-i+1;work<-work+2;
   work<-work+2;
  }
  work<-work+2305;return(out,work);
 }
}.

lemma rt_primitive_suffix_ll : islossless RTPrimitive.suffix.
proof. proc;wp;while true(32-comparisons);auto=> />;smt(). qed.
lemma rt_primitive_suffix_steps :
 hoare[RTPrimitive.suffix:true ==>res.`2=rt_byte_compare_steps 32].
proof.
 proc;wp;while(0<=comparisons<=32 /\ work=196+12*comparisons).
 + auto=> />;smt().
 auto=> />;rewrite /rt_byte_compare_steps;smt().
qed.
lemma rt_primitive_suffix_projection :
 equiv[RTPrimitive.suffix~HistKey.suffix: ={x,y} ==>res{1}.`1=res{2}.`1].
proof. proc;wp;while(={x,y,same,comparisons});auto=> />;smt(). qed.
lemma rt_primitive_suffix_spec x0 y0 :
 hoare[RTPrimitive.suffix:x=x0 /\ y=y0 ==>res.`1=(x0=y0)].
proof.
 proc;wp;while(x=x0 /\ y=y0 /\ 0<=comparisons<=32 /\
 same=hist_byte_prefix(fun i=>x0.[i])(fun i=>y0.[i])comparisons).
 + auto=> />;smt(hist_byte_prefix_step).
 auto=> />;smt(hist_byte_prefix_zero hist_suffix_full).
qed.
lemma rt_primitive_suffix_correct x0 y0 :
 phoare[RTPrimitive.suffix:x=x0 /\ y=y0 ==>
 res=((x0=y0),rt_byte_compare_steps 32)]=1%r.
proof.
 have hc:hoare[RTPrimitive.suffix:x=x0 /\ y=y0 ==>res=((x0=y0),rt_byte_compare_steps 32)].
 + conseq(rt_primitive_suffix_spec x0 y0)rt_primitive_suffix_steps;smt().
 by conseq rt_primitive_suffix_ll hc.
qed.

lemma rt_primitive_cipher_ll : islossless RTPrimitive.cipher.
proof. proc;wp;while true(1152-comparisons);auto=> />;smt(). qed.
lemma rt_primitive_cipher_steps :
 hoare[RTPrimitive.cipher:true ==>res.`2=rt_byte_compare_steps 1152].
proof.
 proc;wp;while(0<=comparisons<=1152 /\ work=6916+12*comparisons).
 + auto=> />;smt().
 auto=> />;rewrite /rt_byte_compare_steps;smt().
qed.
lemma rt_primitive_cipher_projection :
 equiv[RTPrimitive.cipher~HistKey.cipher: ={x,y} ==>res{1}.`1=res{2}.`1].
proof. proc;wp;while(={x,y,same,comparisons});auto=> />;smt(). qed.
lemma rt_primitive_cipher_spec x0 y0 :
 hoare[RTPrimitive.cipher:x=x0 /\ y=y0 ==>res.`1=(x0=y0)].
proof.
 proc;wp;while(x=x0 /\ y=y0 /\ 0<=comparisons<=1152 /\
 same=hist_byte_prefix(fun i=>x0.[i])(fun i=>y0.[i])comparisons).
 + auto=> />;smt(hist_byte_prefix_step).
 auto=> />;smt(hist_byte_prefix_zero hist_cipher_full).
qed.
lemma rt_primitive_cipher_correct x0 y0 :
 phoare[RTPrimitive.cipher:x=x0 /\ y=y0 ==>
 res=((x0=y0),rt_byte_compare_steps 1152)]=1%r.
proof.
 have hc:hoare[RTPrimitive.cipher:x=x0 /\ y=y0 ==>res=((x0=y0),rt_byte_compare_steps 1152)].
 + conseq(rt_primitive_cipher_spec x0 y0)rt_primitive_cipher_steps;smt().
 by conseq rt_primitive_cipher_ll hc.
qed.

lemma rt_primitive_key_ll : islossless RTPrimitive.key.
proof. proc;wp;while true(128-comparisons);auto=> />;smt(). qed.
lemma rt_primitive_key_steps :
 hoare[RTPrimitive.key:true ==>res.`2=rt_key_compare_steps].
proof.
 proc;wp;while(0<=comparisons<=128 /\
 work=772+14*comparisons+2*max 0(comparisons-96)).
 + auto=> />;smt().
 auto=> />;rewrite /rt_key_compare_steps;smt().
qed.
lemma rt_primitive_key_projection :
 equiv[RTPrimitive.key~HistKey.equal: ={x,y} ==>res{1}.`1=res{2}.`1].
proof. proc;wp;while(={x,y,same,comparisons});auto=> />;smt(). qed.
lemma rt_primitive_key_spec x0 y0 :
 hoare[RTPrimitive.key:x=x0 /\ y=y0 ==>res.`1=(x0=y0)].
proof.
 proc;wp;while(x=x0 /\ y=y0 /\ 0<=comparisons<=128 /\
 same=hist_key_prefix x0 y0 comparisons).
 + wp;skip=> /> &hr h0 hn hlt.
   have hs:=hist_key_prefix_step x0 y0 comparisons{hr} h0.
   move:hs;rewrite /hist_key_byte;smt().
 auto=> />;smt(hist_key_prefix_zero hist_key_prefix_full).
qed.
lemma rt_primitive_key_correct x0 y0 :
 phoare[RTPrimitive.key:x=x0 /\ y=y0 ==>
 res=((x0=y0),rt_key_compare_steps)]=1%r.
proof.
 have hc:hoare[RTPrimitive.key:x=x0 /\ y=y0 ==>res=((x0=y0),rt_key_compare_steps)].
 + conseq(rt_primitive_key_spec x0 y0)rt_primitive_key_steps;smt().
 by conseq rt_primitive_key_ll hc.
qed.
lemma rt_primitive_word_equal_ll : islossless RTPrimitive.word_equal.
proof. proc;wp;while true(768-i);auto=> />;smt(). qed.
lemma rt_primitive_word_equal_steps :
 hoare[RTPrimitive.word_equal:true ==>res.`2=rt_word_compare_steps 768].
proof.
 proc;wp;while(0<=i<=768 /\ work=4612+10*i);auto=> />;
 rewrite /rt_word_compare_steps;smt().
qed.
lemma rt_primitive_word_equal_spec x0 y0 :
 hoare[RTPrimitive.word_equal:x=x0 /\ y=y0 ==>res.`1=(x0=y0)].
proof.
 proc;wp;while(x=x0 /\ y=y0 /\ 0<=i<=768 /\
 same=(forall j,0<=j<i=>x0.[j]=y0.[j])).
 + auto=> />;smt().
 auto=> />;smt(Array768.tP).
qed.
lemma rt_primitive_word_equal_correct x0 y0 :
 phoare[RTPrimitive.word_equal:x=x0 /\ y=y0 ==>
 res=((x0=y0),rt_word_compare_steps 768)]=1%r.
proof.
 have hc:hoare[RTPrimitive.word_equal:x=x0 /\ y=y0 ==>res=((x0=y0),rt_word_compare_steps 768)].
 + conseq(rt_primitive_word_equal_spec x0 y0)rt_primitive_word_equal_steps;smt().
 by conseq rt_primitive_word_equal_ll hc.
qed.
lemma rt_primitive_copy768_ll : islossless RTPrimitive.copy768.
proof. proc;wp;while true(768-i);auto=> />;smt(). qed.
lemma rt_primitive_copy768_spec x0 :
 hoare[RTPrimitive.copy768:x=x0 ==>res=(x0,rt_copy_steps 768)].
proof.
 proc;wp;while(x=x0 /\ 0<=i<=768 /\ work=3076+7*i /\
 forall j,0<=j<i=>out.[j]=x0.[j]).
 + auto=> />;smt(Array768.get_setE).
 auto=> />;rewrite /rt_copy_steps;smt(Array768.tP).
qed.
lemma rt_primitive_copy768_correct x0 :
 phoare[RTPrimitive.copy768:x=x0 ==>res=(x0,rt_copy_steps 768)]=1%r.
proof. by conseq rt_primitive_copy768_ll(rt_primitive_copy768_spec x0). qed.
