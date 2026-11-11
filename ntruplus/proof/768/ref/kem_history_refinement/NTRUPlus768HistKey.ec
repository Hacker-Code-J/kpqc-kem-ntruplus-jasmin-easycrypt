require import AllCore Distr.
from Jasmin require import JWord.
require import Array32 Array96 Array1152.
require import NTRUPlus768FOModel.

(* Specification only: the executable comparator below reads the two
   fixed arrays directly. All 128 bytes are compared, including after
   a mismatch. The resource units are one indexed byte read and one
   byte equality test; no CPU-cycle or constant-time theorem is claimed. *)
op [opaque] hist_key_byte (x:fo_h_input) (i:int) : W8.t =
 if i<96 then x.`1.[i] else x.`2.[i-96].
op hist_key_prefix (x y:fo_h_input) (n:int) =
 forall i,0<=i<n=>hist_key_byte x i=hist_key_byte y i.

lemma hist_key_index_bounds i : 0<=i<128=>
 (i<96=>0<=i<96) /\ (!(i<96)=>0<=i-96<32).
proof. smt(). qed.
lemma hist_key_prefix_zero x y : hist_key_prefix x y 0.
proof. rewrite /hist_key_prefix;smt(). qed.
lemma hist_key_prefix_step x y n : 0<=n=>
 hist_key_prefix x y (n+1)=(hist_key_prefix x y n /\ hist_key_byte x n=hist_key_byte y n).
proof. rewrite /hist_key_prefix;smt(). qed.
lemma hist_key_prefix_full x y : hist_key_prefix x y 128=(x=y).
proof.
 rewrite /hist_key_prefix;apply eq_iff;split.
 + move=>h.
   have h1:x.`1=y.`1.
   - apply Array96.tP=>i hi.
     have hi128:0<=i<128 by smt().
     have hb:=h i hi128;move:hb;rewrite /hist_key_byte;smt().
   have h2:x.`2=y.`2.
   - apply Array32.tP=>i hi.
     have hi128:0<=i+96<128 by smt().
     have hb:=h (i+96) hi128;move:hb;rewrite /hist_key_byte;smt().
   smt().
 by move=>->.
qed.

module HistKey = {
 proc equal(x y:fo_h_input):bool*int = {
  var same,byte_equal:bool;var comparisons:int;var left_byte,right_byte:W8.t;
  same<-true;comparisons<-0;
  while(comparisons<128){
   if(comparisons<96){
    left_byte<-x.`1.[comparisons];right_byte<-y.`1.[comparisons];
   }else{
    left_byte<-x.`2.[comparisons-96];right_byte<-y.`2.[comparisons-96];
   }
   byte_equal<-(left_byte=right_byte);
   same<-same /\ byte_equal;
   comparisons<-comparisons+1;
  }
  return(same,comparisons);
 }
 proc suffix(x y:W8.t Array32.t):bool*int = {
  var same,byte_equal:bool;var comparisons:int;var left_byte,right_byte:W8.t;
  same<-true;comparisons<-0;
  while(comparisons<32){
   left_byte<-x.[comparisons];right_byte<-y.[comparisons];
   byte_equal<-(left_byte=right_byte);
   same<-same /\ byte_equal;
   comparisons<-comparisons+1;
  }
  return(same,comparisons);
 }
 proc cipher(x y:W8.t Array1152.t):bool*int = {
  var same,byte_equal:bool;var comparisons:int;var left_byte,right_byte:W8.t;
  same<-true;comparisons<-0;
  while(comparisons<1152){
   left_byte<-x.[comparisons];right_byte<-y.[comparisons];
   byte_equal<-(left_byte=right_byte);
   same<-same /\ byte_equal;
   comparisons<-comparisons+1;
  }
  return(same,comparisons);
 }
}.

lemma hist_key_lossless : islossless HistKey.equal.
proof.
 proc;while(0<=comparisons<=128)(128-comparisons);auto=> />;smt().
qed.
lemma hist_key_spec x0 y0 :
 hoare[HistKey.equal:x=x0 /\ y=y0 ==>res.`1=(x0=y0) /\ res.`2=128].
proof.
 proc;while(x=x0 /\ y=y0 /\ 0<=comparisons<=128 /\
 same=hist_key_prefix x0 y0 comparisons).
 + wp;skip=> /> &hr h0 h128 hlt.
   have hs:=hist_key_prefix_step x0 y0 comparisons{hr} h0.
   move:hs;rewrite /hist_key_byte;smt().
 auto=> />;smt(hist_key_prefix_zero hist_key_prefix_full).
qed.
lemma hist_key_functional x0 y0 :
 hoare[HistKey.equal:x=x0 /\ y=y0 ==>res.`1=(x0=y0)].
proof. conseq(hist_key_spec x0 y0);smt(). qed.
lemma hist_key_count : hoare[HistKey.equal:true ==>res.`2=128].
proof.
 proc;while(0<=comparisons<=128);auto=> />;smt().
qed.
lemma hist_key_bounds : hoare[HistKey.equal:true ==>0<=res.`2<=128].
proof. conseq hist_key_count;smt(). qed.
lemma hist_key_equal_count x0 :
 hoare[HistKey.equal:x=x0 /\ y=x0 ==>res=(true,128)].
proof. conseq(hist_key_spec x0 x0);smt(). qed.
lemma hist_key_correct x0 y0 :
 phoare[HistKey.equal:x=x0 /\ y=y0 ==>res.`1=(x0=y0) /\ res.`2=128]=1%r.
proof. by conseq hist_key_lossless (hist_key_spec x0 y0). qed.

(* Exactly two explicit indexed reads precede each counted comparison.
   This derived count is in the stated indexed-read model, not a claim
   about machine loads performed by a compiler or a cache. *)
lemma hist_key_indexed_read_count :
 hoare[HistKey.equal:true ==>2*res.`2=256].
proof. conseq hist_key_count;smt(). qed.


op hist_byte_prefix (x y:int->W8.t) (n:int) =
 forall i,0<=i<n=>x i=y i.
lemma hist_byte_prefix_zero x y : hist_byte_prefix x y 0.
proof. rewrite /hist_byte_prefix;smt(). qed.
lemma hist_byte_prefix_step x y n : 0<=n=>
 hist_byte_prefix x y (n+1)=(hist_byte_prefix x y n /\ x n=y n).
proof. rewrite /hist_byte_prefix;smt(). qed.
lemma hist_suffix_full (x y:W8.t Array32.t) :
 hist_byte_prefix (fun i=>x.[i]) (fun i=>y.[i]) 32=(x=y).
proof.
 rewrite /hist_byte_prefix;apply eq_iff;split.
 + move=>h;apply Array32.tP=>i hi;exact(h i hi).
 by move=>->.
qed.
lemma hist_cipher_full (x y:W8.t Array1152.t) :
 hist_byte_prefix (fun i=>x.[i]) (fun i=>y.[i]) 1152=(x=y).
proof.
 rewrite /hist_byte_prefix;apply eq_iff;split.
 + move=>h;apply Array1152.tP=>i hi;exact(h i hi).
 by move=>->.
qed.

lemma hist_suffix_lossless : islossless HistKey.suffix.
proof. proc;while(0<=comparisons<=32)(32-comparisons);auto=> />;smt(). qed.
lemma hist_suffix_spec x0 y0 :
 hoare[HistKey.suffix:x=x0 /\ y=y0 ==>res.`1=(x0=y0) /\ res.`2=32].
proof.
 proc;while(x=x0 /\ y=y0 /\ 0<=comparisons<=32 /\
 same=hist_byte_prefix (fun i=>x0.[i]) (fun i=>y0.[i]) comparisons).
 + wp;skip=> /> &hr h0 hn hlt.
   have hs:=hist_byte_prefix_step (fun i=>x0.[i]) (fun i=>y0.[i]) comparisons{hr} h0.
   smt().
 auto=> />;smt(hist_byte_prefix_zero hist_suffix_full).
qed.
lemma hist_suffix_count : hoare[HistKey.suffix:true ==>res.`2=32].
proof. proc;while(0<=comparisons<=32);auto=> />;smt(). qed.
lemma hist_suffix_correct x0 y0 :
 phoare[HistKey.suffix:x=x0 /\ y=y0 ==>res.`1=(x0=y0) /\ res.`2=32]=1%r.
proof. by conseq hist_suffix_lossless (hist_suffix_spec x0 y0). qed.

lemma hist_cipher_lossless : islossless HistKey.cipher.
proof. proc;while(0<=comparisons<=1152)(1152-comparisons);auto=> />;smt(). qed.
lemma hist_cipher_spec x0 y0 :
 hoare[HistKey.cipher:x=x0 /\ y=y0 ==>res.`1=(x0=y0) /\ res.`2=1152].
proof.
 proc;while(x=x0 /\ y=y0 /\ 0<=comparisons<=1152 /\
 same=hist_byte_prefix (fun i=>x0.[i]) (fun i=>y0.[i]) comparisons).
 + wp;skip=> /> &hr h0 hn hlt.
   have hs:=hist_byte_prefix_step (fun i=>x0.[i]) (fun i=>y0.[i]) comparisons{hr} h0.
   smt().
 auto=> />;smt(hist_byte_prefix_zero hist_cipher_full).
qed.
lemma hist_cipher_count : hoare[HistKey.cipher:true ==>res.`2=1152].
proof. proc;while(0<=comparisons<=1152);auto=> />;smt(). qed.
lemma hist_cipher_correct x0 y0 :
 phoare[HistKey.cipher:x=x0 /\ y=y0 ==>res.`1=(x0=y0) /\ res.`2=1152]=1%r.
proof. by conseq hist_cipher_lossless (hist_cipher_spec x0 y0). qed.
