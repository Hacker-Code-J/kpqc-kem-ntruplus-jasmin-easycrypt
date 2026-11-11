require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array768 Array1152 WArray1152 WArray1536.


require import NTRUPlus768PolyFromBytesChecked.
(* Each rt_work update is a ghost charge for the preceding concrete instruction.
   Each array parameter is copied into an owned buffer (3N primitive events: allocation, load, store). Whole-array assignments/returns also pay 3N; Array.set updates this owned buffer. These procedures preserve the original data path; no global state is added. *)
module RTFixedFromBytes = {
  proc jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes (rp:W16.t Array768.t,
                                                           ap:W8.t Array1152.t) : (W16.t Array768.t * W32.t) * int = {
    var rt_work:int;
    var fail_0:W32.t;
    var i:W64.t;
    var off:W64.t;
    var byte:W8.t;
    var t0:W16.t;
    var word:W16.t;
    var t1:W16.t;
    var wide:W32.t;
    var delta_0:W32.t;
    var _0:W64.t;
    rt_work <- 5760;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    i <- (W64.of_int 0);
    rt_work <- rt_work + 1;
    fail_0 <- (W32.of_int 0);
    rt_work <- rt_work + 1;
    rt_work <- rt_work + 2;
    while ((i \ult (W64.of_int (768 %/ 2)))) {
      off <- i;
      rt_work <- rt_work + 1;
      off <- (off `<<` (W8.of_int 1));
      rt_work <- rt_work + 2;
      off <- (off + i);
      rt_work <- rt_work + 2;
      byte <- ap.[(W64.to_uint off)];
      rt_work <- rt_work + 2;
      t0 <- (zeroextu16 byte);
      rt_work <- rt_work + 2;
      byte <- ap.[(W64.to_uint (off + (W64.of_int 1)))];
      rt_work <- rt_work + 3;
      word <- (zeroextu16 byte);
      rt_work <- rt_work + 2;
      word <- (word `<<` (W8.of_int 8));
      rt_work <- rt_work + 2;
      t0 <- (t0 `|` word);
      rt_work <- rt_work + 2;
      t0 <- (t0 `&` (W16.of_int 4095));
      rt_work <- rt_work + 2;
      t1 <- (zeroextu16 byte);
      rt_work <- rt_work + 2;
      t1 <- (t1 `>>` (W8.of_int 4));
      rt_work <- rt_work + 2;
      byte <- ap.[(W64.to_uint (off + (W64.of_int 2)))];
      rt_work <- rt_work + 3;
      word <- (zeroextu16 byte);
      rt_work <- rt_work + 2;
      word <- (word `<<` (W8.of_int 4));
      rt_work <- rt_work + 2;
      t1 <- (t1 `|` word);
      rt_work <- rt_work + 2;
      t1 <- (t1 `&` (W16.of_int 4095));
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint ((W64.of_int 2) * i))] <- t0;
      rt_work <- rt_work + 3;
      rp.[(W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 1)))] <- t1;
      rt_work <- rt_work + 4;
      wide <- (zeroextu32 t0);
      rt_work <- rt_work + 2;
      delta_0 <- (W32.of_int (3457 - 1));
      rt_work <- rt_work + 2;
      delta_0 <- (delta_0 - wide);
      rt_work <- rt_work + 2;
      fail_0 <- (fail_0 `|` delta_0);
      rt_work <- rt_work + 2;
      wide <- (zeroextu32 t1);
      rt_work <- rt_work + 2;
      delta_0 <- (W32.of_int (3457 - 1));
      rt_work <- rt_work + 2;
      delta_0 <- (delta_0 - wide);
      rt_work <- rt_work + 2;
      fail_0 <- (fail_0 `|` delta_0);
      rt_work <- rt_work + 2;
      i <- (i + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    fail_0 <- (fail_0 `>>` (W8.of_int 31));
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 2306;
    return ((rp, fail_0),rt_work);
  }
}.

lemma rt_fixed_u64_next (i:W64.t) : W64.to_uint i<2048 => W64.to_uint(i+W64.one)=W64.to_uint i+1.
proof. move=>h;rewrite W64.to_uintD_small /=;smt(W64.to_uint_cmp). qed.
lemma rt_fixed_u64_add (i:W64.t)(n:int) : 0<=W64.to_uint i<=768 => 0<=n<=768 => W64.to_uint(i+W64.of_int n)=W64.to_uint i+n.
proof. move=>hi hn;have hnE:W64.to_uint(W64.of_int n)=n. + rewrite W64.to_uint_small;smt(). rewrite W64.to_uintD_small. + rewrite hnE;smt(). by rewrite hnE. qed.
lemma rt_fixed_ult (i:W64.t)(n:int) : 0<=n<2048 => (i \ult W64.of_int n)=(W64.to_uint i<n).
proof. move=>hn;rewrite W64.ultE W64.to_uint_small;smt(). qed.
lemma rt_fixed_exit (i:W64.t)(n:int) : 0<=n<2048 => !(i \ult W64.of_int n) => W64.to_uint i<=n => W64.to_uint i=n.
proof. move=>hn;rewrite(rt_fixed_ult i n hn);smt(). qed.

lemma rt_fixed_frombytes_jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes_projection :
 equiv[RTFixedFromBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes ~ NTRUPlus768PolyFromBytesChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes :
 ={rp,ap} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,ap,i,fail_0}).
  + auto.
 auto.
qed.
lemma rt_fixed_frombytes_jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes_cost :
 hoare[RTFixedFromBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes : true ==> 0<=res.`2<=31881].
proof. proc.
 wp;while(0<=W64.to_uint i<=384 /\ 0<=rt_work<=5765+62*(W64.to_uint i-(0))).
  + auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> />;smt(rt_fixed_exit).
qed.
op rt_fixed_frombytes_bound:int = 31881.
lemma rt_fixed_frombytes_bound_cost : hoare[RTFixedFromBytes.jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes : true ==>0<=res.`2<=rt_fixed_frombytes_bound].
proof. exact rt_fixed_frombytes_jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes_cost. qed.
