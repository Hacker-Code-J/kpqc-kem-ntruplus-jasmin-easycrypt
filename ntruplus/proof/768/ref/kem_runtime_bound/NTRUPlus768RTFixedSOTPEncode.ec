require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array96 Array192 Array768 WArray96 WArray192 WArray1536.


require import NTRUPlus768PolySOTPEncodeChecked.
(* Each rt_work update is a ghost charge for the preceding concrete instruction.
   Each array parameter is copied into an owned buffer (3N primitive events: allocation, load, store). Whole-array assignments/returns also pay 3N; Array.set updates this owned buffer. These procedures preserve the original data path; no global state is added. *)
module RTFixedSOTPEncode = {
  proc jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode (rp:W16.t Array768.t,
                                                             msg:W8.t Array96.t,
                                                             buf:W8.t Array192.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var k:W64.t;
    var i:W64.t;
    var j:W8.t;
    var head:W8.t;
    var t1:W16.t;
    var t2:W16.t;
    var _0:W64.t;
    var _1:bool;
    var _2:bool;
    var _3:bool;
    var _4:bool;
    var _5:bool;
    var _6:bool;
    var _7:bool;
    var _8:bool;
    var _9:bool;
    var _10:bool;
    rt_work <- 3168;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    k <- (W64.of_int 0);
    rt_work <- rt_work + 1;
    rt_work <- rt_work + 2;
    while ((k \ult (W64.of_int 768))) {
      i <- k;
      rt_work <- rt_work + 1;
      i <- (i `>>` (W8.of_int 3));
      rt_work <- rt_work + 2;
      j <- (truncateu8 k);
      rt_work <- rt_work + 2;
      j <- (j `&` (W8.of_int 7));
      rt_work <- rt_work + 2;
      head <- buf.[(W64.to_uint i)];
      rt_work <- rt_work + 2;
      head <- (head `^` msg.[(W64.to_uint i)]);
      rt_work <- rt_work + 3;
      t1 <- (zeroextu16 head);
      rt_work <- rt_work + 2;
      t2 <- (zeroextu16 buf.[(W64.to_uint (i + (W64.of_int (768 %/ 8))))]);
      rt_work <- rt_work + 5;
      ( _1, _2, _3, _4, _5, t1) <- (SHR_16 t1 j);
      rt_work <- rt_work + 7;
      ( _6, _7, _8, _9, _10, t2) <- (SHR_16 t2 j);
      rt_work <- rt_work + 7;
      t1 <- (t1 `&` (W16.of_int 1));
      rt_work <- rt_work + 2;
      t2 <- (t2 `&` (W16.of_int 1));
      rt_work <- rt_work + 2;
      t1 <- (t1 - t2);
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint k)] <- t1;
      rt_work <- rt_work + 2;
      k <- (k + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
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

lemma rt_fixed_sotpencode_jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode_projection :
 equiv[RTFixedSOTPEncode.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode ~ NTRUPlus768PolySOTPEncodeChecked.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode :
 ={rp,msg,buf} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,msg,buf,k}).
  + auto.
 auto.
qed.
lemma rt_fixed_sotpencode_jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode_cost :
 hoare[RTFixedSOTPEncode.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode : true ==> 0<=res.`2<=40037].
proof. proc.
 wp;while(0<=W64.to_uint k<=768 /\ 0<=rt_work<=3172+45*(W64.to_uint k-(0))).
  + auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> />;smt(rt_fixed_exit).
qed.
op rt_fixed_sotpencode_bound:int = 40037.
lemma rt_fixed_sotpencode_bound_cost : hoare[RTFixedSOTPEncode.jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode : true ==>0<=res.`2<=rt_fixed_sotpencode_bound].
proof. exact rt_fixed_sotpencode_jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_encode_cost. qed.
