require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array768 WArray1536.


require import NTRUPlus768InvNTT.
(* Each rt_work update is a ghost charge for the preceding concrete instruction.
   Each array parameter is copied into an owned buffer (3N primitive events: allocation, load, store). Whole-array assignments/returns also pay 3N; Array.set updates this owned buffer. These procedures preserve the original data path; no global state is added. *)
module RTFixedInvNTT = {
  proc radix2_4____mul_i16 (a:W16.t, b:W16.t) : (W32.t) * int = {
    var rt_work:int;
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    rt_work <- 0;
    ad <- (sigextu32 a);
    rt_work <- rt_work + 2;
    bd <- (sigextu32 b);
    rt_work <- rt_work + 2;
    c <- (ad * bd);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (c,rt_work);
  }
  proc radix2_4____montgomery_reduce (a:W32.t) : (W16.t) * int = {
    var rt_work:int;
    var t:W16.t;
    var q:W32.t;
    var td:W32.t;
    var r:W32.t;
    rt_work <- 0;
    q <- (W32.of_int 3457);
    rt_work <- rt_work + 1;
    td <- a;
    rt_work <- rt_work + 1;
    td <- (td * (W32.of_int 12929));
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    td <- (sigextu32 t);
    rt_work <- rt_work + 2;
    r <- a;
    rt_work <- rt_work + 1;
    td <- (td * q);
    rt_work <- rt_work + 2;
    r <- (r - td);
    rt_work <- rt_work + 2;
    r <- (r `|>>` (W8.of_int 16));
    rt_work <- rt_work + 2;
    t <- (truncateu16 r);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (t,rt_work);
  }
  proc radix2_4____barrett_reduce (a:W16.t) : (W16.t) * int = {
    var rt_work:int;
    var t:W16.t;
    var v:W32.t;
    var td:W32.t;
    var q:W32.t;
    rt_work <- 0;
    v <- (W32.of_int 19412);
    rt_work <- rt_work + 1;
    td <- (sigextu32 a);
    rt_work <- rt_work + 2;
    td <- (td * v);
    rt_work <- rt_work + 2;
    td <- (td + (W32.of_int 33554432));
    rt_work <- rt_work + 2;
    td <- (td `|>>` (W8.of_int 26));
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    q <- (W32.of_int 3457);
    rt_work <- rt_work + 1;
    td <- (sigextu32 t);
    rt_work <- rt_work + 2;
    td <- (td * q);
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    t <- (a - t);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (t,rt_work);
  }
  proc radix2_4____invntt_radix2_4_block (rp:W16.t Array768.t, base:W64.t,
                                          zeta_0:W16.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var i:W64.t;
    var stop:W64.t;
    var low:W16.t;
    var high:W16.t;
    var wd:W32.t;
    var td:W32.t;
    var sum:W16.t;
    var diff:W16.t;
    var acc:W32.t;
    var prod:W16.t;
    var rt_call_radix2_4____barrett_reduce:(W16.t) * int;
    var rt_call_radix2_4____montgomery_reduce:(W16.t) * int;
    var rt_call_radix2_4____mul_i16:(W32.t) * int;
    rt_work <- 2304;
    i <- base;
    rt_work <- rt_work + 1;
    stop <- base;
    rt_work <- rt_work + 1;
    stop <- (stop + (W64.of_int 4));
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 2;
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      rt_work <- rt_work + 2;
      high <- rp.[(W64.to_uint (i + (W64.of_int 4)))];
      rt_work <- rt_work + 3;
      wd <- (sigextu32 low);
      rt_work <- rt_work + 2;
      td <- (sigextu32 high);
      rt_work <- rt_work + 2;
      wd <- (wd + td);
      rt_work <- rt_work + 2;
      sum <- (truncateu16 wd);
      rt_work <- rt_work + 2;
      wd <- (sigextu32 high);
      rt_work <- rt_work + 2;
      td <- (sigextu32 low);
      rt_work <- rt_work + 2;
      wd <- (wd - td);
      rt_work <- rt_work + 2;
      diff <- (truncateu16 wd);
      rt_work <- rt_work + 2;
      rt_call_radix2_4____barrett_reduce <@ radix2_4____barrett_reduce (sum);
      sum <- rt_call_radix2_4____barrett_reduce.`1;
      rt_work <- rt_work + rt_call_radix2_4____barrett_reduce.`2 + 3;
      rt_call_radix2_4____mul_i16 <@ radix2_4____mul_i16 (zeta_0, diff);
      acc <- rt_call_radix2_4____mul_i16.`1;
      rt_work <- rt_work + rt_call_radix2_4____mul_i16.`2 + 4;
      rt_call_radix2_4____montgomery_reduce <@ radix2_4____montgomery_reduce (acc);
      prod <- rt_call_radix2_4____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_radix2_4____montgomery_reduce.`2 + 3;
      rp.[(W64.to_uint i)] <- sum;
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint (i + (W64.of_int 4)))] <- prod;
      rt_work <- rt_work + 3;
      i <- (i + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 (
  rp:W16.t Array768.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var _0:W64.t;
    var rt_call_radix2_4____invntt_radix2_4_block:(W16.t Array768.t) * int;
    rt_work <- 2304;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 0), (W16.of_int (- 779)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 8), (W16.of_int 1588));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 16), (W16.of_int 892));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 24), (W16.of_int (- 1095)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 32), (W16.of_int (- 732)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 40), (W16.of_int 294));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 48), (W16.of_int (- 218)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 56), (W16.of_int 1221));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 64), (W16.of_int 858));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 72), (W16.of_int (- 968)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 80), (W16.of_int (- 1728)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 88), (W16.of_int 354));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 96), (W16.of_int 1108));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 104), (W16.of_int (- 275)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 112), (W16.of_int 1709));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 120), (W16.of_int 22));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 128), (W16.of_int (- 1681)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 136), (W16.of_int (- 940)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 144), (W16.of_int 1379));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 152), (W16.of_int 1458));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 160), (W16.of_int (- 124)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 168), (W16.of_int (- 1367)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 176), (W16.of_int 1531));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 184), (W16.of_int (- 1550)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 192), (W16.of_int 32));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 200), (W16.of_int (- 1543)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 208), (W16.of_int 274));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 216), (W16.of_int 400));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 224), (W16.of_int (- 1248)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 232), (W16.of_int 1408));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 240), (W16.of_int (- 315)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 248), (W16.of_int 1685));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 256), (W16.of_int (- 1626)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 264), (W16.of_int (- 27)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 272), (W16.of_int (- 1391)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 280), (W16.of_int 417));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 288), (W16.of_int 1188));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 296), (W16.of_int 1053));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 304), (W16.of_int (- 1063)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 312), (W16.of_int 1022));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 320), (W16.of_int 251));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 328), (W16.of_int 1401));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 336), (W16.of_int 1501));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 344), (W16.of_int 1409));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 352), (W16.of_int 582));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 360), (W16.of_int 673));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 368), (W16.of_int 230));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 376), (W16.of_int 361));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 384), (W16.of_int (- 1209)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 392), (W16.of_int 1364));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 400), (W16.of_int 235));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 408), (W16.of_int 444));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 416), (W16.of_int (- 1247)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 424), (W16.of_int (- 1341)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 432), (W16.of_int 1206));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 440), (W16.of_int (- 31)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 448), (W16.of_int 1660));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 456), (W16.of_int (- 100)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 464), (W16.of_int 1250));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 472), (W16.of_int 8));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 480), (W16.of_int 943));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 488), (W16.of_int 443));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 496), (W16.of_int (- 352)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 504), (W16.of_int (- 312)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 512), (W16.of_int 1212));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 520), (W16.of_int 760));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 528), (W16.of_int 871));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 536), (W16.of_int 1322));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 544), (W16.of_int 1130));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 552), (W16.of_int 1473));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 560), (W16.of_int 601));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 568), (W16.of_int 297));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 576), (W16.of_int 489));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 584), (W16.of_int 512));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 592), (W16.of_int 514));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 600), (W16.of_int 927));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 608), (W16.of_int 1671));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 616), (W16.of_int 774));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 624), (W16.of_int 696));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 632), (W16.of_int (- 1583)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 640), (W16.of_int 432));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 648), (W16.of_int 1640));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 656), (W16.of_int 242));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 664), (W16.of_int (- 1514)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 672), (W16.of_int 437));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 680), (W16.of_int 1723));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 688), (W16.of_int 933));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 696), (W16.of_int 277));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 704), (W16.of_int (- 1674)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 712), (W16.of_int 559));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 720), (W16.of_int 1655));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 728), (W16.of_int (- 183)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 736), (W16.of_int (- 397)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 744), (W16.of_int (- 1059)));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2310;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 752), (W16.of_int 1138));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_call_radix2_4____invntt_radix2_4_block <@ radix2_4____invntt_radix2_4_block (rp, (W64.of_int 760), (W16.of_int 223));
    rp <- rt_call_radix2_4____invntt_radix2_4_block.`1;
    rt_work <- rt_work + rt_call_radix2_4____invntt_radix2_4_block.`2 + 2309;
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc radix2_8____mul_i16 (a:W16.t, b:W16.t) : (W32.t) * int = {
    var rt_work:int;
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    rt_work <- 0;
    ad <- (sigextu32 a);
    rt_work <- rt_work + 2;
    bd <- (sigextu32 b);
    rt_work <- rt_work + 2;
    c <- (ad * bd);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (c,rt_work);
  }
  proc radix2_8____montgomery_reduce (a:W32.t) : (W16.t) * int = {
    var rt_work:int;
    var t:W16.t;
    var q:W32.t;
    var td:W32.t;
    var r:W32.t;
    rt_work <- 0;
    q <- (W32.of_int 3457);
    rt_work <- rt_work + 1;
    td <- a;
    rt_work <- rt_work + 1;
    td <- (td * (W32.of_int 12929));
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    td <- (sigextu32 t);
    rt_work <- rt_work + 2;
    r <- a;
    rt_work <- rt_work + 1;
    td <- (td * q);
    rt_work <- rt_work + 2;
    r <- (r - td);
    rt_work <- rt_work + 2;
    r <- (r `|>>` (W8.of_int 16));
    rt_work <- rt_work + 2;
    t <- (truncateu16 r);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (t,rt_work);
  }
  proc radix2_8____barrett_reduce (a:W16.t) : (W16.t) * int = {
    var rt_work:int;
    var t:W16.t;
    var v:W32.t;
    var td:W32.t;
    var q:W32.t;
    rt_work <- 0;
    v <- (W32.of_int 19412);
    rt_work <- rt_work + 1;
    td <- (sigextu32 a);
    rt_work <- rt_work + 2;
    td <- (td * v);
    rt_work <- rt_work + 2;
    td <- (td + (W32.of_int 33554432));
    rt_work <- rt_work + 2;
    td <- (td `|>>` (W8.of_int 26));
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    q <- (W32.of_int 3457);
    rt_work <- rt_work + 1;
    td <- (sigextu32 t);
    rt_work <- rt_work + 2;
    td <- (td * q);
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    t <- (a - t);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (t,rt_work);
  }
  proc radix2_8____invntt_radix2_8_block (rp:W16.t Array768.t, base:W64.t,
                                          zeta_0:W16.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var i:W64.t;
    var stop:W64.t;
    var low:W16.t;
    var high:W16.t;
    var wd:W32.t;
    var td:W32.t;
    var sum:W16.t;
    var diff:W16.t;
    var acc:W32.t;
    var prod:W16.t;
    var rt_call_radix2_8____barrett_reduce:(W16.t) * int;
    var rt_call_radix2_8____montgomery_reduce:(W16.t) * int;
    var rt_call_radix2_8____mul_i16:(W32.t) * int;
    rt_work <- 2304;
    i <- base;
    rt_work <- rt_work + 1;
    stop <- base;
    rt_work <- rt_work + 1;
    stop <- (stop + (W64.of_int 8));
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 2;
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      rt_work <- rt_work + 2;
      high <- rp.[(W64.to_uint (i + (W64.of_int 8)))];
      rt_work <- rt_work + 3;
      wd <- (sigextu32 low);
      rt_work <- rt_work + 2;
      td <- (sigextu32 high);
      rt_work <- rt_work + 2;
      wd <- (wd + td);
      rt_work <- rt_work + 2;
      sum <- (truncateu16 wd);
      rt_work <- rt_work + 2;
      wd <- (sigextu32 high);
      rt_work <- rt_work + 2;
      td <- (sigextu32 low);
      rt_work <- rt_work + 2;
      wd <- (wd - td);
      rt_work <- rt_work + 2;
      diff <- (truncateu16 wd);
      rt_work <- rt_work + 2;
      rt_call_radix2_8____barrett_reduce <@ radix2_8____barrett_reduce (sum);
      sum <- rt_call_radix2_8____barrett_reduce.`1;
      rt_work <- rt_work + rt_call_radix2_8____barrett_reduce.`2 + 3;
      rt_call_radix2_8____mul_i16 <@ radix2_8____mul_i16 (zeta_0, diff);
      acc <- rt_call_radix2_8____mul_i16.`1;
      rt_work <- rt_work + rt_call_radix2_8____mul_i16.`2 + 4;
      rt_call_radix2_8____montgomery_reduce <@ radix2_8____montgomery_reduce (acc);
      prod <- rt_call_radix2_8____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_radix2_8____montgomery_reduce.`2 + 3;
      rp.[(W64.to_uint i)] <- sum;
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint (i + (W64.of_int 8)))] <- prod;
      rt_work <- rt_work + 3;
      i <- (i + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 (
  rp:W16.t Array768.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var _0:W64.t;
    var rt_call_radix2_8____invntt_radix2_8_block:(W16.t Array768.t) * int;
    rt_work <- 2304;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 0), (W16.of_int 436));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 16), (W16.of_int 1015));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 32), (W16.of_int (- 588)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 48), (W16.of_int (- 1464)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 64), (W16.of_int 281));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 80), (W16.of_int (- 1558)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 96), (W16.of_int (- 1267)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 112), (W16.of_int (- 1673)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 128), (W16.of_int (- 1331)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 144), (W16.of_int 1413));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 160), (W16.of_int 1351));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 176), (W16.of_int (- 1081)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 192), (W16.of_int 54));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 208), (W16.of_int 205));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 224), (W16.of_int (- 834)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 240), (W16.of_int 675));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 256), (W16.of_int 630));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 272), (W16.of_int 87));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 288), (W16.of_int 641));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 304), (W16.of_int 961));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 320), (W16.of_int (- 371)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 336), (W16.of_int 64));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 352), (W16.of_int (- 800)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 368), (W16.of_int 548));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 384), (W16.of_int (- 992)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 400), (W16.of_int (- 565)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 416), (W16.of_int (- 1580)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 432), (W16.of_int 1428));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 448), (W16.of_int 661));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 464), (W16.of_int 1293));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 480), (W16.of_int (- 606)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 496), (W16.of_int (- 380)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 512), (W16.of_int (- 1507)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 528), (W16.of_int 1257));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 544), (W16.of_int (- 156)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 560), (W16.of_int 176));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 576), (W16.of_int 4));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 592), (W16.of_int (- 625)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 608), (W16.of_int (- 830)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 624), (W16.of_int 50));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 640), (W16.of_int 1199));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 656), (W16.of_int (- 1530)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 672), (W16.of_int (- 1617)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 688), (W16.of_int (- 569)));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2310;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 704), (W16.of_int 1637));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 720), (W16.of_int 901));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 736), (W16.of_int 837));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_call_radix2_8____invntt_radix2_8_block <@ radix2_8____invntt_radix2_8_block (rp, (W64.of_int 752), (W16.of_int 1449));
    rp <- rt_call_radix2_8____invntt_radix2_8_block.`1;
    rt_work <- rt_work + rt_call_radix2_8____invntt_radix2_8_block.`2 + 2309;
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc radix2_16____mul_i16 (a:W16.t, b:W16.t) : (W32.t) * int = {
    var rt_work:int;
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    rt_work <- 0;
    ad <- (sigextu32 a);
    rt_work <- rt_work + 2;
    bd <- (sigextu32 b);
    rt_work <- rt_work + 2;
    c <- (ad * bd);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (c,rt_work);
  }
  proc radix2_16____montgomery_reduce (a:W32.t) : (W16.t) * int = {
    var rt_work:int;
    var t:W16.t;
    var q:W32.t;
    var td:W32.t;
    var r:W32.t;
    rt_work <- 0;
    q <- (W32.of_int 3457);
    rt_work <- rt_work + 1;
    td <- a;
    rt_work <- rt_work + 1;
    td <- (td * (W32.of_int 12929));
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    td <- (sigextu32 t);
    rt_work <- rt_work + 2;
    r <- a;
    rt_work <- rt_work + 1;
    td <- (td * q);
    rt_work <- rt_work + 2;
    r <- (r - td);
    rt_work <- rt_work + 2;
    r <- (r `|>>` (W8.of_int 16));
    rt_work <- rt_work + 2;
    t <- (truncateu16 r);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (t,rt_work);
  }
  proc radix2_16____barrett_reduce (a:W16.t) : (W16.t) * int = {
    var rt_work:int;
    var t:W16.t;
    var v:W32.t;
    var td:W32.t;
    var q:W32.t;
    rt_work <- 0;
    v <- (W32.of_int 19412);
    rt_work <- rt_work + 1;
    td <- (sigextu32 a);
    rt_work <- rt_work + 2;
    td <- (td * v);
    rt_work <- rt_work + 2;
    td <- (td + (W32.of_int 33554432));
    rt_work <- rt_work + 2;
    td <- (td `|>>` (W8.of_int 26));
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    q <- (W32.of_int 3457);
    rt_work <- rt_work + 1;
    td <- (sigextu32 t);
    rt_work <- rt_work + 2;
    td <- (td * q);
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    t <- (a - t);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (t,rt_work);
  }
  proc radix2_16____invntt_radix2_16_block (rp:W16.t Array768.t, base:W64.t,
                                            zeta_0:W16.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var i:W64.t;
    var stop:W64.t;
    var low:W16.t;
    var high:W16.t;
    var wd:W32.t;
    var td:W32.t;
    var sum:W16.t;
    var diff:W16.t;
    var acc:W32.t;
    var prod:W16.t;
    var rt_call_radix2_16____barrett_reduce:(W16.t) * int;
    var rt_call_radix2_16____montgomery_reduce:(W16.t) * int;
    var rt_call_radix2_16____mul_i16:(W32.t) * int;
    rt_work <- 2304;
    i <- base;
    rt_work <- rt_work + 1;
    stop <- base;
    rt_work <- rt_work + 1;
    stop <- (stop + (W64.of_int 16));
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 2;
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      rt_work <- rt_work + 2;
      high <- rp.[(W64.to_uint (i + (W64.of_int 16)))];
      rt_work <- rt_work + 3;
      wd <- (sigextu32 low);
      rt_work <- rt_work + 2;
      td <- (sigextu32 high);
      rt_work <- rt_work + 2;
      wd <- (wd + td);
      rt_work <- rt_work + 2;
      sum <- (truncateu16 wd);
      rt_work <- rt_work + 2;
      wd <- (sigextu32 high);
      rt_work <- rt_work + 2;
      td <- (sigextu32 low);
      rt_work <- rt_work + 2;
      wd <- (wd - td);
      rt_work <- rt_work + 2;
      diff <- (truncateu16 wd);
      rt_work <- rt_work + 2;
      rt_call_radix2_16____barrett_reduce <@ radix2_16____barrett_reduce (sum);
      sum <- rt_call_radix2_16____barrett_reduce.`1;
      rt_work <- rt_work + rt_call_radix2_16____barrett_reduce.`2 + 3;
      rt_call_radix2_16____mul_i16 <@ radix2_16____mul_i16 (zeta_0, diff);
      acc <- rt_call_radix2_16____mul_i16.`1;
      rt_work <- rt_work + rt_call_radix2_16____mul_i16.`2 + 4;
      rt_call_radix2_16____montgomery_reduce <@ radix2_16____montgomery_reduce (acc);
      prod <- rt_call_radix2_16____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_radix2_16____montgomery_reduce.`2 + 3;
      rp.[(W64.to_uint i)] <- sum;
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint (i + (W64.of_int 16)))] <- prod;
      rt_work <- rt_work + 3;
      i <- (i + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 (
  rp:W16.t Array768.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var _0:W64.t;
    var rt_call_radix2_16____invntt_radix2_16_block:(W16.t Array768.t) * int;
    rt_work <- 2304;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 0), (W16.of_int 1058));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2309;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 32), (W16.of_int (- 1105)));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2310;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 64), (W16.of_int 1713));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2309;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 96), (W16.of_int (- 603)));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2310;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 128), (W16.of_int 387));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2309;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 160), (W16.of_int 893));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2309;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 192), (W16.of_int 937));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2309;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 224), (W16.of_int (- 348)));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2310;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 256), (W16.of_int (- 757)));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2310;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 288), (W16.of_int (- 121)));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2310;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 320), (W16.of_int (- 216)));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2310;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 352), (W16.of_int (- 820)));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2310;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 384), (W16.of_int 39));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2309;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 416), (W16.of_int (- 44)));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2310;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 448), (W16.of_int 550));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2309;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 480), (W16.of_int (- 1241)));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2310;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 512), (W16.of_int (- 1577)));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2310;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 544), (W16.of_int 95));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2309;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 576), (W16.of_int 541));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2309;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 608), (W16.of_int (- 699)));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2310;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 640), (W16.of_int 655));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2309;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 672), (W16.of_int 502));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2309;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 704), (W16.of_int 639));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2309;
    rt_call_radix2_16____invntt_radix2_16_block <@ radix2_16____invntt_radix2_16_block (rp, (W64.of_int 736), (W16.of_int (- 455)));
    rp <- rt_call_radix2_16____invntt_radix2_16_block.`1;
    rt_work <- rt_work + rt_call_radix2_16____invntt_radix2_16_block.`2 + 2310;
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc radix2_32____mul_i16 (a:W16.t, b:W16.t) : (W32.t) * int = {
    var rt_work:int;
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    rt_work <- 0;
    ad <- (sigextu32 a);
    rt_work <- rt_work + 2;
    bd <- (sigextu32 b);
    rt_work <- rt_work + 2;
    c <- (ad * bd);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (c,rt_work);
  }
  proc radix2_32____montgomery_reduce (a:W32.t) : (W16.t) * int = {
    var rt_work:int;
    var t:W16.t;
    var q:W32.t;
    var td:W32.t;
    var r:W32.t;
    rt_work <- 0;
    q <- (W32.of_int 3457);
    rt_work <- rt_work + 1;
    td <- a;
    rt_work <- rt_work + 1;
    td <- (td * (W32.of_int 12929));
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    td <- (sigextu32 t);
    rt_work <- rt_work + 2;
    r <- a;
    rt_work <- rt_work + 1;
    td <- (td * q);
    rt_work <- rt_work + 2;
    r <- (r - td);
    rt_work <- rt_work + 2;
    r <- (r `|>>` (W8.of_int 16));
    rt_work <- rt_work + 2;
    t <- (truncateu16 r);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (t,rt_work);
  }
  proc radix2_32____barrett_reduce (a:W16.t) : (W16.t) * int = {
    var rt_work:int;
    var t:W16.t;
    var v:W32.t;
    var td:W32.t;
    var q:W32.t;
    rt_work <- 0;
    v <- (W32.of_int 19412);
    rt_work <- rt_work + 1;
    td <- (sigextu32 a);
    rt_work <- rt_work + 2;
    td <- (td * v);
    rt_work <- rt_work + 2;
    td <- (td + (W32.of_int 33554432));
    rt_work <- rt_work + 2;
    td <- (td `|>>` (W8.of_int 26));
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    q <- (W32.of_int 3457);
    rt_work <- rt_work + 1;
    td <- (sigextu32 t);
    rt_work <- rt_work + 2;
    td <- (td * q);
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    t <- (a - t);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (t,rt_work);
  }
  proc radix2_32____invntt_radix2_32_block (rp:W16.t Array768.t, base:W64.t,
                                            zeta_0:W16.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var i:W64.t;
    var stop:W64.t;
    var low:W16.t;
    var high:W16.t;
    var wd:W32.t;
    var td:W32.t;
    var sum:W16.t;
    var diff:W16.t;
    var acc:W32.t;
    var prod:W16.t;
    var rt_call_radix2_32____barrett_reduce:(W16.t) * int;
    var rt_call_radix2_32____montgomery_reduce:(W16.t) * int;
    var rt_call_radix2_32____mul_i16:(W32.t) * int;
    rt_work <- 2304;
    i <- base;
    rt_work <- rt_work + 1;
    stop <- base;
    rt_work <- rt_work + 1;
    stop <- (stop + (W64.of_int 32));
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 2;
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      rt_work <- rt_work + 2;
      high <- rp.[(W64.to_uint (i + (W64.of_int 32)))];
      rt_work <- rt_work + 3;
      wd <- (sigextu32 low);
      rt_work <- rt_work + 2;
      td <- (sigextu32 high);
      rt_work <- rt_work + 2;
      wd <- (wd + td);
      rt_work <- rt_work + 2;
      sum <- (truncateu16 wd);
      rt_work <- rt_work + 2;
      wd <- (sigextu32 high);
      rt_work <- rt_work + 2;
      td <- (sigextu32 low);
      rt_work <- rt_work + 2;
      wd <- (wd - td);
      rt_work <- rt_work + 2;
      diff <- (truncateu16 wd);
      rt_work <- rt_work + 2;
      rt_call_radix2_32____barrett_reduce <@ radix2_32____barrett_reduce (sum);
      sum <- rt_call_radix2_32____barrett_reduce.`1;
      rt_work <- rt_work + rt_call_radix2_32____barrett_reduce.`2 + 3;
      rt_call_radix2_32____mul_i16 <@ radix2_32____mul_i16 (zeta_0, diff);
      acc <- rt_call_radix2_32____mul_i16.`1;
      rt_work <- rt_work + rt_call_radix2_32____mul_i16.`2 + 4;
      rt_call_radix2_32____montgomery_reduce <@ radix2_32____montgomery_reduce (acc);
      prod <- rt_call_radix2_32____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_radix2_32____montgomery_reduce.`2 + 3;
      rp.[(W64.to_uint i)] <- sum;
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint (i + (W64.of_int 32)))] <- prod;
      rt_work <- rt_work + 3;
      i <- (i + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32 (
  rp:W16.t Array768.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var _0:W64.t;
    var rt_call_radix2_32____invntt_radix2_32_block:(W16.t Array768.t) * int;
    rt_work <- 2304;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    rt_call_radix2_32____invntt_radix2_32_block <@ radix2_32____invntt_radix2_32_block (rp, (W64.of_int 0), (W16.of_int 395));
    rp <- rt_call_radix2_32____invntt_radix2_32_block.`1;
    rt_work <- rt_work + rt_call_radix2_32____invntt_radix2_32_block.`2 + 2309;
    rt_call_radix2_32____invntt_radix2_32_block <@ radix2_32____invntt_radix2_32_block (rp, (W64.of_int 64), (W16.of_int (- 357)));
    rp <- rt_call_radix2_32____invntt_radix2_32_block.`1;
    rt_work <- rt_work + rt_call_radix2_32____invntt_radix2_32_block.`2 + 2310;
    rt_call_radix2_32____invntt_radix2_32_block <@ radix2_32____invntt_radix2_32_block (rp, (W64.of_int 128), (W16.of_int (- 1521)));
    rp <- rt_call_radix2_32____invntt_radix2_32_block.`1;
    rt_work <- rt_work + rt_call_radix2_32____invntt_radix2_32_block.`2 + 2310;
    rt_call_radix2_32____invntt_radix2_32_block <@ radix2_32____invntt_radix2_32_block (rp, (W64.of_int 192), (W16.of_int 1716));
    rp <- rt_call_radix2_32____invntt_radix2_32_block.`1;
    rt_work <- rt_work + rt_call_radix2_32____invntt_radix2_32_block.`2 + 2309;
    rt_call_radix2_32____invntt_radix2_32_block <@ radix2_32____invntt_radix2_32_block (rp, (W64.of_int 256), (W16.of_int (- 1346)));
    rp <- rt_call_radix2_32____invntt_radix2_32_block.`1;
    rt_work <- rt_work + rt_call_radix2_32____invntt_radix2_32_block.`2 + 2310;
    rt_call_radix2_32____invntt_radix2_32_block <@ radix2_32____invntt_radix2_32_block (rp, (W64.of_int 320), (W16.of_int 1164));
    rp <- rt_call_radix2_32____invntt_radix2_32_block.`1;
    rt_work <- rt_work + rt_call_radix2_32____invntt_radix2_32_block.`2 + 2309;
    rt_call_radix2_32____invntt_radix2_32_block <@ radix2_32____invntt_radix2_32_block (rp, (W64.of_int 384), (W16.of_int 222));
    rp <- rt_call_radix2_32____invntt_radix2_32_block.`1;
    rt_work <- rt_work + rt_call_radix2_32____invntt_radix2_32_block.`2 + 2309;
    rt_call_radix2_32____invntt_radix2_32_block <@ radix2_32____invntt_radix2_32_block (rp, (W64.of_int 448), (W16.of_int 1611));
    rp <- rt_call_radix2_32____invntt_radix2_32_block.`1;
    rt_work <- rt_work + rt_call_radix2_32____invntt_radix2_32_block.`2 + 2309;
    rt_call_radix2_32____invntt_radix2_32_block <@ radix2_32____invntt_radix2_32_block (rp, (W64.of_int 512), (W16.of_int (- 1590)));
    rp <- rt_call_radix2_32____invntt_radix2_32_block.`1;
    rt_work <- rt_work + rt_call_radix2_32____invntt_radix2_32_block.`2 + 2310;
    rt_call_radix2_32____invntt_radix2_32_block <@ radix2_32____invntt_radix2_32_block (rp, (W64.of_int 576), (W16.of_int 1262));
    rp <- rt_call_radix2_32____invntt_radix2_32_block.`1;
    rt_work <- rt_work + rt_call_radix2_32____invntt_radix2_32_block.`2 + 2309;
    rt_call_radix2_32____invntt_radix2_32_block <@ radix2_32____invntt_radix2_32_block (rp, (W64.of_int 640), (W16.of_int 1484));
    rp <- rt_call_radix2_32____invntt_radix2_32_block.`1;
    rt_work <- rt_work + rt_call_radix2_32____invntt_radix2_32_block.`2 + 2309;
    rt_call_radix2_32____invntt_radix2_32_block <@ radix2_32____invntt_radix2_32_block (rp, (W64.of_int 704), (W16.of_int (- 256)));
    rp <- rt_call_radix2_32____invntt_radix2_32_block.`1;
    rt_work <- rt_work + rt_call_radix2_32____invntt_radix2_32_block.`2 + 2310;
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc radix2_64____mul_i16 (a:W16.t, b:W16.t) : (W32.t) * int = {
    var rt_work:int;
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    rt_work <- 0;
    ad <- (sigextu32 a);
    rt_work <- rt_work + 2;
    bd <- (sigextu32 b);
    rt_work <- rt_work + 2;
    c <- (ad * bd);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (c,rt_work);
  }
  proc radix2_64____montgomery_reduce (a:W32.t) : (W16.t) * int = {
    var rt_work:int;
    var t:W16.t;
    var q:W32.t;
    var td:W32.t;
    var r:W32.t;
    rt_work <- 0;
    q <- (W32.of_int 3457);
    rt_work <- rt_work + 1;
    td <- a;
    rt_work <- rt_work + 1;
    td <- (td * (W32.of_int 12929));
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    td <- (sigextu32 t);
    rt_work <- rt_work + 2;
    r <- a;
    rt_work <- rt_work + 1;
    td <- (td * q);
    rt_work <- rt_work + 2;
    r <- (r - td);
    rt_work <- rt_work + 2;
    r <- (r `|>>` (W8.of_int 16));
    rt_work <- rt_work + 2;
    t <- (truncateu16 r);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (t,rt_work);
  }
  proc radix2_64____barrett_reduce (a:W16.t) : (W16.t) * int = {
    var rt_work:int;
    var t:W16.t;
    var v:W32.t;
    var td:W32.t;
    var q:W32.t;
    rt_work <- 0;
    v <- (W32.of_int 19412);
    rt_work <- rt_work + 1;
    td <- (sigextu32 a);
    rt_work <- rt_work + 2;
    td <- (td * v);
    rt_work <- rt_work + 2;
    td <- (td + (W32.of_int 33554432));
    rt_work <- rt_work + 2;
    td <- (td `|>>` (W8.of_int 26));
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    q <- (W32.of_int 3457);
    rt_work <- rt_work + 1;
    td <- (sigextu32 t);
    rt_work <- rt_work + 2;
    td <- (td * q);
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    t <- (a - t);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (t,rt_work);
  }
  proc radix2_64____invntt_radix2_64_block (rp:W16.t Array768.t, base:W64.t,
                                            zeta_0:W16.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var i:W64.t;
    var stop:W64.t;
    var low:W16.t;
    var high:W16.t;
    var wd:W32.t;
    var td:W32.t;
    var sum:W16.t;
    var diff:W16.t;
    var acc:W32.t;
    var prod:W16.t;
    var rt_call_radix2_64____barrett_reduce:(W16.t) * int;
    var rt_call_radix2_64____montgomery_reduce:(W16.t) * int;
    var rt_call_radix2_64____mul_i16:(W32.t) * int;
    rt_work <- 2304;
    i <- base;
    rt_work <- rt_work + 1;
    stop <- base;
    rt_work <- rt_work + 1;
    stop <- (stop + (W64.of_int 64));
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 2;
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      rt_work <- rt_work + 2;
      high <- rp.[(W64.to_uint (i + (W64.of_int 64)))];
      rt_work <- rt_work + 3;
      wd <- (sigextu32 low);
      rt_work <- rt_work + 2;
      td <- (sigextu32 high);
      rt_work <- rt_work + 2;
      wd <- (wd + td);
      rt_work <- rt_work + 2;
      sum <- (truncateu16 wd);
      rt_work <- rt_work + 2;
      wd <- (sigextu32 high);
      rt_work <- rt_work + 2;
      td <- (sigextu32 low);
      rt_work <- rt_work + 2;
      wd <- (wd - td);
      rt_work <- rt_work + 2;
      diff <- (truncateu16 wd);
      rt_work <- rt_work + 2;
      rt_call_radix2_64____barrett_reduce <@ radix2_64____barrett_reduce (sum);
      sum <- rt_call_radix2_64____barrett_reduce.`1;
      rt_work <- rt_work + rt_call_radix2_64____barrett_reduce.`2 + 3;
      rt_call_radix2_64____mul_i16 <@ radix2_64____mul_i16 (zeta_0, diff);
      acc <- rt_call_radix2_64____mul_i16.`1;
      rt_work <- rt_work + rt_call_radix2_64____mul_i16.`2 + 4;
      rt_call_radix2_64____montgomery_reduce <@ radix2_64____montgomery_reduce (acc);
      prod <- rt_call_radix2_64____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_radix2_64____montgomery_reduce.`2 + 3;
      rp.[(W64.to_uint i)] <- sum;
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint (i + (W64.of_int 64)))] <- prod;
      rt_work <- rt_work + 3;
      i <- (i + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 (
  rp:W16.t Array768.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var _0:W64.t;
    var rt_call_radix2_64____invntt_radix2_64_block:(W16.t Array768.t) * int;
    rt_work <- 2304;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    rt_call_radix2_64____invntt_radix2_64_block <@ radix2_64____invntt_radix2_64_block (rp, (W64.of_int 0), (W16.of_int (- 867)));
    rp <- rt_call_radix2_64____invntt_radix2_64_block.`1;
    rt_work <- rt_work + rt_call_radix2_64____invntt_radix2_64_block.`2 + 2310;
    rt_call_radix2_64____invntt_radix2_64_block <@ radix2_64____invntt_radix2_64_block (rp, (W64.of_int 128), (W16.of_int (- 1124)));
    rp <- rt_call_radix2_64____invntt_radix2_64_block.`1;
    rt_work <- rt_work + rt_call_radix2_64____invntt_radix2_64_block.`2 + 2310;
    rt_call_radix2_64____invntt_radix2_64_block <@ radix2_64____invntt_radix2_64_block (rp, (W64.of_int 256), (W16.of_int (- 257)));
    rp <- rt_call_radix2_64____invntt_radix2_64_block.`1;
    rt_work <- rt_work + rt_call_radix2_64____invntt_radix2_64_block.`2 + 2310;
    rt_call_radix2_64____invntt_radix2_64_block <@ radix2_64____invntt_radix2_64_block (rp, (W64.of_int 384), (W16.of_int (- 723)));
    rp <- rt_call_radix2_64____invntt_radix2_64_block.`1;
    rt_work <- rt_work + rt_call_radix2_64____invntt_radix2_64_block.`2 + 2310;
    rt_call_radix2_64____invntt_radix2_64_block <@ radix2_64____invntt_radix2_64_block (rp, (W64.of_int 512), (W16.of_int (- 722)));
    rp <- rt_call_radix2_64____invntt_radix2_64_block.`1;
    rt_work <- rt_work + rt_call_radix2_64____invntt_radix2_64_block.`2 + 2310;
    rt_call_radix2_64____invntt_radix2_64_block <@ radix2_64____invntt_radix2_64_block (rp, (W64.of_int 640), (W16.of_int 1));
    rp <- rt_call_radix2_64____invntt_radix2_64_block.`1;
    rt_work <- rt_work + rt_call_radix2_64____invntt_radix2_64_block.`2 + 2309;
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc radix3____mul_i16 (a:W16.t, b:W16.t) : (W32.t) * int = {
    var rt_work:int;
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    rt_work <- 0;
    ad <- (sigextu32 a);
    rt_work <- rt_work + 2;
    bd <- (sigextu32 b);
    rt_work <- rt_work + 2;
    c <- (ad * bd);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (c,rt_work);
  }
  proc radix3____montgomery_reduce (a:W32.t) : (W16.t) * int = {
    var rt_work:int;
    var t:W16.t;
    var q:W32.t;
    var td:W32.t;
    var r:W32.t;
    rt_work <- 0;
    q <- (W32.of_int 3457);
    rt_work <- rt_work + 1;
    td <- a;
    rt_work <- rt_work + 1;
    td <- (td * (W32.of_int 12929));
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    td <- (sigextu32 t);
    rt_work <- rt_work + 2;
    r <- a;
    rt_work <- rt_work + 1;
    td <- (td * q);
    rt_work <- rt_work + 2;
    r <- (r - td);
    rt_work <- rt_work + 2;
    r <- (r `|>>` (W8.of_int 16));
    rt_work <- rt_work + 2;
    t <- (truncateu16 r);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (t,rt_work);
  }
  proc radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 (rp:W16.t Array768.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var i:W64.t;
    var a0:W16.t;
    var a1:W16.t;
    var a2:W16.t;
    var td:W16.t;
    var acc:W32.t;
    var t1:W16.t;
    var t2:W16.t;
    var t3:W16.t;
    var r0:W16.t;
    var _0:W64.t;
    var rt_call_radix3____montgomery_reduce:(W16.t) * int;
    var rt_call_radix3____mul_i16:(W32.t) * int;
    rt_work <- 2304;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    i <- (W64.of_int 0);
    rt_work <- rt_work + 1;
    rt_work <- rt_work + 2;
    while ((i \ult (W64.of_int 128))) {
      a0 <- rp.[(W64.to_uint i)];
      rt_work <- rt_work + 2;
      a1 <- rp.[(W64.to_uint (i + (W64.of_int 128)))];
      rt_work <- rt_work + 3;
      a2 <- rp.[(W64.to_uint (i + (W64.of_int 256)))];
      rt_work <- rt_work + 3;
      td <- a1;
      rt_work <- rt_work + 1;
      td <- (td - a0);
      rt_work <- rt_work + 2;
      rt_call_radix3____mul_i16 <@ radix3____mul_i16 ((W16.of_int (- 886)), td);
      acc <- rt_call_radix3____mul_i16.`1;
      rt_work <- rt_work + rt_call_radix3____mul_i16.`2 + 5;
      rt_call_radix3____montgomery_reduce <@ radix3____montgomery_reduce (acc);
      t1 <- rt_call_radix3____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_radix3____montgomery_reduce.`2 + 3;
      td <- a2;
      rt_work <- rt_work + 1;
      td <- (td - a0);
      rt_work <- rt_work + 2;
      td <- (td + t1);
      rt_work <- rt_work + 2;
      rt_call_radix3____mul_i16 <@ radix3____mul_i16 ((W16.of_int (- 708)), td);
      acc <- rt_call_radix3____mul_i16.`1;
      rt_work <- rt_work + rt_call_radix3____mul_i16.`2 + 5;
      rt_call_radix3____montgomery_reduce <@ radix3____montgomery_reduce (acc);
      t2 <- rt_call_radix3____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_radix3____montgomery_reduce.`2 + 3;
      td <- a2;
      rt_work <- rt_work + 1;
      td <- (td - a1);
      rt_work <- rt_work + 2;
      td <- (td - t1);
      rt_work <- rt_work + 2;
      rt_call_radix3____mul_i16 <@ radix3____mul_i16 ((W16.of_int 682), td);
      acc <- rt_call_radix3____mul_i16.`1;
      rt_work <- rt_work + rt_call_radix3____mul_i16.`2 + 4;
      rt_call_radix3____montgomery_reduce <@ radix3____montgomery_reduce (acc);
      t3 <- rt_call_radix3____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_radix3____montgomery_reduce.`2 + 3;
      r0 <- a0;
      rt_work <- rt_work + 1;
      r0 <- (r0 + a1);
      rt_work <- rt_work + 2;
      r0 <- (r0 + a2);
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint i)] <- r0;
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint (i + (W64.of_int 128)))] <- t2;
      rt_work <- rt_work + 3;
      rp.[(W64.to_uint (i + (W64.of_int 256)))] <- t3;
      rt_work <- rt_work + 3;
      i <- (i + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    i <- (W64.of_int 384);
    rt_work <- rt_work + 1;
    rt_work <- rt_work + 2;
    while ((i \ult (W64.of_int 512))) {
      a0 <- rp.[(W64.to_uint i)];
      rt_work <- rt_work + 2;
      a1 <- rp.[(W64.to_uint (i + (W64.of_int 128)))];
      rt_work <- rt_work + 3;
      a2 <- rp.[(W64.to_uint (i + (W64.of_int 256)))];
      rt_work <- rt_work + 3;
      td <- a1;
      rt_work <- rt_work + 1;
      td <- (td - a0);
      rt_work <- rt_work + 2;
      rt_call_radix3____mul_i16 <@ radix3____mul_i16 ((W16.of_int (- 886)), td);
      acc <- rt_call_radix3____mul_i16.`1;
      rt_work <- rt_work + rt_call_radix3____mul_i16.`2 + 5;
      rt_call_radix3____montgomery_reduce <@ radix3____montgomery_reduce (acc);
      t1 <- rt_call_radix3____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_radix3____montgomery_reduce.`2 + 3;
      td <- a2;
      rt_work <- rt_work + 1;
      td <- (td - a0);
      rt_work <- rt_work + 2;
      td <- (td + t1);
      rt_work <- rt_work + 2;
      rt_call_radix3____mul_i16 <@ radix3____mul_i16 ((W16.of_int (- 682)), td);
      acc <- rt_call_radix3____mul_i16.`1;
      rt_work <- rt_work + rt_call_radix3____mul_i16.`2 + 5;
      rt_call_radix3____montgomery_reduce <@ radix3____montgomery_reduce (acc);
      t2 <- rt_call_radix3____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_radix3____montgomery_reduce.`2 + 3;
      td <- a2;
      rt_work <- rt_work + 1;
      td <- (td - a1);
      rt_work <- rt_work + 2;
      td <- (td - t1);
      rt_work <- rt_work + 2;
      rt_call_radix3____mul_i16 <@ radix3____mul_i16 ((W16.of_int (- 248)), td);
      acc <- rt_call_radix3____mul_i16.`1;
      rt_work <- rt_work + rt_call_radix3____mul_i16.`2 + 5;
      rt_call_radix3____montgomery_reduce <@ radix3____montgomery_reduce (acc);
      t3 <- rt_call_radix3____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_radix3____montgomery_reduce.`2 + 3;
      r0 <- a0;
      rt_work <- rt_work + 1;
      r0 <- (r0 + a1);
      rt_work <- rt_work + 2;
      r0 <- (r0 + a2);
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint i)] <- r0;
      rt_work <- rt_work + 2;
      rp.[(W64.to_uint (i + (W64.of_int 128)))] <- t2;
      rt_work <- rt_work + 3;
      rp.[(W64.to_uint (i + (W64.of_int 256)))] <- t3;
      rt_work <- rt_work + 3;
      i <- (i + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc final____mul_i16 (a:W16.t, b:W16.t) : (W32.t) * int = {
    var rt_work:int;
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    rt_work <- 0;
    ad <- (sigextu32 a);
    rt_work <- rt_work + 2;
    bd <- (sigextu32 b);
    rt_work <- rt_work + 2;
    c <- (ad * bd);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (c,rt_work);
  }
  proc final____montgomery_reduce (a:W32.t) : (W16.t) * int = {
    var rt_work:int;
    var t:W16.t;
    var q:W32.t;
    var td:W32.t;
    var r:W32.t;
    rt_work <- 0;
    q <- (W32.of_int 3457);
    rt_work <- rt_work + 1;
    td <- a;
    rt_work <- rt_work + 1;
    td <- (td * (W32.of_int 12929));
    rt_work <- rt_work + 2;
    t <- (truncateu16 td);
    rt_work <- rt_work + 2;
    td <- (sigextu32 t);
    rt_work <- rt_work + 2;
    r <- a;
    rt_work <- rt_work + 1;
    td <- (td * q);
    rt_work <- rt_work + 2;
    r <- (r - td);
    rt_work <- rt_work + 2;
    r <- (r `|>>` (W8.of_int 16));
    rt_work <- rt_work + 2;
    t <- (truncateu16 r);
    rt_work <- rt_work + 2;
    rt_work <- rt_work + 1;
    return (t,rt_work);
  }
  proc final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final (rp:W16.t Array768.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var aux:W16.t;
    var i:W64.t;
    var lo:W16.t;
    var hi:W16.t;
    var t1:W16.t;
    var td:W16.t;
    var acc:W32.t;
    var t2:W16.t;
    var _0:W64.t;
    var rt_call_final____montgomery_reduce:(W16.t) * int;
    var rt_call_final____mul_i16:(W32.t) * int;
    rt_work <- 2304;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    i <- (W64.of_int 0);
    rt_work <- rt_work + 1;
    rt_work <- rt_work + 2;
    while ((i \ult (W64.of_int (768 %/ 2)))) {
      lo <- rp.[(W64.to_uint i)];
      rt_work <- rt_work + 2;
      hi <- rp.[(W64.to_uint (i + (W64.of_int (768 %/ 2))))];
      rt_work <- rt_work + 4;
      t1 <- lo;
      rt_work <- rt_work + 1;
      t1 <- (t1 + hi);
      rt_work <- rt_work + 2;
      td <- lo;
      rt_work <- rt_work + 1;
      td <- (td - hi);
      rt_work <- rt_work + 2;
      rt_call_final____mul_i16 <@ final____mul_i16 ((W16.of_int (- 1665)), td);
      acc <- rt_call_final____mul_i16.`1;
      rt_work <- rt_work + rt_call_final____mul_i16.`2 + 5;
      rt_call_final____montgomery_reduce <@ final____montgomery_reduce (acc);
      t2 <- rt_call_final____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_final____montgomery_reduce.`2 + 3;
      td <- t1;
      rt_work <- rt_work + 1;
      td <- (td - t2);
      rt_work <- rt_work + 2;
      rt_call_final____mul_i16 <@ final____mul_i16 ((W16.of_int (- 811)), td);
      acc <- rt_call_final____mul_i16.`1;
      rt_work <- rt_work + rt_call_final____mul_i16.`2 + 5;
      rt_call_final____montgomery_reduce <@ final____montgomery_reduce (acc);
      aux <- rt_call_final____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_final____montgomery_reduce.`2 + 3;
      rp.[(W64.to_uint i)] <- aux;
      rt_work <- rt_work + 2;
      rt_call_final____mul_i16 <@ final____mul_i16 ((W16.of_int (- 1622)), t2);
      acc <- rt_call_final____mul_i16.`1;
      rt_work <- rt_work + rt_call_final____mul_i16.`2 + 5;
      rt_call_final____montgomery_reduce <@ final____montgomery_reduce (acc);
      aux <- rt_call_final____montgomery_reduce.`1;
      rt_work <- rt_work + rt_call_final____montgomery_reduce.`2 + 3;
      rp.[(W64.to_uint (i + (W64.of_int (768 %/ 2))))] <- aux;
      rt_work <- rt_work + 4;
      i <- (i + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc __invntt_copy (rp:W16.t Array768.t, ap:W16.t Array768.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var i:W64.t;
    var _0:W64.t;
    rt_work <- 4608;
    _0 <- (init_msf);
    rt_work <- rt_work + 1;
    i <- (W64.of_int 0);
    rt_work <- rt_work + 1;
    rt_work <- rt_work + 2;
    while ((i \ult (W64.of_int 768))) {
      rp.[(W64.to_uint i)] <- ap.[(W64.to_uint i)];
      rt_work <- rt_work + 3;
      i <- (i + (W64.of_int 1));
      rt_work <- rt_work + 2;
      rt_work <- rt_work + 2;
    }
    rt_work <- rt_work + 2305;
    return (rp,rt_work);
  }
  proc jade_ntruplus_ntruplus768_amd64_ref_invntt (rp:W16.t Array768.t,
                                                   ap:W16.t Array768.t) : (W16.t Array768.t) * int = {
    var rt_work:int;
    var rt_call___invntt_copy:(W16.t Array768.t) * int;
    var rt_call_final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final:(W16.t Array768.t) * int;
    var rt_call_radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16:(W16.t Array768.t) * int;
    var rt_call_radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32:(W16.t Array768.t) * int;
    var rt_call_radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4:(W16.t Array768.t) * int;
    var rt_call_radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64:(W16.t Array768.t) * int;
    var rt_call_radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8:(W16.t Array768.t) * int;
    var rt_call_radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3:(W16.t Array768.t) * int;
    rt_work <- 4608;
    rt_call___invntt_copy <@ __invntt_copy (rp, ap);
    rp <- rt_call___invntt_copy.`1;
    rt_work <- rt_work + rt_call___invntt_copy.`2 + 2308;
    rt_call_radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 <@ radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 (rp);
    rp <- rt_call_radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4.`1;
    rt_work <- rt_work + rt_call_radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4.`2 + 2307;
    rt_call_radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 <@ radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 (rp);
    rp <- rt_call_radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8.`1;
    rt_work <- rt_work + rt_call_radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8.`2 + 2307;
    rt_call_radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 <@ radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 ( rp);
    rp <- rt_call_radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16.`1;
    rt_work <- rt_work + rt_call_radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16.`2 + 2307;
    rt_call_radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32 <@ radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32 ( rp);
    rp <- rt_call_radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32.`1;
    rt_work <- rt_work + rt_call_radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32.`2 + 2307;
    rt_call_radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 <@ radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 ( rp);
    rp <- rt_call_radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64.`1;
    rt_work <- rt_work + rt_call_radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64.`2 + 2307;
    rt_call_radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 <@ radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 (rp);
    rp <- rt_call_radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3.`1;
    rt_work <- rt_work + rt_call_radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3.`2 + 2307;
    rt_call_final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final <@ final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final (rp);
    rp <- rt_call_final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final.`1;
    rt_work <- rt_work + rt_call_final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final.`2 + 2307;
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

lemma rt_fixed_invntt_radix2_4____mul_i16_projection :
 equiv[RTFixedInvNTT.radix2_4____mul_i16 ~ NTRUPlus768InvNTT.M.radix2_4____mul_i16 :
 ={a,b} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_4____mul_i16_cost :
 hoare[RTFixedInvNTT.radix2_4____mul_i16 : true ==> 0<=res.`2<=7].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_4____montgomery_reduce_projection :
 equiv[RTFixedInvNTT.radix2_4____montgomery_reduce ~ NTRUPlus768InvNTT.M.radix2_4____montgomery_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_4____montgomery_reduce_cost :
 hoare[RTFixedInvNTT.radix2_4____montgomery_reduce : true ==> 0<=res.`2<=18].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_4____barrett_reduce_projection :
 equiv[RTFixedInvNTT.radix2_4____barrett_reduce ~ NTRUPlus768InvNTT.M.radix2_4____barrett_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_4____barrett_reduce_cost :
 hoare[RTFixedInvNTT.radix2_4____barrett_reduce : true ==> 0<=res.`2<=21].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection :
 equiv[RTFixedInvNTT.radix2_4____invntt_radix2_4_block ~ NTRUPlus768InvNTT.M.radix2_4____invntt_radix2_4_block :
 ={rp,base,zeta_0} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,base,zeta_0,i,stop}).
  + wp;call rt_fixed_invntt_radix2_4____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_radix2_4____mul_i16_projection.
    wp;call rt_fixed_invntt_radix2_4____barrett_reduce_projection.
    auto.
 auto.
qed.
lemma rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost :
 hoare[RTFixedInvNTT.radix2_4____invntt_radix2_4_block : 0<=W64.to_uint base<=768 ==> 0<=res.`2<=4959].
proof. proc.
 wp;while(W64.to_uint base<=W64.to_uint i<=W64.to_uint base+4 /\ 0<=rt_work<=2310+86*(W64.to_uint i-(W64.to_uint base)) /\ 0<=W64.to_uint base<=768 /\ W64.to_uint stop=W64.to_uint base+4).
  + wp;call rt_fixed_invntt_radix2_4____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_radix2_4____mul_i16_cost.
    wp;call rt_fixed_invntt_radix2_4____barrett_reduce_cost.
    auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> /> &hr hb0 hb1.
 have hs:W64.to_uint(base{hr}+W64.of_int 4)=W64.to_uint base{hr}+4.
 + apply rt_fixed_u64_add;smt().
 smt(W64.ultE).
qed.
lemma rt_fixed_invntt_radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4_projection :
 equiv[RTFixedInvNTT.radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 ~ NTRUPlus768InvNTT.M.radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 :
 ={rp} ==> res{1}.`1=res{2}].
proof. proc.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_projection.
 auto.
qed.
lemma rt_fixed_invntt_radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4_cost :
 hoare[RTFixedInvNTT.radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4 : true ==> 0<=res.`2<=702370].
proof. proc.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 wp;call rt_fixed_invntt_radix2_4____invntt_radix2_4_block_cost.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_8____mul_i16_projection :
 equiv[RTFixedInvNTT.radix2_8____mul_i16 ~ NTRUPlus768InvNTT.M.radix2_8____mul_i16 :
 ={a,b} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_8____mul_i16_cost :
 hoare[RTFixedInvNTT.radix2_8____mul_i16 : true ==> 0<=res.`2<=7].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_8____montgomery_reduce_projection :
 equiv[RTFixedInvNTT.radix2_8____montgomery_reduce ~ NTRUPlus768InvNTT.M.radix2_8____montgomery_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_8____montgomery_reduce_cost :
 hoare[RTFixedInvNTT.radix2_8____montgomery_reduce : true ==> 0<=res.`2<=18].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_8____barrett_reduce_projection :
 equiv[RTFixedInvNTT.radix2_8____barrett_reduce ~ NTRUPlus768InvNTT.M.radix2_8____barrett_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_8____barrett_reduce_cost :
 hoare[RTFixedInvNTT.radix2_8____barrett_reduce : true ==> 0<=res.`2<=21].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection :
 equiv[RTFixedInvNTT.radix2_8____invntt_radix2_8_block ~ NTRUPlus768InvNTT.M.radix2_8____invntt_radix2_8_block :
 ={rp,base,zeta_0} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,base,zeta_0,i,stop}).
  + wp;call rt_fixed_invntt_radix2_8____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_radix2_8____mul_i16_projection.
    wp;call rt_fixed_invntt_radix2_8____barrett_reduce_projection.
    auto.
 auto.
qed.
lemma rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost :
 hoare[RTFixedInvNTT.radix2_8____invntt_radix2_8_block : 0<=W64.to_uint base<=768 ==> 0<=res.`2<=5303].
proof. proc.
 wp;while(W64.to_uint base<=W64.to_uint i<=W64.to_uint base+8 /\ 0<=rt_work<=2310+86*(W64.to_uint i-(W64.to_uint base)) /\ 0<=W64.to_uint base<=768 /\ W64.to_uint stop=W64.to_uint base+8).
  + wp;call rt_fixed_invntt_radix2_8____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_radix2_8____mul_i16_cost.
    wp;call rt_fixed_invntt_radix2_8____barrett_reduce_cost.
    auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> /> &hr hb0 hb1.
 have hs:W64.to_uint(base{hr}+W64.of_int 8)=W64.to_uint base{hr}+8.
 + apply rt_fixed_u64_add;smt().
 smt(W64.ultE).
qed.
lemma rt_fixed_invntt_radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8_projection :
 equiv[RTFixedInvNTT.radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 ~ NTRUPlus768InvNTT.M.radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 :
 ={rp} ==> res{1}.`1=res{2}].
proof. proc.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_projection.
 auto.
qed.
lemma rt_fixed_invntt_radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8_cost :
 hoare[RTFixedInvNTT.radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8 : true ==> 0<=res.`2<=370008].
proof. proc.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 wp;call rt_fixed_invntt_radix2_8____invntt_radix2_8_block_cost.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_16____mul_i16_projection :
 equiv[RTFixedInvNTT.radix2_16____mul_i16 ~ NTRUPlus768InvNTT.M.radix2_16____mul_i16 :
 ={a,b} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_16____mul_i16_cost :
 hoare[RTFixedInvNTT.radix2_16____mul_i16 : true ==> 0<=res.`2<=7].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_16____montgomery_reduce_projection :
 equiv[RTFixedInvNTT.radix2_16____montgomery_reduce ~ NTRUPlus768InvNTT.M.radix2_16____montgomery_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_16____montgomery_reduce_cost :
 hoare[RTFixedInvNTT.radix2_16____montgomery_reduce : true ==> 0<=res.`2<=18].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_16____barrett_reduce_projection :
 equiv[RTFixedInvNTT.radix2_16____barrett_reduce ~ NTRUPlus768InvNTT.M.radix2_16____barrett_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_16____barrett_reduce_cost :
 hoare[RTFixedInvNTT.radix2_16____barrett_reduce : true ==> 0<=res.`2<=21].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection :
 equiv[RTFixedInvNTT.radix2_16____invntt_radix2_16_block ~ NTRUPlus768InvNTT.M.radix2_16____invntt_radix2_16_block :
 ={rp,base,zeta_0} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,base,zeta_0,i,stop}).
  + wp;call rt_fixed_invntt_radix2_16____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_radix2_16____mul_i16_projection.
    wp;call rt_fixed_invntt_radix2_16____barrett_reduce_projection.
    auto.
 auto.
qed.
lemma rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost :
 hoare[RTFixedInvNTT.radix2_16____invntt_radix2_16_block : 0<=W64.to_uint base<=768 ==> 0<=res.`2<=5991].
proof. proc.
 wp;while(W64.to_uint base<=W64.to_uint i<=W64.to_uint base+16 /\ 0<=rt_work<=2310+86*(W64.to_uint i-(W64.to_uint base)) /\ 0<=W64.to_uint base<=768 /\ W64.to_uint stop=W64.to_uint base+16).
  + wp;call rt_fixed_invntt_radix2_16____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_radix2_16____mul_i16_cost.
    wp;call rt_fixed_invntt_radix2_16____barrett_reduce_cost.
    auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> /> &hr hb0 hb1.
 have hs:W64.to_uint(base{hr}+W64.of_int 16)=W64.to_uint base{hr}+16.
 + apply rt_fixed_u64_add;smt().
 smt(W64.ultE).
qed.
lemma rt_fixed_invntt_radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16_projection :
 equiv[RTFixedInvNTT.radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 ~ NTRUPlus768InvNTT.M.radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 :
 ={rp} ==> res{1}.`1=res{2}].
proof. proc.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_projection.
 auto.
qed.
lemma rt_fixed_invntt_radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16_cost :
 hoare[RTFixedInvNTT.radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16 : true ==> 0<=res.`2<=203822].
proof. proc.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 wp;call rt_fixed_invntt_radix2_16____invntt_radix2_16_block_cost.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_32____mul_i16_projection :
 equiv[RTFixedInvNTT.radix2_32____mul_i16 ~ NTRUPlus768InvNTT.M.radix2_32____mul_i16 :
 ={a,b} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_32____mul_i16_cost :
 hoare[RTFixedInvNTT.radix2_32____mul_i16 : true ==> 0<=res.`2<=7].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_32____montgomery_reduce_projection :
 equiv[RTFixedInvNTT.radix2_32____montgomery_reduce ~ NTRUPlus768InvNTT.M.radix2_32____montgomery_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_32____montgomery_reduce_cost :
 hoare[RTFixedInvNTT.radix2_32____montgomery_reduce : true ==> 0<=res.`2<=18].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_32____barrett_reduce_projection :
 equiv[RTFixedInvNTT.radix2_32____barrett_reduce ~ NTRUPlus768InvNTT.M.radix2_32____barrett_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_32____barrett_reduce_cost :
 hoare[RTFixedInvNTT.radix2_32____barrett_reduce : true ==> 0<=res.`2<=21].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_32____invntt_radix2_32_block_projection :
 equiv[RTFixedInvNTT.radix2_32____invntt_radix2_32_block ~ NTRUPlus768InvNTT.M.radix2_32____invntt_radix2_32_block :
 ={rp,base,zeta_0} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,base,zeta_0,i,stop}).
  + wp;call rt_fixed_invntt_radix2_32____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_radix2_32____mul_i16_projection.
    wp;call rt_fixed_invntt_radix2_32____barrett_reduce_projection.
    auto.
 auto.
qed.
lemma rt_fixed_invntt_radix2_32____invntt_radix2_32_block_cost :
 hoare[RTFixedInvNTT.radix2_32____invntt_radix2_32_block : 0<=W64.to_uint base<=768 ==> 0<=res.`2<=7367].
proof. proc.
 wp;while(W64.to_uint base<=W64.to_uint i<=W64.to_uint base+32 /\ 0<=rt_work<=2310+86*(W64.to_uint i-(W64.to_uint base)) /\ 0<=W64.to_uint base<=768 /\ W64.to_uint stop=W64.to_uint base+32).
  + wp;call rt_fixed_invntt_radix2_32____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_radix2_32____mul_i16_cost.
    wp;call rt_fixed_invntt_radix2_32____barrett_reduce_cost.
    auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> /> &hr hb0 hb1.
 have hs:W64.to_uint(base{hr}+W64.of_int 32)=W64.to_uint base{hr}+32.
 + apply rt_fixed_u64_add;smt().
 smt(W64.ultE).
qed.
lemma rt_fixed_invntt_radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32_projection :
 equiv[RTFixedInvNTT.radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32 ~ NTRUPlus768InvNTT.M.radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32 :
 ={rp} ==> res{1}.`1=res{2}].
proof. proc.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_projection.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_projection.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_projection.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_projection.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_projection.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_projection.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_projection.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_projection.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_projection.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_projection.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_projection.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_projection.
 auto.
qed.
lemma rt_fixed_invntt_radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32_cost :
 hoare[RTFixedInvNTT.radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32 : true ==> 0<=res.`2<=120727].
proof. proc.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_cost.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_cost.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_cost.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_cost.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_cost.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_cost.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_cost.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_cost.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_cost.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_cost.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_cost.
 wp;call rt_fixed_invntt_radix2_32____invntt_radix2_32_block_cost.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_64____mul_i16_projection :
 equiv[RTFixedInvNTT.radix2_64____mul_i16 ~ NTRUPlus768InvNTT.M.radix2_64____mul_i16 :
 ={a,b} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_64____mul_i16_cost :
 hoare[RTFixedInvNTT.radix2_64____mul_i16 : true ==> 0<=res.`2<=7].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_64____montgomery_reduce_projection :
 equiv[RTFixedInvNTT.radix2_64____montgomery_reduce ~ NTRUPlus768InvNTT.M.radix2_64____montgomery_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_64____montgomery_reduce_cost :
 hoare[RTFixedInvNTT.radix2_64____montgomery_reduce : true ==> 0<=res.`2<=18].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_64____barrett_reduce_projection :
 equiv[RTFixedInvNTT.radix2_64____barrett_reduce ~ NTRUPlus768InvNTT.M.radix2_64____barrett_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix2_64____barrett_reduce_cost :
 hoare[RTFixedInvNTT.radix2_64____barrett_reduce : true ==> 0<=res.`2<=21].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix2_64____invntt_radix2_64_block_projection :
 equiv[RTFixedInvNTT.radix2_64____invntt_radix2_64_block ~ NTRUPlus768InvNTT.M.radix2_64____invntt_radix2_64_block :
 ={rp,base,zeta_0} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,base,zeta_0,i,stop}).
  + wp;call rt_fixed_invntt_radix2_64____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_radix2_64____mul_i16_projection.
    wp;call rt_fixed_invntt_radix2_64____barrett_reduce_projection.
    auto.
 auto.
qed.
lemma rt_fixed_invntt_radix2_64____invntt_radix2_64_block_cost :
 hoare[RTFixedInvNTT.radix2_64____invntt_radix2_64_block : 0<=W64.to_uint base<=768 ==> 0<=res.`2<=10119].
proof. proc.
 wp;while(W64.to_uint base<=W64.to_uint i<=W64.to_uint base+64 /\ 0<=rt_work<=2310+86*(W64.to_uint i-(W64.to_uint base)) /\ 0<=W64.to_uint base<=768 /\ W64.to_uint stop=W64.to_uint base+64).
  + wp;call rt_fixed_invntt_radix2_64____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_radix2_64____mul_i16_cost.
    wp;call rt_fixed_invntt_radix2_64____barrett_reduce_cost.
    auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> /> &hr hb0 hb1.
 have hs:W64.to_uint(base{hr}+W64.of_int 64)=W64.to_uint base{hr}+64.
 + apply rt_fixed_u64_add;smt().
 smt(W64.ultE).
qed.
lemma rt_fixed_invntt_radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64_projection :
 equiv[RTFixedInvNTT.radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 ~ NTRUPlus768InvNTT.M.radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 :
 ={rp} ==> res{1}.`1=res{2}].
proof. proc.
 wp;call rt_fixed_invntt_radix2_64____invntt_radix2_64_block_projection.
 wp;call rt_fixed_invntt_radix2_64____invntt_radix2_64_block_projection.
 wp;call rt_fixed_invntt_radix2_64____invntt_radix2_64_block_projection.
 wp;call rt_fixed_invntt_radix2_64____invntt_radix2_64_block_projection.
 wp;call rt_fixed_invntt_radix2_64____invntt_radix2_64_block_projection.
 wp;call rt_fixed_invntt_radix2_64____invntt_radix2_64_block_projection.
 auto.
qed.
lemma rt_fixed_invntt_radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64_cost :
 hoare[RTFixedInvNTT.radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64 : true ==> 0<=res.`2<=79183].
proof. proc.
 wp;call rt_fixed_invntt_radix2_64____invntt_radix2_64_block_cost.
 wp;call rt_fixed_invntt_radix2_64____invntt_radix2_64_block_cost.
 wp;call rt_fixed_invntt_radix2_64____invntt_radix2_64_block_cost.
 wp;call rt_fixed_invntt_radix2_64____invntt_radix2_64_block_cost.
 wp;call rt_fixed_invntt_radix2_64____invntt_radix2_64_block_cost.
 wp;call rt_fixed_invntt_radix2_64____invntt_radix2_64_block_cost.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix3____mul_i16_projection :
 equiv[RTFixedInvNTT.radix3____mul_i16 ~ NTRUPlus768InvNTT.M.radix3____mul_i16 :
 ={a,b} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix3____mul_i16_cost :
 hoare[RTFixedInvNTT.radix3____mul_i16 : true ==> 0<=res.`2<=7].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix3____montgomery_reduce_projection :
 equiv[RTFixedInvNTT.radix3____montgomery_reduce ~ NTRUPlus768InvNTT.M.radix3____montgomery_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_radix3____montgomery_reduce_cost :
 hoare[RTFixedInvNTT.radix3____montgomery_reduce : true ==> 0<=res.`2<=18].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3_projection :
 equiv[RTFixedInvNTT.radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 ~ NTRUPlus768InvNTT.M.radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 :
 ={rp} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,i}).
  + wp;call rt_fixed_invntt_radix3____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_radix3____mul_i16_projection.
    wp;call rt_fixed_invntt_radix3____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_radix3____mul_i16_projection.
    wp;call rt_fixed_invntt_radix3____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_radix3____mul_i16_projection.
    auto.
 wp;while(={rp,i}).
  + wp;call rt_fixed_invntt_radix3____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_radix3____mul_i16_projection.
    wp;call rt_fixed_invntt_radix3____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_radix3____mul_i16_projection.
    wp;call rt_fixed_invntt_radix3____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_radix3____mul_i16_projection.
    auto.
 auto.
qed.
lemma rt_fixed_invntt_radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3_cost :
 hoare[RTFixedInvNTT.radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3 : true ==> 0<=res.`2<=39560].
proof. proc.
 wp;while(384<=W64.to_uint i<=512 /\ 0<=rt_work<=19719+137*(W64.to_uint i-(384))).
  + wp;call rt_fixed_invntt_radix3____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_radix3____mul_i16_cost.
    wp;call rt_fixed_invntt_radix3____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_radix3____mul_i16_cost.
    wp;call rt_fixed_invntt_radix3____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_radix3____mul_i16_cost.
    auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 wp;while(0<=W64.to_uint i<=128 /\ 0<=rt_work<=2308+136*(W64.to_uint i-(0))).
  + wp;call rt_fixed_invntt_radix3____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_radix3____mul_i16_cost.
    wp;call rt_fixed_invntt_radix3____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_radix3____mul_i16_cost.
    wp;call rt_fixed_invntt_radix3____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_radix3____mul_i16_cost.
    auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_final____mul_i16_projection :
 equiv[RTFixedInvNTT.final____mul_i16 ~ NTRUPlus768InvNTT.M.final____mul_i16 :
 ={a,b} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_final____mul_i16_cost :
 hoare[RTFixedInvNTT.final____mul_i16 : true ==> 0<=res.`2<=7].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_final____montgomery_reduce_projection :
 equiv[RTFixedInvNTT.final____montgomery_reduce ~ NTRUPlus768InvNTT.M.final____montgomery_reduce :
 ={a} ==> res{1}.`1=res{2}].
proof. proc.
 auto.
qed.
lemma rt_fixed_invntt_final____montgomery_reduce_cost :
 hoare[RTFixedInvNTT.final____montgomery_reduce : true ==> 0<=res.`2<=18].
proof. proc.
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final_projection :
 equiv[RTFixedInvNTT.final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final ~ NTRUPlus768InvNTT.M.final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final :
 ={rp} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,i}).
  + wp;call rt_fixed_invntt_final____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_final____mul_i16_projection.
    wp;call rt_fixed_invntt_final____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_final____mul_i16_projection.
    wp;call rt_fixed_invntt_final____montgomery_reduce_projection.
    wp;call rt_fixed_invntt_final____mul_i16_projection.
    auto.
 auto.
qed.
lemma rt_fixed_invntt_final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final_cost :
 hoare[RTFixedInvNTT.final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final : true ==> 0<=res.`2<=52229].
proof. proc.
 wp;while(0<=W64.to_uint i<=384 /\ 0<=rt_work<=2308+124*(W64.to_uint i-(0))).
  + wp;call rt_fixed_invntt_final____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_final____mul_i16_cost.
    wp;call rt_fixed_invntt_final____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_final____mul_i16_cost.
    wp;call rt_fixed_invntt_final____montgomery_reduce_cost.
    wp;call rt_fixed_invntt_final____mul_i16_cost.
    auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt___invntt_copy_projection :
 equiv[RTFixedInvNTT.__invntt_copy ~ NTRUPlus768InvNTT.M.__invntt_copy :
 ={rp,ap} ==> res{1}.`1=res{2}].
proof. proc.
 wp;while(={rp,ap,i}).
  + auto.
 auto.
qed.
lemma rt_fixed_invntt___invntt_copy_cost :
 hoare[RTFixedInvNTT.__invntt_copy : true ==> 0<=res.`2<=12293].
proof. proc.
 wp;while(0<=W64.to_uint i<=768 /\ 0<=rt_work<=4612+7*(W64.to_uint i-(0))).
  + auto=> /> &hr;rewrite W64.ultE /=;move=>*;try (rewrite rt_fixed_u64_next 1:/#);smt().
 auto=> />;smt(rt_fixed_exit).
qed.
lemma rt_fixed_invntt_jade_ntruplus_ntruplus768_amd64_ref_invntt_projection :
 equiv[RTFixedInvNTT.jade_ntruplus_ntruplus768_amd64_ref_invntt ~ NTRUPlus768InvNTT.M.jade_ntruplus_ntruplus768_amd64_ref_invntt :
 ={rp,ap} ==> res{1}.`1=res{2}].
proof. proc.
 wp;call rt_fixed_invntt_final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final_projection.
 wp;call rt_fixed_invntt_radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3_projection.
 wp;call rt_fixed_invntt_radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64_projection.
 wp;call rt_fixed_invntt_radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32_projection.
 wp;call rt_fixed_invntt_radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16_projection.
 wp;call rt_fixed_invntt_radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8_projection.
 wp;call rt_fixed_invntt_radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4_projection.
 wp;call rt_fixed_invntt___invntt_copy_projection.
 auto.
qed.
lemma rt_fixed_invntt_jade_ntruplus_ntruplus768_amd64_ref_invntt_cost :
 hoare[RTFixedInvNTT.jade_ntruplus_ntruplus768_amd64_ref_invntt : true ==> 0<=res.`2<=1605562].
proof. proc.
 wp;call rt_fixed_invntt_final__jade_ntruplus_ntruplus768_amd64_ref_invntt_final_cost.
 wp;call rt_fixed_invntt_radix3__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3_cost.
 wp;call rt_fixed_invntt_radix2_64__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_64_cost.
 wp;call rt_fixed_invntt_radix2_32__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_32_cost.
 wp;call rt_fixed_invntt_radix2_16__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_16_cost.
 wp;call rt_fixed_invntt_radix2_8__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_8_cost.
 wp;call rt_fixed_invntt_radix2_4__jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4_cost.
 wp;call rt_fixed_invntt___invntt_copy_cost.
 auto=> />;smt(rt_fixed_exit).
qed.
op rt_fixed_invntt_bound:int = 1605562.
lemma rt_fixed_invntt_bound_cost : hoare[RTFixedInvNTT.jade_ntruplus_ntruplus768_amd64_ref_invntt : true ==>0<=res.`2<=rt_fixed_invntt_bound].
proof. exact rt_fixed_invntt_jade_ntruplus_ntruplus768_amd64_ref_invntt_cost. qed.
