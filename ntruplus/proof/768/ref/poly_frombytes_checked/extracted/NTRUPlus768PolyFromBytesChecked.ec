require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array768 Array1152 WArray1152 WArray1536.

module M = {
  proc jade_ntruplus_ntruplus768_amd64_ref_poly_frombytes (rp:W16.t Array768.t,
                                                           ap:W8.t Array1152.t) : 
  W16.t Array768.t * W32.t = {
    var fail_0:W32.t;
    var i:W64.t;
    var off:W64.t;
    var byte:W8.t;
    var t0:W16.t;
    var word:W16.t;
    var t1:W16.t;
    var wide:W32.t;
    var delta_0:W32.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    fail_0 <- (W32.of_int 0);
    while ((i \ult (W64.of_int (768 %/ 2)))) {
      off <- i;
      off <- (off `<<` (W8.of_int 1));
      off <- (off + i);
      byte <- ap.[(W64.to_uint off)];
      t0 <- (zeroextu16 byte);
      byte <- ap.[(W64.to_uint (off + (W64.of_int 1)))];
      word <- (zeroextu16 byte);
      word <- (word `<<` (W8.of_int 8));
      t0 <- (t0 `|` word);
      t0 <- (t0 `&` (W16.of_int 4095));
      t1 <- (zeroextu16 byte);
      t1 <- (t1 `>>` (W8.of_int 4));
      byte <- ap.[(W64.to_uint (off + (W64.of_int 2)))];
      word <- (zeroextu16 byte);
      word <- (word `<<` (W8.of_int 4));
      t1 <- (t1 `|` word);
      t1 <- (t1 `&` (W16.of_int 4095));
      rp.[(W64.to_uint ((W64.of_int 2) * i))] <- t0;
      rp.[(W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 1)))] <- t1;
      wide <- (zeroextu32 t0);
      delta_0 <- (W32.of_int (3457 - 1));
      delta_0 <- (delta_0 - wide);
      fail_0 <- (fail_0 `|` delta_0);
      wide <- (zeroextu32 t1);
      delta_0 <- (W32.of_int (3457 - 1));
      delta_0 <- (delta_0 - wide);
      fail_0 <- (fail_0 `|` delta_0);
      i <- (i + (W64.of_int 1));
    }
    fail_0 <- (fail_0 `>>` (W8.of_int 31));
    return (rp, fail_0);
  }
}.
