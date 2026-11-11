require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array96 Array192 Array768 WArray96 WArray192 WArray1536.

module M = {
  proc __decode_bit (t1:W8.t, t2:W8.t, t3:W16.t, r:W32.t, coeff:W16.t,
                     sHIFT:int) : W8.t * W8.t * W16.t * W32.t = {
    var t2w:W16.t;
    var t4:W16.t;
    var t4d:W32.t;
    var t1w:W16.t;
    t2w <- (zeroextu16 t2);
    t4 <- t2w;
    t4 <- (t4 `&` (W16.of_int 1));
    t4 <- (t4 + coeff);
    t4d <- (zeroextu32 t4);
    r <- (r `|` t4d);
    t1w <- (zeroextu16 t1);
    t4 <- (t4 `^` t1w);
    t4 <- (t4 `&` (W16.of_int 1));
    t4 <- (t4 `<<` (W8.of_int sHIFT));
    t3 <- (t3 `^` t4);
    t1 <- (t1 `>>` (W8.of_int 1));
    t2 <- (t2 `>>` (W8.of_int 1));
    return (t1, t2, t3, r);
  }
  proc jade_ntruplus_ntruplus768_amd64_ref_poly_sotp_decode (msg:W8.t Array96.t,
                                                             ap:W16.t Array768.t,
                                                             buf:W8.t Array192.t) : 
  W8.t Array96.t * W32.t = {
    var r:W32.t;
    var i:W64.t;
    var off:W64.t;
    var t1:W8.t;
    var t2:W8.t;
    var t3:W16.t;
    var norm:W32.t;
    var mask32:W32.t;
    var mask:W8.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    r <- (W32.of_int 0);
    while ((i \ult (W64.of_int (768 %/ 8)))) {
      off <- i;
      off <- (off `<<` (W8.of_int 3));
      t1 <- buf.[(W64.to_uint i)];
      t2 <- buf.[(W64.to_uint (i + (W64.of_int (768 %/ 8))))];
      t3 <- (W16.of_int 0);
      (t1, t2, t3, r) <@ __decode_bit (t1, t2, t3, r, ap.[(W64.to_uint off)],
      0);
      (t1, t2, t3, r) <@ __decode_bit (t1, t2, t3, r,
      ap.[(W64.to_uint (off + (W64.of_int 1)))], 1);
      (t1, t2, t3, r) <@ __decode_bit (t1, t2, t3, r,
      ap.[(W64.to_uint (off + (W64.of_int 2)))], 2);
      (t1, t2, t3, r) <@ __decode_bit (t1, t2, t3, r,
      ap.[(W64.to_uint (off + (W64.of_int 3)))], 3);
      (t1, t2, t3, r) <@ __decode_bit (t1, t2, t3, r,
      ap.[(W64.to_uint (off + (W64.of_int 4)))], 4);
      (t1, t2, t3, r) <@ __decode_bit (t1, t2, t3, r,
      ap.[(W64.to_uint (off + (W64.of_int 5)))], 5);
      (t1, t2, t3, r) <@ __decode_bit (t1, t2, t3, r,
      ap.[(W64.to_uint (off + (W64.of_int 6)))], 6);
      (t1, t2, t3, r) <@ __decode_bit (t1, t2, t3, r,
      ap.[(W64.to_uint (off + (W64.of_int 7)))], 7);
      msg.[(W64.to_uint i)] <- (truncateu8 t3);
      i <- (i + (W64.of_int 1));
    }
    r <- (r `>>` (W8.of_int 1));
    norm <- (W32.of_int 0);
    norm <- (norm - r);
    norm <- (norm `>>` (W8.of_int 31));
    r <- norm;
    mask32 <- r;
    mask32 <- (mask32 - (W32.of_int 1));
    mask <- (truncateu8 mask32);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (768 %/ 8)))) {
      msg.[(W64.to_uint i)] <- (msg.[(W64.to_uint i)] `&` mask);
      i <- (i + (W64.of_int 1));
    }
    return (msg, r);
  }
}.
