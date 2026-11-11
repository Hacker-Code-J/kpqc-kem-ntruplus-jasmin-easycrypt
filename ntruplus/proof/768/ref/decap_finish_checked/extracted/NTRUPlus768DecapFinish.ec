require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array32 Array224 Array1152 WArray32 WArray224 WArray1152.

module M = {
  proc verify_bytes (recovered:W8.t Array1152.t, regenerated:W8.t Array1152.t) : 
  W64.t = {
    var result:W64.t;
    var acc:W8.t;
    var i:W64.t;
    var x:W8.t;
    acc <- (W8.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 1152))) {
      x <- recovered.[(W64.to_uint i)];
      x <- (x `^` regenerated.[(W64.to_uint i)]);
      acc <- (acc `|` x);
      i <- (i + (W64.of_int 1));
    }
    result <- (zeroextu64 acc);
    result <- (- result);
    result <- (result `>>` (W8.of_int 63));
    return result;
  }
  proc jade_ntruplus_ntruplus768_amd64_ref_decap_finish (ss:W8.t Array32.t,
                                                         hashout:W8.t Array224.t,
                                                         recovered:W8.t Array1152.t,
                                                         regenerated:W8.t Array1152.t,
                                                         decode_fail:W32.t) : 
  W8.t Array32.t * W32.t = {
    var failed:W32.t;
    var comparison:W64.t;
    var mask:W32.t;
    var i:W64.t;
    var b:W8.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    comparison <@ verify_bytes (recovered, regenerated);
    failed <- (truncateu32 comparison);
    failed <- (failed `|` decode_fail);
    mask <- failed;
    mask <- (- mask);
    mask <- (invw mask);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      b <- hashout.[(W64.to_uint i)];
      b <- (b `&` (truncateu8 mask));
      ss.[(W64.to_uint i)] <- b;
      i <- (i + (W64.of_int 1));
    }
    return (ss, failed);
  }
}.
