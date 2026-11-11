require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array32 Array96 Array129 WArray32 WArray96 WArray129.

module M = {
  proc jade_ntruplus_ntruplus768_amd64_ref_decap_hash_h_prepare (input:W8.t Array129.t,
                                                                 msg:W8.t Array96.t,
                                                                 suffix:W8.t Array32.t) : 
  W8.t Array129.t = {
    var i:W64.t;
    var b:W8.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    input.[0] <- (W8.of_int 2);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 96))) {
      b <- msg.[(W64.to_uint i)];
      input.[(W64.to_uint (i + (W64.of_int 1)))] <- b;
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      b <- suffix.[(W64.to_uint i)];
      input.[(W64.to_uint (i + (W64.of_int 97)))] <- b;
      i <- (i + (W64.of_int 1));
    }
    return input;
  }
}.
