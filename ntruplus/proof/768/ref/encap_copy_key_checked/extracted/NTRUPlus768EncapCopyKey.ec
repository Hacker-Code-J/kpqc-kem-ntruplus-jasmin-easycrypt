require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array32 Array224 WArray32 WArray224.

module M = {
  proc jade_ntruplus_ntruplus768_amd64_ref_encap_copy_key (ss:W8.t Array32.t,
                                                           hash_output:W8.t Array224.t) : 
  W8.t Array32.t = {
    var i:W64.t;
    var b:W8.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      b <- hash_output.[(W64.to_uint i)];
      ss.[(W64.to_uint i)] <- b;
      i <- (i + (W64.of_int 1));
    }
    return ss;
  }
}.
