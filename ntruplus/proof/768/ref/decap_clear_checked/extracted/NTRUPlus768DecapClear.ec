require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array13506 WArray13506.

module M = {
  proc jade_ntruplus_ntruplus768_amd64_ref_decap_clear (workspace:W8.t Array13506.t) : 
  W8.t Array13506.t = {
    var i:W64.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 13506))) {
      workspace.[(W64.to_uint i)] <- (W8.of_int 0);
      i <- (i + (W64.of_int 1));
    }
    return workspace;
  }
}.
