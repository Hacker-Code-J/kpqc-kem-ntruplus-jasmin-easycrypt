require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array14466 WArray14466.

module M = {
  proc jade_ntruplus_ntruplus768_amd64_ref_keygen_clear (workspace:W8.t Array14466.t) : 
  W8.t Array14466.t = {
    var i:W64.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 14466))) {
      workspace.[(W64.to_uint i)] <- (W8.of_int 0);
      i <- (i + (W64.of_int 1));
    }
    return workspace;
  }
}.
