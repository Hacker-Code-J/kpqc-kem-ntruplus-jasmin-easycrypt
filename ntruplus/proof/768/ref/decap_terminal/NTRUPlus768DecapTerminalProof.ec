require import AllCore Distr.
from Jasmin require import JWord.

require import Array32.
require import NTRUPlus768DecapMaskProof.

module DecapTerminal = {
  (* This is only the value-level terminal wrapper around the already-proved
     32-byte masking loop.  Returning [failv] here preserves the byte value,
     not C's wider integer-return semantics. *)
  proc finish(ss_source : W8.t Array32.t,
              failv : W8.t) : W8.t Array32.t * W8.t = {
    var ss : W8.t Array32.t;

    ss <@ DecapMask.mask_ss(ss_source, failv);
    return (ss, failv);
  }
}.

lemma finish_functional
    (ss_source0 : W8.t Array32.t)
    (failv0 : W8.t) :
  hoare [DecapTerminal.finish :
    arg = (ss_source0, failv0) ==>
      res.`1 = decap_mask_ss_spec failv0 ss_source0 /\
      res.`2 = failv0].
proof.
  proc.
  call (decap_mask_functional ss_source0 failv0).
  by auto => />.
qed.

lemma finish_ll :
  islossless DecapTerminal.finish.
proof.
  proc.
  call decap_mask_ll.
  by auto.
qed.

lemma finish_correct
    (ss_source0 : W8.t Array32.t)
    (failv0 : W8.t) :
  phoare [DecapTerminal.finish :
    arg = (ss_source0, failv0) ==>
      res.`1 = decap_mask_ss_spec failv0 ss_source0 /\
      res.`2 = failv0] = 1%r.
proof.
  by conseq finish_ll (finish_functional ss_source0 failv0).
qed.
