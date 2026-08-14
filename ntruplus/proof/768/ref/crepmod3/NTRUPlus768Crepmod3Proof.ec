require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.

require import Array768 WArray1536 NTRUPlus768Crepmod3.

op qword : W16.t = W16.of_int 3457.
op qhalf_hi_word : W16.t = W16.of_int 1729.
op qhalf_lo_word : W16.t = W16.of_int 1728.
op vword : W32.t = W32.of_int 10923.
op biasword : W32.t = W32.of_int 16384.

op crepmod3_word (a : W16.t) : W16.t =
  let mask = (a `|>>` W8.of_int 15) `&` qword in
  let a = a + mask in
  let a = a - qhalf_hi_word in
  let mask = (a `|>>` W8.of_int 15) `&` qword in
  let a = a + mask in
  let a = a - qhalf_lo_word in
  let td = sigextu32 a * vword + biasword in
  let t = truncateu16 (td `|>>` W8.of_int 15) in
  a - t * W16.of_int 3.

op poly_crepmod3_spec (p : W16.t Array768.t) : W16.t Array768.t =
  Array768.init (fun j => crepmod3_word p.[j]).

op crepmod3_prefix
    (ap rp : W16.t Array768.t) (upto : int) : bool =
  forall j, 0 <= j < upto => rp.[j] = crepmod3_word ap.[j].

lemma crepmod3_helper_functional (a0 : W16.t) :
  hoare [NTRUPlus768Crepmod3.M.__crepmod3 :
    a = a0 ==> res = crepmod3_word a0].
proof.
  proc; auto => />.
qed.

lemma crepmod3_prefix_extend
    (ap rp : W16.t Array768.t) (i : int) (v : W16.t) :
  0 <= i < 768 =>
  crepmod3_prefix ap rp i =>
  v = crepmod3_word ap.[i] =>
  crepmod3_prefix ap (rp.[i <- v]) (i + 1).
proof.
  move=> Hi Hprefix Hv j Hj.
  case (j = i) => [-> | Hneq].
  + smt(Array768.get_setE).
  have Hjold : 0 <= j < i by smt().
  smt(Array768.get_setE).
qed.

lemma crepmod3_prefix_full
    (ap rp : W16.t Array768.t) :
  crepmod3_prefix ap rp 768 => rp = poly_crepmod3_spec ap.
proof.
  move=> Hprefix.
  apply Array768.tP => j Hj.
  rewrite /poly_crepmod3_spec Array768.initiE 1:Hj.
  exact (Hprefix j Hj).
qed.

lemma poly_crepmod3_functional
    (rp0 ap0 : W16.t Array768.t) :
  hoare [NTRUPlus768Crepmod3.M.jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3 :
    rp = rp0 /\ ap = ap0 ==> res = poly_crepmod3_spec ap0].
proof.
  proc.
  seq 2 : (ap = ap0 /\ i = W64.of_int 0 /\ crepmod3_prefix ap0 rp 0).
  + auto => />; rewrite /crepmod3_prefix; smt().
  while (0 <= W64.to_uint i <= 768 /\ ap = ap0 /\
         crepmod3_prefix ap0 rp (W64.to_uint i)); last first.
  + skip => &hr [Hap [Hi0 Hprefix0]].
    split.
    - split; first by rewrite Hi0 W64.to_uint0; smt().
      split; first exact Hap.
      by rewrite Hi0 W64.to_uint0.
    move=> i1 rp1 Hexit [Hi [Hap1 Hprefix1]].
    rewrite W64.ultE /= in Hexit.
    apply crepmod3_prefix_full.
    have Hiend : W64.to_uint i1 = 768 by smt().
    by rewrite -Hiend.
  inline NTRUPlus768Crepmod3.M.__crepmod3.
  auto => /> &hr HiLow HiHigh Hprefix Hloop.
  rewrite W64.ultE /= in Hloop.
  have Hi768 : 0 <= W64.to_uint i{hr} < 768 by smt().
  have Hnext : W64.to_uint (i{hr} + W64.one) = W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  split.
  + rewrite Hnext; smt(W64.to_uint_cmp).
  rewrite Hnext.
  apply crepmod3_prefix_extend; 1: exact Hi768; 1: exact Hprefix.
  by rewrite /crepmod3_word.
qed.

lemma poly_crepmod3_lossless :
  islossless
    NTRUPlus768Crepmod3.M.jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3.
proof.
  proc.
  while (0 <= W64.to_uint i <= 768) (768 - W64.to_uint i); last first.
  + auto => /> i0 Hi Hdone.
    rewrite W64.ultE /=.
    smt().
  move=> *.
  inline NTRUPlus768Crepmod3.M.__crepmod3.
  auto => /> &hr Hi Hhigh Hloop.
  rewrite W64.ultE /= in Hloop.
  rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
qed.

lemma poly_crepmod3_correct
    (rp0 ap0 : W16.t Array768.t) :
  phoare [NTRUPlus768Crepmod3.M.jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3 :
    rp = rp0 /\ ap = ap0 ==> res = poly_crepmod3_spec ap0] = 1%r.
proof.
  by conseq poly_crepmod3_lossless (poly_crepmod3_functional rp0 ap0).
qed.
