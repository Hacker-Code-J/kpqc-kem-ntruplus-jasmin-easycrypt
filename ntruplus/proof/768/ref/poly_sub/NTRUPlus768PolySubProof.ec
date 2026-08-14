require import AllCore IntDiv Distr.
from Jasmin require import JWord JModel_x86.

require import Array768 NTRUPlus768PolySub.

op poly_sub_spec
    (ap bp : W16.t Array768.t) : W16.t Array768.t =
  Array768.init (fun j => ap.[j] - bp.[j]).

op poly_sub_prefix
    (ap bp rp : W16.t Array768.t) (upto : int) : bool =
  forall j, 0 <= j < upto => rp.[j] = ap.[j] - bp.[j].

lemma poly_sub_prefix_extend
    (ap bp rp : W16.t Array768.t) (i : int) :
  0 <= i < 768 =>
  poly_sub_prefix ap bp rp i =>
  poly_sub_prefix ap bp (rp.[i <- ap.[i] - bp.[i]]) (i + 1).
proof.
  move=> Hi Hprefix j Hj.
  case (j = i) => [-> | Hneq].
  + by rewrite Array768.get_setE.
  have Hjold : 0 <= j < i by smt().
  have Hkeep : (rp.[i <- ap.[i] - bp.[i]]).[j] = rp.[j].
  + smt(Array768.get_setE).
  rewrite Hkeep.
  exact (Hprefix j Hjold).
qed.

lemma poly_sub_prefix_full
    (ap bp rp : W16.t Array768.t) :
  poly_sub_prefix ap bp rp 768 =>
  rp = poly_sub_spec ap bp.
proof.
  move=> Hprefix.
  apply Array768.tP => j Hj.
  rewrite /poly_sub_spec Array768.initiE 1:Hj.
  exact (Hprefix j Hj).
qed.

lemma poly_sub_functional
    (rp0 ap0 bp0 : W16.t Array768.t) :
  hoare [NTRUPlus768PolySub.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sub :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==>
    res = poly_sub_spec ap0 bp0].
proof.
  proc.
  seq 2 :
    (ap = ap0 /\ bp = bp0 /\ i = W64.of_int 0 /\ poly_sub_prefix ap0 bp0 rp 0).
  + auto => />.
    rewrite /poly_sub_prefix.
    smt().
  while (0 <= W64.to_uint i <= 768 /\ ap = ap0 /\ bp = bp0 /\
         poly_sub_prefix ap0 bp0 rp (W64.to_uint i)); last first.
  + skip => &hr [Hap [Hbp [Hi0 Hprefix0]]].
    split.
    - split; first by rewrite Hi0 W64.to_uint0; smt().
      split; first exact Hap.
      split; first exact Hbp.
      by rewrite Hi0 W64.to_uint0.
    move=> i1 rp1 Hexit [Hi [Hap1 [Hbp1 Hprefix1]]].
    rewrite W64.ultE /= in Hexit.
    apply poly_sub_prefix_full.
    have Hiend : W64.to_uint i1 = 768 by smt().
    by rewrite -Hiend.
  auto => /> &hr HiLow HiHigh Hprefix Hloop.
  rewrite W64.ultE /= in Hloop.
  have Hi768 : 0 <= W64.to_uint i{hr} < 768 by smt().
  have Hnext :
      W64.to_uint (i{hr} + W64.one) =
      W64.to_uint i{hr} + 1.
  + rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
  split.
  + rewrite Hnext; smt(W64.to_uint_cmp).
  rewrite Hnext.
  apply poly_sub_prefix_extend; first exact Hi768.
  exact Hprefix.
qed.

lemma poly_sub_lossless :
  islossless
    NTRUPlus768PolySub.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sub.
proof.
  proc.
  while (0 <= W64.to_uint i <= 768) (768 - W64.to_uint i); last first.
  + auto => /> i0 Hi Hdone.
    rewrite W64.ultE /=.
    smt().
  auto => /> &hr Hi Hhigh Hloop.
  rewrite W64.ultE /= in Hloop.
  rewrite W64.to_uintD_small /=; smt(W64.to_uint_cmp).
qed.

lemma poly_sub_correct
    (rp0 ap0 bp0 : W16.t Array768.t) :
  phoare [NTRUPlus768PolySub.M.jade_ntruplus_ntruplus768_amd64_ref_poly_sub :
    rp = rp0 /\ ap = ap0 /\ bp = bp0 ==>
    res = poly_sub_spec ap0 bp0] = 1%r.
proof.
  by conseq poly_sub_lossless (poly_sub_functional rp0 ap0 bp0).
qed.
