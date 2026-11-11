require import AllCore StdOrder.
import IntOrder.

(* Counts of direct named calls, not CPU cycles. The price of OWUnitTest,
   OWEncode and OWRecover includes their own fixed arithmetic, codecs and
   coefficient/polynomial conversions. Scaling the challenger polynomial
   remains an explicitly priced representation operation; it is never
   silently charged to the challenger. The caller accounts for B's time. *)
type rt_kernel_profile = {
 rtk_scale:int;
 rtk_unit:int;
 rtk_encode:int;
 rtk_recover:int;
 rtk_encrypt:int;
 rtk_trit:int;
 rtk_poly_compare:int;
 rtk_cipher_compare:int;
 rtk_psi_draw:int;
 rtk_adversary:int;
}.
op rtk_profile s u e r p t q c d a : rt_kernel_profile =
 {|rtk_scale=s;rtk_unit=u;rtk_encode=e;rtk_recover=r;
   rtk_encrypt=p;rtk_trit=t;rtk_poly_compare=q;rtk_cipher_compare=c;
   rtk_psi_draw=d;rtk_adversary=a|}.
op rtk_add(x y:rt_kernel_profile) =
 rtk_profile (x.`rtk_scale+y.`rtk_scale) (x.`rtk_unit+y.`rtk_unit)
 (x.`rtk_encode+y.`rtk_encode) (x.`rtk_recover+y.`rtk_recover)
 (x.`rtk_encrypt+y.`rtk_encrypt) (x.`rtk_trit+y.`rtk_trit)
 (x.`rtk_poly_compare+y.`rtk_poly_compare) (x.`rtk_cipher_compare+y.`rtk_cipher_compare)
 (x.`rtk_psi_draw+y.`rtk_psi_draw) (x.`rtk_adversary+y.`rtk_adversary).
op rtk_le(x y:rt_kernel_profile) =
 0<=x.`rtk_scale<=y.`rtk_scale /\ 0<=x.`rtk_unit<=y.`rtk_unit /\
 0<=x.`rtk_encode<=y.`rtk_encode /\ 0<=x.`rtk_recover<=y.`rtk_recover /\
 0<=x.`rtk_encrypt<=y.`rtk_encrypt /\ 0<=x.`rtk_trit<=y.`rtk_trit /\
 0<=x.`rtk_poly_compare<=y.`rtk_poly_compare /\
 0<=x.`rtk_cipher_compare<=y.`rtk_cipher_compare /\
 0<=x.`rtk_psi_draw<=y.`rtk_psi_draw /\ 0<=x.`rtk_adversary<=y.`rtk_adversary.

lemma rtk_add_upper x y X Y : rtk_le x X=>rtk_le y Y=>
 rtk_le(rtk_add x y)(rtk_add X Y).
proof. rewrite /rtk_le /rtk_add /rtk_profile /=;smt(). qed.
lemma rtk_add_zero x : rtk_add x(rtk_profile 0 0 0 0 0 0 0 0 0 0)=x.
proof. by case x=> />;rewrite /rtk_add /rtk_profile /=. qed.
