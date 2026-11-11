require import AllCore.

(* The transformed value before multiplication and the value passed to the
   inverse may use different scales. Their representation relations and
   bounds are deliberately separate. No ring or correctness law is assumed. *)

type polynomial, coefficient_buffer, transform_buffer.

op polynomial_product : polynomial -> polynomial -> polynomial.
op input_rep : coefficient_buffer -> polynomial -> bool.
op forward_rep : transform_buffer -> polynomial -> bool.
op product_rep : transform_buffer -> polynomial -> bool.
op output_rep : coefficient_buffer -> polynomial -> bool.
op input_bound : coefficient_buffer -> bool.
op forward_bound : transform_buffer -> bool.
op inverse_bound : transform_buffer -> bool.
op output_bound : coefficient_buffer -> bool.

module type Kernels = {
  proc forward(x:coefficient_buffer) : transform_buffer
  proc multiply(x:transform_buffer, y:transform_buffer) : transform_buffer
  proc inverse(x:transform_buffer) : coefficient_buffer
}.

module Product(K:Kernels) = {
  proc run(x:coefficient_buffer, y:coefficient_buffer) : coefficient_buffer = {
    var a,b,t:transform_buffer;
    var r:coefficient_buffer;
    a <@ K.forward(x);
    b <@ K.forward(y);
    t <@ K.multiply(a,b);
    r <@ K.inverse(t);
    return r;
  }
}.

lemma composition_total (K <: Kernels) (p q:polynomial) :
  (forall a, phoare[K.forward : input_rep x a /\ input_bound x ==>
    forward_rep res a /\ forward_bound res] = 1%r) =>
  (forall a b, phoare[K.multiply :
    forward_rep x a /\ forward_bound x /\ forward_rep y b /\ forward_bound y ==>
    product_rep res (polynomial_product a b) /\ inverse_bound res] = 1%r) =>
  (forall a, phoare[K.inverse : product_rep x a /\ inverse_bound x ==>
    output_rep res a /\ output_bound res] = 1%r) =>
  phoare[Product(K).run :
    input_rep x p /\ input_bound x /\ input_rep y q /\ input_bound y ==>
    output_rep res (polynomial_product p q) /\ output_bound res] = 1%r.
proof.
move=> hf hm hi.
proc.
conseq (_ : _ ==> _ : >=1%r) => //.
seq 1 : (forward_rep a p /\ forward_bound a /\ input_rep y q /\ input_bound y) => //.
+ conseq (_ : _ ==> _ : =1%r) => //.
  call (hf p); skip; smt().
seq 1 : (forward_rep a p /\ forward_bound a /\ forward_rep b q /\ forward_bound b) => //.
+ conseq (_ : _ ==> _ : =1%r) => //.
  call (hf q); skip; smt().
seq 1 : (product_rep t (polynomial_product p q) /\ inverse_bound t) => //.
+ conseq (_ : _ ==> _ : =1%r) => //.
  call (hm p q); skip; smt().
conseq (_ : _ ==> _ : =1%r) => //.
call (hi (polynomial_product p q)); skip; smt().
qed.
