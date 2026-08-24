require import AllCore IntDiv Ring StdOrder.
from Jasmin require import JWord.

require import Array192 Array768.
require import NTRUPlus768PolyCBD1Algebra.
require import NTRUPlus768NTTAlgebra.
require import NTRUPlus768KeygenSamplerAlgebra.

(* Typed value flow from the two CBD1 inputs through coefficient shaping and
   the verified forward NTT.  poly_baseinv and all inverse conclusions are
   deliberately outside this theory. *)

op keygen_f_ntt_spec (buf : W8.t Array192.t) : W16.t Array768.t =
  NTRUPlus768NTTAlgebra.forward_ntt_spec
    (keygen_f_pre_ntt_spec buf).

op keygen_g_ntt_spec (buf : W8.t Array192.t) : W16.t Array768.t =
  NTRUPlus768NTTAlgebra.forward_ntt_spec
    (keygen_g_pre_ntt_spec buf).

op keygen_sampler_value_flow
    (fbuf gbuf : W8.t Array192.t)
    (fsample gsample fpre gpre fntt gntt : W16.t Array768.t) : bool =
  fsample = NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec fbuf /\
  gsample = NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec gbuf /\
  fpre = keygen_f_pre_ntt_spec fbuf /\
  gpre = keygen_g_pre_ntt_spec gbuf /\
  keygen_f_mod3_shape fpre /\
  keygen_g_mod3_shape gpre /\
  keygen_f_small_shape fpre /\
  keygen_g_small_shape gpre /\
  fntt = keygen_f_ntt_spec fbuf /\
  gntt = keygen_g_ntt_spec gbuf /\
  NTRUPlus768NTTAlgebra.forward_ntt_algebra fpre fntt /\
  NTRUPlus768NTTAlgebra.forward_ntt_algebra gpre gntt.

lemma keygen_f_ntt_algebra (buf : W8.t Array192.t) :
  NTRUPlus768NTTAlgebra.forward_ntt_algebra
    (keygen_f_pre_ntt_spec buf) (keygen_f_ntt_spec buf).
proof.
  rewrite /keygen_f_ntt_spec.
  exact
    (NTRUPlus768NTTAlgebra.forward_ntt_spec_algebra
      (keygen_f_pre_ntt_spec buf)
      (keygen_f_pre_ntt_input_qrange buf)).
qed.

lemma keygen_g_ntt_algebra (buf : W8.t Array192.t) :
  NTRUPlus768NTTAlgebra.forward_ntt_algebra
    (keygen_g_pre_ntt_spec buf) (keygen_g_ntt_spec buf).
proof.
  rewrite /keygen_g_ntt_spec.
  exact
    (NTRUPlus768NTTAlgebra.forward_ntt_spec_algebra
      (keygen_g_pre_ntt_spec buf)
      (keygen_g_pre_ntt_input_qrange buf)).
qed.

lemma keygen_f_ntt_centered_output (buf : W8.t Array192.t) :
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape
    (keygen_f_ntt_spec buf).
proof.
  rewrite /keygen_f_ntt_spec.
  exact
    (NTRUPlus768NTTAlgebra.forward_ntt_centered_output_shape
      (keygen_f_pre_ntt_spec buf)
      (keygen_f_pre_ntt_input_qrange buf)).
qed.

lemma keygen_g_ntt_centered_output (buf : W8.t Array192.t) :
  NTRUPlus768NTTRadix2_4Algebra.centered_input_shape
    (keygen_g_ntt_spec buf).
proof.
  rewrite /keygen_g_ntt_spec.
  exact
    (NTRUPlus768NTTAlgebra.forward_ntt_centered_output_shape
      (keygen_g_pre_ntt_spec buf)
      (keygen_g_pre_ntt_input_qrange buf)).
qed.

lemma keygen_sampler_value_flow_intro
    (fbuf gbuf : W8.t Array192.t) :
  keygen_sampler_value_flow
    fbuf gbuf
    (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec fbuf)
    (NTRUPlus768PolyCBD1Algebra.poly_cbd1_spec gbuf)
    (keygen_f_pre_ntt_spec fbuf)
    (keygen_g_pre_ntt_spec gbuf)
    (keygen_f_ntt_spec fbuf)
    (keygen_g_ntt_spec gbuf).
proof.
  rewrite /keygen_sampler_value_flow.
  split; first done.
  split; first done.
  split; first done.
  split; first done.
  split; first exact (keygen_f_pre_ntt_mod3 fbuf).
  split; first exact (keygen_g_pre_ntt_mod3 gbuf).
  split; first exact (keygen_f_pre_ntt_small fbuf).
  split; first exact (keygen_g_pre_ntt_small gbuf).
  split; first done.
  split; first done.
  split; first exact (keygen_f_ntt_algebra fbuf).
  exact (keygen_g_ntt_algebra gbuf).
qed.
