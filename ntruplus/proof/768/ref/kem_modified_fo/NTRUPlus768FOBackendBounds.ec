require import AllCore List Distr.
from Jasmin require import JWord.
require import Array32 Array1152.
require import NTRUPlus768ROMOracles NTRUPlus768RawXOFStreams NTRUPlus768CCADecapOracle.
require import NTRUPlus768CCAGame NTRUPlus768FOModel NTRUPlus768FOError.
require import NTRUPlus768FOKEMGame NTRUPlus768FOQueryBudget NTRUPlus768FOHMonitor.
require import NTRUPlus768FOBackendContracts NTRUPlus768FOBadBound.

(* These are the actual backend instances of the shared H/D accounting
   theorem. The event is bad at return; adversary termination is neither
   inferred from the cap nor needed for this partial-mass upper bound. *)
lemma fo_native_bounded_bad
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState})
 w0 g0 q0 pk0 ct0 key0 &m :
 0<=q0 =>FOContext.w{m}=w0 =>FOContext.g{m}=g0 =>
 Pr[FOBadPhase(A,FONativeBackend).run(q0,pk0,ct0,key0) @ &m:FOBadState.bad]
 <=q0%r*fo_error w0 g0.
proof.
 move=>hq hw hg.
 apply(fo_bounded_phase_bad A FONativeBackend w0 g0 q0 pk0 ct0 key0 &m hq hw hg).
 + move=>b; exact(fo_shared_e_frame w0 g0 b).
 + move=>b; exact(fo_shared_f_frame w0 g0 b).
 + move=>b; exact(fo_shared_g_frame w0 g0 b).
 + move=>b; exact(fo_hmonitor_frame w0 g0 b).
 + move=>b; exact(fo_raw_get_frame w0 g0 b).
 + move=>b; exact(fo_raw_get_non_h_frame w0 g0 b).
 + move=>b; exact(fo_native_decap_frame w0 g0 b).
 + exact(fo_hmonitor_bad_bound w0 g0).
 + exact(fo_raw_get_bad_bound w0 g0).
 exact(fo_native_decap_bad_bound w0 g0).
qed.

lemma fo_full_bounded_bad
 (A<:CCAExtendedAdversary {-ROE,-ROF,-ROG,-ROH,-RawXOFStreams,-CCADecapOracle,
   -FOPublicKey,-FOContext,-FOBadState,-FOBudgetState})
 w0 g0 q0 pk0 ct0 key0 &m :
 0<=q0 =>FOContext.w{m}=w0 =>FOContext.g{m}=g0 =>
 Pr[FOBadPhase(A,FOFullBackend).run(q0,pk0,ct0,key0) @ &m:FOBadState.bad]
 <=q0%r*fo_error w0 g0.
proof.
 move=>hq hw hg.
 apply(fo_bounded_phase_bad A FOFullBackend w0 g0 q0 pk0 ct0 key0 &m hq hw hg).
 + move=>b; exact(fo_shared_e_frame w0 g0 b).
 + move=>b; exact(fo_shared_f_frame w0 g0 b).
 + move=>b; exact(fo_shared_g_frame w0 g0 b).
 + move=>b; exact(fo_hmonitor_frame w0 g0 b).
 + move=>b; exact(fo_raw_get_frame w0 g0 b).
 + move=>b; exact(fo_raw_get_non_h_frame w0 g0 b).
 + move=>b; exact(fo_full_decap_frame w0 g0 b).
 + exact(fo_hmonitor_bad_bound w0 g0).
 + exact(fo_raw_get_bad_bound w0 g0).
 exact(fo_full_decap_bad_bound w0 g0).
qed.
