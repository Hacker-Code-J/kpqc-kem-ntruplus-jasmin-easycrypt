require import AllCore List.
from Jasmin require import JWord.
require import Array32 Array96 Array129 Array1152 Array1153.

(* Exactly the honest SHAKE query domains. Invalid raw prefixes carry no
   cross-port identification claim. E is unprefixed and distinguished by
   its 32-byte length; F/G have equal lengths and distinct tags. *)
op encode_f (pk : W8.t Array1152.t) : W8.t Array1153.t =
  Array1153.init (fun i => if i = 0 then W8.zero else pk.[i-1]).
op encode_g (serialized : W8.t Array1152.t) : W8.t Array1153.t =
  Array1153.init (fun i => if i = 0 then W8.one else serialized.[i-1]).
op encode_h (coins : W8.t Array96.t) (pkhash : W8.t Array32.t) : W8.t Array129.t =
  Array129.init (fun i => if i = 0 then W8.of_int 2 else
    if i <= 96 then coins.[i-1] else pkhash.[i-97]).
op peel1153 (input : W8.t Array1153.t) : W8.t Array1152.t =
  Array1152.init (fun i => input.[i+1]).
op peel_h (input : W8.t Array129.t) : W8.t Array96.t * W8.t Array32.t =
  (Array96.init (fun i => input.[i+1]),
   Array32.init (fun i => input.[i+97])).

lemma peel_encode_f pk : peel1153 (encode_f pk) = pk.
proof.
  apply Array1152.tP=> i hi.
  rewrite /peel1153 /encode_f Array1152.initiE //.
  rewrite /= Array1153.initiE 1:/#; smt().
qed.
lemma peel_encode_g serialized : peel1153 (encode_g serialized) = serialized.
proof.
  apply Array1152.tP=> i hi.
  rewrite /peel1153 /encode_g Array1152.initiE //.
  rewrite /= Array1153.initiE 1:/#; smt().
qed.
lemma peel_encode_h coins pkhash : peel_h (encode_h coins pkhash) = (coins,pkhash).
proof.
  rewrite /peel_h /encode_h; congr.
  + apply Array96.tP=> i hi.
    rewrite Array96.initiE //; rewrite /= Array129.initiE 1:/#; smt().
  apply Array32.tP=> i hi.
  rewrite Array32.initiE //; rewrite /= Array129.initiE 1:/#; smt().
qed.
lemma encode_peel_f input : input.[0] = W8.zero => encode_f (peel1153 input) = input.
proof.
  move=> ht; apply Array1153.tP=> i hi.
  rewrite /encode_f Array1153.initiE //.
  case (i=0)=> hz; first by rewrite hz ht.
  rewrite /peel1153 Array1152.initiE 1:/#; smt().
qed.
lemma encode_peel_g input : input.[0] = W8.one => encode_g (peel1153 input) = input.
proof.
  move=> ht; apply Array1153.tP=> i hi.
  rewrite /encode_g Array1153.initiE //.
  case (i=0)=> hz; first by rewrite hz ht.
  rewrite /peel1153 Array1152.initiE 1:/#; smt().
qed.
lemma encode_peel_h input : input.[0] = W8.of_int 2 =>
  encode_h (peel_h input).`1 (peel_h input).`2 = input.
proof.
  move=> ht; apply Array129.tP=> i hi.
  rewrite /encode_h Array129.initiE // /peel_h /=.
  case (i=0)=> hz; first by rewrite hz ht.
  case (i<=96)=> hc.
  + rewrite Array96.initiE 1:/#; smt().
  rewrite Array32.initiE 1:/#; smt().
qed.
lemma encode_f_tag pk : (encode_f pk).[0] = W8.zero.
proof. by rewrite /encode_f Array1153.initiE. qed.
lemma encode_g_tag serialized : (encode_g serialized).[0] = W8.one.
proof. by rewrite /encode_g Array1153.initiE. qed.
lemma encode_h_tag coins pkhash : (encode_h coins pkhash).[0] = W8.of_int 2.
proof. by rewrite /encode_h Array129.initiE. qed.
lemma tag_zero_neq_one : W8.zero <> W8.one.
proof.
  have h : W8.to_uint W8.zero <> W8.to_uint W8.one by trivial.
  smt().
qed.
lemma encode_f_inj : injective encode_f.
proof.
  move=> x y he.
  have h := congr1 peel1153 _ _ he.
  by rewrite !peel_encode_f in h.
qed.
lemma encode_g_inj : injective encode_g.
proof.
  move=> x y he.
  have h := congr1 peel1153 _ _ he.
  by rewrite !peel_encode_g in h.
qed.
lemma encode_h_inj coins pkhash coins' pkhash' :
  encode_h coins pkhash = encode_h coins' pkhash' => (coins,pkhash)=(coins',pkhash').
proof. by move=> he; have := congr1 peel_h _ _ he; rewrite !peel_encode_h. qed.
lemma encode_f_g_disjoint pk serialized : encode_f pk <> encode_g serialized.
proof.
  apply/negP=> he; have := congr1 (fun x : W8.t Array1153.t => x.[0]) _ _ he.
  by rewrite /= encode_f_tag encode_g_tag; exact tag_zero_neq_one.
qed.

type typed_query = [ E of W8.t Array32.t | F of W8.t Array1152.t |
  G of W8.t Array1152.t | H of (W8.t Array96.t * W8.t Array32.t) ].
op raw_query (q : typed_query) : W8.t list =
  with q = E seed => Array32.to_list seed
  with q = F pk => Array1153.to_list (encode_f pk)
  with q = G serialized => Array1153.to_list (encode_g serialized)
  with q = H payload => Array129.to_list (encode_h payload.`1 payload.`2).

lemma raw_query_inj : injective raw_query.
proof.
  move=> q q'; case q; case q';
  simplify;
  smt(Array32.to_list_inj Array1153.to_list_inj Array129.to_list_inj
    Array32.size_to_list Array1153.size_to_list Array129.size_to_list
    encode_f_inj encode_g_inj encode_h_inj encode_f_g_disjoint).
qed.

lemma raw_e_length seed : size (raw_query (E seed)) = 32.
proof. smt(Array32.size_to_list). qed.
lemma raw_f_length pk : size (raw_query (F pk)) = 1153.
proof. smt(Array1153.size_to_list). qed.
lemma raw_g_length serialized : size (raw_query (G serialized)) = 1153.
proof. smt(Array1153.size_to_list). qed.
lemma raw_h_length payload : size (raw_query (H payload)) = 129.
proof. smt(Array129.size_to_list). qed.
lemma raw_domains_disjoint q1 q2 :
  q1 <> q2 => raw_query q1 <> raw_query q2.
proof.
  move=> hn; apply/negP=> he.
  have hq := raw_query_inj q1 q2 he.
  by move: hn; rewrite hq.
qed.
lemma rom_domains_eof : injective raw_query.
proof. exact raw_query_inj. qed.
