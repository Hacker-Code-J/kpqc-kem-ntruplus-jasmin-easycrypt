require import AllCore IntDiv List Distr DList DBool StdOrder StdBigop Finite RealSeries.
from Jasmin require import JWord JUtils.
require import Array192 Array768.
require import NTRUPlus768ROMDistributions NTRUPlus768PolyCBD1Algebra NTRUPlus768PolySOTPDecodeAlgebra.
require import JWordList.
require import NTRUPlus768CBDTensor.
import RField RealOrder Bigreal.

(* This distribution describes unconditioned CBD1 coefficients only. *)
op [opaque] dcbd : int distr = dmap (duniform [0;1;2;3])
 (fun u=>if u=0 then -1 else if u=3 then 1 else 0).
type cbd_quad = (int * int) * (int * int).
op [opaque] dcbd_quad : cbd_quad distr = (dcbd `*` dcbd) `*` (dcbd `*` dcbd).

op cbd_coeff_list (buf:W8.t Array192.t) = mkseq (poly_cbd1_coeff_int buf) 768.
op cbd_pair_blocks (perm:int -> int) (buffers:W8.t Array192.t * W8.t Array192.t) =
 mkseq (fun i=>
  ((poly_cbd1_coeff_int buffers.`1 i,poly_cbd1_coeff_int buffers.`1 (i+384)),
   (poly_cbd1_coeff_int buffers.`2 (perm i),poly_cbd1_coeff_int buffers.`2 (perm i+384)))) 384.
op cbd_buffer_bits (buf:W8.t Array192.t) = bytes_to_bits (Array192.to_list buf).
op cbd_trit_of_bits (xs:bool list) = b2i(nth false xs 0)-b2i(nth false xs 1).

lemma dcbd_ll : is_lossless dcbd.
proof. rewrite /dcbd; apply/dmap_ll/duniform_ll; done. qed.
lemma dcbd_finite : is_finite(support dcbd).
proof.
 rewrite /dcbd /dmap.
 apply finite_dlet; first exact (finite_duniform [0;1;2;3]).
 move=>x hx; exact (finite_dunit _).
qed.
lemma dcbd_quad_ll : is_lossless dcbd_quad.
proof. rewrite /dcbd_quad !dprod_ll; smt(dcbd_ll). qed.
lemma dcbd_quad_finite : is_finite(support dcbd_quad).
proof.
 rewrite /dcbd_quad; apply finite_dprod;
 apply finite_dprod; exact dcbd_finite.
qed.
lemma dcbdE (event:int -> bool) :
 mu dcbd event =
 (if event (-1) then 1%r/4%r else 0%r)+
 (if event 0 then 1%r/2%r else 0%r)+
 (if event 1 then 1%r/4%r else 0%r).
proof.
 rewrite /dcbd dmapE /(\o) duniformE /=.
 case(event(-1)); case(event 0); case(event 1); rewrite /b2i /=; smt().
qed.
lemma dcbd_point x :
 mu1 dcbd x = if x= -1 then 1%r/4%r else if x=0 then 1%r/2%r
  else if x=1 then 1%r/4%r else 0%r.
proof. rewrite dcbdE /pred1; smt(). qed.

lemma dcbd_bits2 : dmap (dlist dbool 2) cbd_trit_of_bits=dcbd.
proof.
 rewrite (_:2=1+1) 1:// dlistS // dlist1 dmap_dprodR !dmap_comp.
 rewrite dmap_dprodE; apply eq_distr=>x.
 rewrite dlet1E sum_bool /= !dbool1E !dmap1E /(\o) /cbd_trit_of_bits /= !dboolE /= dcbd_point.
 smt().
qed.

lemma cbd_byte_bits_law : W8.dword=dmap (dlist dbool 8) W8.bits2w.
proof.
 apply eq_distr=>w; rewrite byte_uniform_point dmap1E /(\o) /=.
 rewrite (mu_eq_support _ _ (pred1 (W8.w2bits w))).
 + move=>xs; rewrite supp_dlist //=; move=>[hs _].
   apply eq_iff; split=>h.
   - by rewrite -h W8.bits2wK.
   by rewrite h W8.w2bitsK.
 rewrite dlist1E // W8.size_w2bits /=.
 rewrite (Bigreal.BRM.eq_bigr _ _ (fun _=>1%r/2%r)).
 + by move=>b hb; rewrite /= dbool1E.
 rewrite Bigreal.mulr_const W8.size_w2bits /max /=.
 by rewrite exprVn // fromintXn.
qed.

lemma cbd_byte_to_bits_law : dmap W8.dword W8.w2bits=dlist dbool 8.
proof.
 rewrite cbd_byte_bits_law dmap_comp.
 rewrite -{2}(dmap_id (dlist dbool 8)).
 apply eq_dmap_in=>xs hs; rewrite /(\o) /= W8.bits2wK; first
  exact (supp_dlist_size dbool 8 xs _ hs).
 done.
qed.

lemma cbd_buffer_bits_uniform : dmap uniform192 cbd_buffer_bits=dlist dbool 1536.
proof.
 rewrite /uniform192 dmap_comp.
 have he:
  dmap (dlist W8.dword 192) (cbd_buffer_bits \o Array192.of_list W8.zero)=
  dmap (dlist W8.dword 192) bytes_to_bits.
 + apply eq_dmap_in=>xs hs; rewrite /(\o) /cbd_buffer_bits /=.
   have hz:=supp_dlist_size W8.dword 192 xs _ hs; first trivial.
   by rewrite Array192.of_listK.
 rewrite he /bytes_to_bits.
 change (dmap (dlist W8.dword 192) (flatten \o map W8.w2bits)=dlist dbool 1536).
 rewrite -dmap_comp -dlist_dmap cbd_byte_to_bits_law.
 by rewrite dlist_dlist.
qed.

lemma cbd_buffer_bits_nth buf k :
 0<=k<1536 => nth false (cbd_buffer_bits buf) k=(buf.[k %/ 8]).[k %% 8].
proof.
 move=>hk; rewrite /cbd_buffer_bits nth_bytes_to_bits.
 + by rewrite Array192.size_to_list; smt().
 rewrite (nth_change_dfl witness W8.zero (Array192.to_list buf) (k %/ 8)).
 + rewrite Array192.size_to_list; smt(IntDiv.edivzP IntDiv.modz_ge0 IntDiv.ltz_pmod).
 by rewrite Array192.get_to_list -W8.get_w2bits.
qed.
lemma cbd_coeff_from_bits buf k :
 0<=k<768 => poly_cbd1_coeff_int buf k=
 b2i(nth false (cbd_buffer_bits buf) k)-b2i(nth false (cbd_buffer_bits buf) (768+k)).
proof.
 move=>hk; rewrite !cbd_buffer_bits_nth 1,2:/#.
 rewrite /poly_cbd1_coeff_int /poly_cbd1_head_bit /poly_cbd1_tail_bit /poly_cbd1_bit /poly_sotp_bit.
 have hd:(768+k) %/ 8=96+k %/ 8 by smt(IntDiv.edivzP IntDiv.modz_ge0 IntDiv.ltz_pmod).
 have hm:(768+k) %% 8=k %% 8 by smt(IntDiv.modzDml).
 by rewrite hd hm !W8.b2i_get ~-1:/#.
qed.

op cbd_from_bits (bs:bool list) =
 mkseq (fun i=>b2i(nth false bs i)-b2i(nth false bs (768+i))) 768.
op cbd_interleave_index (i:int) = if i %% 2=0 then i %/ 2 else 768+i %/ 2.
op cbd_interleave (bs:bool list) = mkseq (fun i=>nth false bs (cbd_interleave_index i)) 1536.
op cbd_adjacent (bs:bool list) =
 mkseq (fun i=>b2i(nth false bs (2*i))-b2i(nth false bs (2*i+1))) 768.

lemma cbd_coeff_list_from_bits buf : cbd_coeff_list buf=cbd_from_bits(cbd_buffer_bits buf).
proof.
 rewrite /cbd_coeff_list /cbd_from_bits; apply eq_in_mkseq=>i hi.
 exact(cbd_coeff_from_bits buf i hi).
qed.
lemma cbd_interleave_even i : cbd_interleave_index (2*i)=i.
proof. rewrite /cbd_interleave_index; smt(IntDiv.edivzP IntDiv.modz_ge0 IntDiv.ltz_pmod). qed.
lemma cbd_interleave_odd i : cbd_interleave_index (2*i+1)=768+i.
proof. rewrite /cbd_interleave_index; smt(IntDiv.edivzP IntDiv.modz_ge0 IntDiv.ltz_pmod). qed.
lemma cbd_interleave_range i : 0<=i<1536 => 0<=cbd_interleave_index i<1536.
proof. rewrite /cbd_interleave_index; smt(IntDiv.edivzP IntDiv.modz_ge0 IntDiv.ltz_pmod). qed.
lemma cbd_interleave_inj i j :
 0<=i<1536 => 0<=j<1536 => cbd_interleave_index i=cbd_interleave_index j => i=j.
proof. rewrite /cbd_interleave_index; smt(IntDiv.edivzP IntDiv.modz_ge0 IntDiv.ltz_pmod). qed.
lemma cbd_interleave_uniform :
 dmap (dlist dbool 1536) cbd_interleave=dlist dbool 1536.
proof.
 apply (dmap_dlist_partial_perm false dbool cbd_interleave_index 1536 1536) => //.
 + exact dbool_ll.
 + exact cbd_interleave_inj.
 exact cbd_interleave_range.
qed.
lemma cbd_from_bits_interleave bs : cbd_from_bits bs=cbd_adjacent(cbd_interleave bs).
proof.
 rewrite /cbd_from_bits /cbd_adjacent; apply eq_in_mkseq=>i hi /=.
 by rewrite /cbd_interleave !nth_mkseq ~-1:/# /= cbd_interleave_even cbd_interleave_odd.
qed.

lemma cbd_adjacent_flatten (xs:bool list list) :
 size xs=768 => (forall x,x \in xs=>size x=2) =>
 cbd_adjacent(flatten xs)=map cbd_trit_of_bits xs.
proof.
 move=>hs hx; apply(eq_from_nth 0).
 + by rewrite /cbd_adjacent size_mkseq size_map hs.
 move=>i hi; rewrite /cbd_adjacent size_mkseq /= in hi.
 rewrite /cbd_adjacent nth_mkseq //= (nth_map []) 1:/# /cbd_trit_of_bits /=.
 have hall:all (fun x:bool list=>size x=2) xs by rewrite allP; exact hx.
 rewrite (BitEncoding.BitChunking.nth_flatten false 2 xs (2*i) hall).
 rewrite (BitEncoding.BitChunking.nth_flatten false 2 xs (2*i+1) hall).
 have he:(2*i) %/ 2=i /\ (2*i) %% 2=0 /\ (2*i+1) %/ 2=i /\ (2*i+1) %% 2=1
  by smt(IntDiv.edivzP IntDiv.modz_ge0 IntDiv.ltz_pmod).
 by move:he=>[-> [-> [-> ->]]].
qed.

lemma cbd_adjacent_uniform : dmap (dlist dbool 1536) cbd_adjacent=dlist dcbd 768.
proof.
 have hf:=dlist_dlist dbool 2 768 _ _; first 2 trivial.
 rewrite /= in hf; rewrite -hf dmap_comp.
 have hm:dmap (dlist (dlist dbool 2) 768) (cbd_adjacent \o flatten)=
  dmap (dlist (dlist dbool 2) 768) (map cbd_trit_of_bits).
 + apply eq_dmap_in=>xs hs; rewrite /(\o).
   have hnall:size xs=768 /\ all (support (dlist dbool 2)) xs.
   - by move:hs; rewrite supp_dlist.
   move:hnall=>[hn hall].
   apply(cbd_adjacent_flatten xs hn)=>x hx.
   have hh: x \in dlist dbool 2 by move:hall; rewrite allP=>h; exact(h x hx).
   exact(supp_dlist_size dbool 2 x _ hh).
 rewrite hm -dlist_dmap dcbd_bits2; done.
qed.

lemma cbd_coeff_list_uniform : dmap uniform192 cbd_coeff_list=dlist dcbd 768.
proof.
 have he:cbd_coeff_list=cbd_from_bits \o cbd_buffer_bits
  by apply fun_ext=>buf; exact(cbd_coeff_list_from_bits buf).
 have hh:cbd_from_bits=cbd_adjacent \o cbd_interleave
  by apply fun_ext=>bs; exact(cbd_from_bits_interleave bs).
 by rewrite he -dmap_comp cbd_buffer_bits_uniform hh -dmap_comp cbd_interleave_uniform cbd_adjacent_uniform.
qed.

op cbd_word_array (xs:int list) : W16.t Array768.t =
 Array768.of_list W16.zero (map W16.of_int xs).

lemma cbd_word_array_coeff_list buf : cbd_word_array(cbd_coeff_list buf)=poly_cbd1_spec buf.
proof.
 apply Array768.tP=>i hi.
 rewrite /cbd_word_array /cbd_coeff_list /poly_cbd1_spec Array768.get_of_list 1:hi Array768.initiE 1:hi.
 rewrite (nth_map 0).
 + rewrite size_mkseq; smt().
 by rewrite nth_mkseq.
qed.

lemma cbd_poly_uniform :
 dmap uniform192 poly_cbd1_spec=dmap (dlist dcbd 768) cbd_word_array.
proof.
 have he:poly_cbd1_spec=cbd_word_array \o cbd_coeff_list.
 + apply fun_ext=>buf; apply/eq_sym; exact(cbd_word_array_coeff_list buf).
 by rewrite he -dmap_comp cbd_coeff_list_uniform.
qed.

lemma cbd_pair_coeff_lists_uniform :
 dmap (uniform192 `*` uniform192)
  (fun buffers:W8.t Array192.t * W8.t Array192.t=>
    (cbd_coeff_list buffers.`1,cbd_coeff_list buffers.`2))=
 (dlist dcbd 768 `*` dlist dcbd 768).
proof. by rewrite -dmap_dprod !cbd_coeff_list_uniform. qed.

lemma cbd_pair_blocks_coeff_lists perm buffers :
 (forall i,0<=i<384=>0<=perm i<384) =>
 cbd_pair_blocks perm buffers=
 paired_halves_tensor 0 384 perm (cbd_coeff_list buffers.`1,cbd_coeff_list buffers.`2).
proof.
 move=>hr; rewrite /cbd_pair_blocks /paired_halves_tensor.
 apply eq_in_mkseq=>i hi /=; have hp:=hr i hi.
 by rewrite /cbd_coeff_list !nth_mkseq ~-1:/#.
qed.

(* The four entries of each block are independent before key acceptance.
   The ordering matches the paired halves in the quotient convolution. *)
lemma cbd_pair_blocks_uniform perm :
 (forall i j,0<=i<384=>0<=j<384=>perm i=perm j=>i=j) =>
 (forall i,0<=i<384=>0<=perm i<384) =>
 dmap (uniform192 `*` uniform192) (cbd_pair_blocks perm)=dlist dcbd_quad 384.
proof.
 move=>hi hr.
 have he:cbd_pair_blocks perm=paired_halves_tensor 0 384 perm \o
  (fun buffers:W8.t Array192.t * W8.t Array192.t=>
    (cbd_coeff_list buffers.`1,cbd_coeff_list buffers.`2)).
 + apply fun_ext=>buffers; exact(cbd_pair_blocks_coeff_lists perm buffers hr).
 rewrite he -dmap_comp cbd_pair_coeff_lists_uniform /dcbd_quad.
 exact(paired_halves_tensor_law dcbd 0 384 perm _ dcbd_ll hi hr).
qed.

op cbd_rotate_four ['a] (bs:('a * 'a) * ('a * 'a)) =
 ((bs.`1.`2,bs.`2.`1),(bs.`2.`2,bs.`1.`1)).

lemma cbd_rotate_four_uniform ['a] (d:'a distr) :
 dmap ((d `*` d) `*` (d `*` d)) cbd_rotate_four=((d `*` d) `*` (d `*` d)).
proof.
 apply eq_distr=>bs.
 rewrite (dmap1E_can _ _
  (fun bs:('a * 'a) * ('a * 'a)=>((bs.`2.`2,bs.`1.`1),(bs.`1.`2,bs.`2.`1)))).
 + by move=>[[a b][c e]]; rewrite /cbd_rotate_four /=.
 + by move=>[[a b][c e]] _; rewrite /cbd_rotate_four /=.
 case:bs=>[[a b][c e]]; rewrite !dprod1E /=; ring.
qed.

op cbd_four_blocks (perm:int -> int)
 (bs:(W8.t Array192.t * W8.t Array192.t) * (W8.t Array192.t * W8.t Array192.t)) =
 cbd_pair_blocks perm (bs.`1.`2,bs.`2.`1) ++
 cbd_pair_blocks perm (bs.`2.`2,bs.`1.`1).

lemma cbd_four_blocks_uniform perm :
 (forall i j,0<=i<384=>0<=j<384=>perm i=perm j=>i=j) =>
 (forall i,0<=i<384=>0<=perm i<384) =>
 dmap ((uniform192 `*` uniform192) `*` (uniform192 `*` uniform192))
  (cbd_four_blocks perm)=dlist dcbd_quad 768.
proof.
 move=>hi hr.
 have he:cbd_four_blocks perm=
  (fun bs:(W8.t Array192.t * W8.t Array192.t) * (W8.t Array192.t * W8.t Array192.t)=>
   cbd_pair_blocks perm bs.`1 ++ cbd_pair_blocks perm bs.`2) \o cbd_rotate_four.
 + by apply fun_ext=>bs; rewrite /cbd_four_blocks /cbd_rotate_four /(\o).
 rewrite he -dmap_comp cbd_rotate_four_uniform.
 rewrite (dmap_dprod_comp (uniform192 `*` uniform192) (uniform192 `*` uniform192)
  (cbd_pair_blocks perm) (cbd_pair_blocks perm) (fun xs ys=>xs++ys)).
 rewrite !(cbd_pair_blocks_uniform perm hi hr).
 by rewrite -dlist_add.
qed.
