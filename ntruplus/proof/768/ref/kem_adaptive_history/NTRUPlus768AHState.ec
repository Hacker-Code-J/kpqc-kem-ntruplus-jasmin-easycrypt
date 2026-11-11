require import AllCore List FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array224 Array1152.
require import NTRUPlus768FOModel NTRUPlus768HistModel.

type ah_state = {
 ah_rows:hist_table;
 ah_pk:W8.t Array1152.t;
 ah_suffix:W8.t Array32.t;
 ah_cstar:W8.t Array1152.t option;
}.
op [opaque] ah_initial pk suffix star : ah_state =
 {|ah_rows=[];ah_pk=pk;ah_suffix=suffix;ah_cstar=star|}.
op [opaque] ah_with_rows (st:ah_state) (rows:hist_table) : ah_state =
 {|ah_rows=rows;ah_pk=st.`ah_pk;ah_suffix=st.`ah_suffix;ah_cstar=st.`ah_cstar|}.
op [opaque] ah_record_state (st:ah_state) input hout =
 ah_with_rows st (hist_put input hout st.`ah_rows).
op [opaque] ah_context (st:ah_state) = (st.`ah_pk,st.`ah_suffix,st.`ah_cstar).

(* The algorithms access state only through procedures. A concrete local
   store declared after the original adversary supplies these operations.
   record must call HistTable.put; ah_record_state is its specification. *)
module type AHStore = {
 proc init(pk:W8.t Array1152.t,suffix:W8.t Array32.t,cstar:W8.t Array1152.t option):unit
 proc snapshot():ah_state
 proc record(input:fo_h_input,hout:W8.t Array224.t):unit
}.

lemma ah_initial_rows pk suffix star : (ah_initial pk suffix star).`ah_rows=[].
proof. by rewrite /ah_initial. qed.
lemma ah_initial_context pk suffix star : ah_context(ah_initial pk suffix star)=(pk,suffix,star).
proof. by rewrite /ah_context /ah_initial. qed.
lemma ah_initial_rep pk suffix star : hist_rep(ah_initial pk suffix star).`ah_rows empty.
proof. rewrite ah_initial_rows;exact hist_rep_empty. qed.
lemma ah_with_rows_fields st rows :
 (ah_with_rows st rows).`ah_rows=rows /\ ah_context(ah_with_rows st rows)=ah_context st.
proof. by rewrite /ah_with_rows /ah_context. qed.
lemma ah_record_context st input hout : ah_context(ah_record_state st input hout)=ah_context st.
proof. by rewrite /ah_record_state /ah_with_rows /ah_context. qed.
lemma ah_record_rep st input hout table : hist_rep st.`ah_rows table=>
 hist_rep(ah_record_state st input hout).`ah_rows table.[input<-hout].
proof. rewrite /ah_record_state /ah_with_rows /=;exact(hist_rep_put input hout st.`ah_rows table). qed.
lemma ah_record_unique st input hout : hist_unique st.`ah_rows=>
 hist_unique(ah_record_state st input hout).`ah_rows.
proof. rewrite /ah_record_state /ah_with_rows /=;exact(hist_put_unique input hout st.`ah_rows). qed.
lemma ah_record_size st input hout :
 size(ah_record_state st input hout).`ah_rows<=size st.`ah_rows+1.
proof. rewrite /ah_record_state /ah_with_rows /=;exact(hist_put_size_bound input hout st.`ah_rows). qed.
lemma ah_record_get st input hout key :
 hist_get key(ah_record_state st input hout).`ah_rows=
 if key=input then Some hout else hist_get key st.`ah_rows.
proof. rewrite /ah_record_state /ah_with_rows /=;exact(hist_put_get input hout key st.`ah_rows). qed.
