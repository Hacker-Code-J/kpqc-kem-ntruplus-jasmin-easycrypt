require import AllCore List FMap FSet.
from Jasmin require import JWord.
require import Array32 Array96 Array224.
require import NTRUPlus768FOModel.

type hist_entry = fo_h_input * W8.t Array224.t.
type hist_table = hist_entry list.
op [opaque] hist_zero_value : W8.t Array224.t = Array224.init(fun _=>W8.zero).
op [opaque] hist_keys (xs:hist_table) = List.map fst xs.
op [opaque] hist_unique (xs:hist_table) = uniq(hist_keys xs).
op [opaque] hist_rep (xs:hist_table) (m:(fo_h_input,W8.t Array224.t)fmap) =
 hist_unique xs /\ ofassoc xs=m.
op [opaque] hist_get (x:fo_h_input) (xs:hist_table) = List.assoc xs x.
op [opaque] hist_keep (x:fo_h_input) (xs:hist_table) =
 List.filter(fun e:hist_entry=>e.`1<>x)xs.
op [opaque] hist_put (x:fo_h_input) (y:W8.t Array224.t) (xs:hist_table) =
 (x,y)::hist_keep x xs.

lemma hist_get_nil x : hist_get x []=None.
proof. by rewrite /hist_get assoc_nil. qed.
lemma hist_get_cons x (e:hist_entry) xs :
 hist_get x(e::xs)=if e.`1=x then Some e.`2 else hist_get x xs.
proof. by case e=>k v;rewrite /hist_get assoc_cons [x=k]eq_sym. qed.
lemma hist_get_step x d xs : xs<>[]=>
 hist_get x xs=if (head d xs).`1=x then Some(head d xs).`2 else hist_get x(behead xs).
proof. by case xs=>[|e xs] //=;rewrite hist_get_cons. qed.
lemma hist_get_stop x xs (answer:W8.t Array224.t option) :
 !(xs<>[] /\ answer=None)=>
 (if answer=None then hist_get x xs else answer)=answer.
proof.
 move=>hs;case(answer=None)=>ha;last done.
 have hx:xs=[] by smt().
 by rewrite hx hist_get_nil ha.
qed.
lemma hist_keep_nil x : hist_keep x []=[].
proof. by rewrite /hist_keep. qed.
lemma hist_keep_cons x e xs :
 hist_keep x(e::xs)=if e.`1<>x then e::hist_keep x xs else hist_keep x xs.
proof. by rewrite /hist_keep /=. qed.
lemma hist_keep_step x d xs : xs<>[]=>
 hist_keep x xs=if (head d xs).`1<>x then head d xs::hist_keep x(behead xs) else hist_keep x(behead xs).
proof. by case xs=>[|e xs] //=;rewrite hist_keep_cons. qed.
lemma hist_keep_size x xs : 0<=size(hist_keep x xs)<=size xs.
proof. rewrite /hist_keep size_filter;smt(count_ge0 count_size). qed.
lemma hist_put_size x y xs : size(hist_put x y xs)=1+size(hist_keep x xs).
proof. by rewrite /hist_put /=. qed.
lemma hist_put_size_bound x y xs : size(hist_put x y xs)<=size xs+1.
proof. rewrite hist_put_size;have h:=hist_keep_size x xs;smt(). qed.

lemma hist_keep_keys x xs :
 hist_keys(hist_keep x xs)=List.filter(fun k=>k<>x)(hist_keys xs).
proof.
 rewrite /hist_keys /hist_keep.
 elim xs=>[|[k v] xs ih] //=.
 by case(k<>x)=>h;rewrite /= ih.
qed.
lemma hist_keys_cons e xs : hist_keys(e::xs)=e.`1::hist_keys xs.
proof. by rewrite /hist_keys /=. qed.
lemma hist_put_unique x y xs : hist_unique xs=>hist_unique(hist_put x y xs).
proof.
 rewrite /hist_unique /hist_put hist_keys_cons /= hist_keep_keys=>hu.
 split;first by rewrite mem_filter;smt().
 exact(filter_uniq _ _ hu).
qed.
lemma hist_get_ofassoc x xs : hist_get x xs=(ofassoc xs).[x].
proof. by rewrite ofassoc_get /hist_get. qed.
lemma hist_keep_get x k xs : hist_get k(hist_keep x xs)=if k<>x then hist_get k xs else None.
proof.
 rewrite /hist_get /hist_keep.
 have h:=assoc_filter(fun k=>k<>x) xs k.
 by move:h;rewrite /(\o) /fst.
qed.
lemma hist_put_get x y k xs :
 hist_get k(hist_put x y xs)=if k=x then Some y else hist_get k xs.
proof. rewrite /hist_put hist_get_cons hist_keep_get /=;by case(k=x);smt(). qed.
lemma hist_put_ofassoc x y xs : ofassoc(hist_put x y xs)=(ofassoc xs).[x<-y].
proof.
 apply/fmap_eqP=>k;rewrite -hist_get_ofassoc get_setE -hist_get_ofassoc.
 exact(hist_put_get x y k xs).
qed.
lemma hist_rep_get x xs m : hist_rep xs m=>hist_get x xs=m.[x].
proof. rewrite /hist_rep;move=>[hu hm];rewrite -hm;exact(hist_get_ofassoc x xs). qed.
lemma hist_rep_entry x y xs m : hist_rep xs m=>
 ((x,y) \in xs <=> m.[x]=Some y).
proof.
 rewrite /hist_rep /hist_unique /hist_keys;move=>[hu hm];rewrite -hm.
 rewrite ofassoc_get;exact(mem_assoc_uniq xs x y hu).
qed.
lemma hist_rep_put x y xs m : hist_rep xs m=>hist_rep(hist_put x y xs)m.[x<-y].
proof.
 rewrite /hist_rep;move=>[hu hm];rewrite -hm;split.
 exact(hist_put_unique x y xs hu).
 exact(hist_put_ofassoc x y xs).
qed.

lemma hist_behead_exact ['a] (xs:'a list) : xs<>[]=>
 size(behead xs)=size xs-1 /\ 0<=size(behead xs)<size xs.
proof. case xs=>[|e xs] //=;smt(size_ge0). qed.
lemma hist_keep_reverse_step x d todo kept : todo<>[]=>
 rev kept++hist_keep x todo=
 rev(if (head d todo).`1=x then kept else head d todo::kept)++hist_keep x(behead todo).
proof.
 move=>hn;rewrite(hist_keep_step x d todo hn).
 case((head d todo).`1=x)=>he /=;first done.
 by rewrite rev_cons -cats1 -catA /=.
qed.
lemma hist_reverse_step (d:hist_entry) todo output : todo<>[]=>
 rev todo++output=rev(behead todo)++head d todo::output.
proof. case todo=>[|e todo] //=;by rewrite rev_cons -cats1 -catA /=. qed.
lemma hist_rep_size xs m : hist_rep xs m=>size xs=fsize m.
proof.
 rewrite /hist_rep /hist_unique /hist_keys;move=>[hu hm];rewrite -hm.
 by rewrite /fsize fdom_ofassoc uniq_card_oflist 1:hu size_map.
qed.
lemma hist_rep_empty : hist_rep [] empty.
proof.
 rewrite /hist_rep /hist_unique /hist_keys /=.
 apply/fmap_eqP=>x;by rewrite ofassoc_get assoc_nil emptyE.
qed.
