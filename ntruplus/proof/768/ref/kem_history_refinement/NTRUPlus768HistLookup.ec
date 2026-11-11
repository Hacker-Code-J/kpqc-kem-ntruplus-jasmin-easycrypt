require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768HistModel NTRUPlus768HistKey.
require import NTRUPlus768FOModel NTRUPlus768SimModel NTRUPlus768SimLookup.
require import NTRUPlus768FOEagerG NTRUPlus768FOGAdapters NTRUPlus768ACWC2Oracle.
require import NTRUPlus768ROMOracles NTRUPlus768KEMPayloadSpec NTRUPlus768CCADecapOracle NTRUPlus768CCAStatusAdapter.
require import NTRUPlus768SecGOracles NTRUPlus768CostLookup.

op [opaque] hist_lookup_default : hist_entry =
 ((Array96.init(fun _=>W8.zero),Array32.init(fun _=>W8.zero)),hist_zero_value).
op [opaque] hist_lookup_matches pk suffix g ct (entry:hist_entry) =
 entry.`1.`2=suffix /\ sim_candidate pk g entry.`1 entry.`2=Some ct.
op [opaque] hist_lookup_result pk suffix g (xs:hist_table) ct =
 sim_first (hist_lookup_matches pk suffix g ct)
  (fun entry:hist_entry=>payload_shared_key entry.`2) xs.
op [opaque] hist_lookup_spec pk suffix cstar g (xs:hist_table) ct =
 if cstar=Some ct then None else hist_lookup_result pk suffix g xs ct.

(* None performs no ciphertext comparison. Some performs the explicit
   1152-byte comparator; an option is never compared as an atomic array. *)
module HistCipherOption = {
 proc equal(candidate:W8.t Array1152.t option,ct:W8.t Array1152.t):bool*int = {
  var same:bool;var compared:int;
  same<-false;compared<-0;
  match candidate with
  | None => {}
  | Some value => {(same,compared)<@HistKey.cipher(value,ct);}
  end;
  return(same,compared);
 }
}.

(* The input list is a local snapshot. Entries carry their H value;
   the scan neither consults a finite map nor enumerates its domain.
   Counts denote visits, SimEncrypt calls and byte equality tests. *)
module HistLookup(G:FOGPort) = {
 proc check(entry:hist_entry,pk:W8.t Array1152.t,suffix:W8.t Array32.t,
            ct:W8.t Array1152.t):cca_reply*int*int = {
  var answer:cca_reply;var candidate:W8.t Array1152.t option;
  var matched:bool;var encrypted,compared,n:int;
  answer<-None;encrypted<-0;
  (matched,n)<@HistKey.suffix(entry.`1.`2,suffix);compared<-n;
  if(matched){
   candidate<@SimEncrypt(G).run(pk,entry.`1.`1,entry.`2);encrypted<-1;
   (matched,n)<@HistCipherOption.equal(candidate,ct);compared<-compared+n;
   if(matched){answer<-Some(payload_shared_key entry.`2);}
  }
  return(answer,encrypted,compared);
 }
 proc run(xs:hist_table,pk:W8.t Array1152.t,suffix:W8.t Array32.t,
          cstar:W8.t Array1152.t option,ct:W8.t Array1152.t):cca_reply*int*int*int = {
  var todo:hist_table;var entry:hist_entry;var answer:cca_reply;
  var blocked:bool;var visited,encrypted,compared,n,e,b:int;
  answer<-None;visited<-0;encrypted<-0;
  (blocked,n)<@HistCipherOption.equal(cstar,ct);compared<-n;
  if(!blocked){
   todo<-xs;
   while(todo<>[] /\ answer=None){
    entry<-head hist_lookup_default todo;todo<-behead todo;visited<-visited+1;
    (answer,e,b)<@check(entry,pk,suffix,ct);
    encrypted<-encrypted+e;compared<-compared+b;
   }
  }
  return(answer,visited,encrypted,compared);
 }
}.

lemma hist_lookup_step pk suffix g (xs:hist_table) ct : xs<>[]=>
 hist_lookup_result pk suffix g xs ct=
 if hist_lookup_matches pk suffix g ct (head hist_lookup_default xs)
 then Some(payload_shared_key (head hist_lookup_default xs).`2)
 else hist_lookup_result pk suffix g (behead xs) ct.
proof. by case xs=>[|entry xs] //=;rewrite /hist_lookup_result sim_first_cons. qed.
lemma hist_lookup_stop pk suffix g xs ct (answer:cca_reply) :
 !(xs<>[] /\ answer=None)=>
 (if answer=None then hist_lookup_result pk suffix g xs ct else answer)=answer.
proof. rewrite /hist_lookup_result;exact(sim_first_stop _ _ xs answer). qed.

lemma hist_lookup_result_none pk suffix g xs ct :
 hist_lookup_result pk suffix g xs ct=None <=>
 forall entry,entry \in xs=>!hist_lookup_matches pk suffix g ct entry.
proof. by rewrite /hist_lookup_result sim_first_none List.hasPn. qed.
lemma hist_lookup_result_found pk suffix g xs ct key :
 hist_lookup_result pk suffix g xs ct=Some key=>
 exists entry,entry \in xs /\ hist_lookup_matches pk suffix g ct entry /\
 payload_shared_key entry.`2=key.
proof.
 rewrite /hist_lookup_result;exact(sim_first_some _ _ xs key).
qed.

lemma hist_cipher_option_lossless : islossless HistCipherOption.equal.
proof.
 proc;sp 2;match.
 + auto.
 call hist_cipher_lossless;auto.
qed.
lemma hist_cipher_option_spec candidate0 ct0 :
 hoare[HistCipherOption.equal:candidate=candidate0 /\ ct=ct0 ==>
 res.`1=(candidate0=Some ct0) /\
 res.`2=(if candidate0=None then 0 else 1152)].
proof.
 proc;sp 2;match.
 + auto=> />;smt().
 ecall(hist_cipher_spec value ct0);auto=> />;smt().
qed.
lemma hist_cipher_option_bounds :
 hoare[HistCipherOption.equal:true ==>0<=res.`2<=1152].
proof.
 proc;sp 2;match.
 + auto.
 call hist_cipher_count;auto=> />;smt().
qed.

lemma hist_lookup_check_lossless (G<:FOGPort) :
 islossless G.get=>islossless HistLookup(G).check.
proof.
 move=>hg;proc;seq 4:true;1,4,5:by auto.
 + wp;call hist_suffix_lossless;auto.
 if;last by auto.
 wp;call hist_cipher_option_lossless;wp;call(sim_encrypt_lossless G hg);auto.
qed.
lemma hist_lookup_check_bounds (G<:FOGPort) :
 hoare[HistLookup(G).check:true ==>
 0<=res.`2<=1 /\ 32<=res.`3<=32+1152*res.`2].
proof.
 proc;seq 4:(encrypted=0 /\ compared=32).
 + wp;call hist_suffix_count;auto.
 if;last by auto.
 wp;call hist_cipher_option_bounds;wp;call(_:true ==>true);first by trivial.
 auto=> />;smt().
qed.
lemma hist_lookup_lossless (G<:FOGPort) :
 islossless G.get=>islossless HistLookup(G).run.
proof.
 move=>hg;proc;seq 5:true;1,4,5:by auto.
 + wp;call hist_cipher_option_lossless;auto.
 if;last by auto.
 while true (size todo).
 + move=>z;wp;call(hist_lookup_check_lossless G hg);auto=> />;smt(sim_behead_decreases).
 auto=> />;smt(size_ge0).
qed.
lemma hist_lookup_bounds (G<:FOGPort) xs0 :
 hoare[HistLookup(G).run:xs=xs0 ==>
 0<=res.`3 /\ res.`3<=res.`2 /\ res.`2<=size xs0 /\
 0<=res.`4<=1152+32*res.`2+1152*res.`3].
proof.
 proc;seq 5:(xs=xs0 /\ visited=0 /\ encrypted=0 /\ 0<=compared<=1152).
 + wp;call hist_cipher_option_bounds;auto.
 if;last by auto=> />;smt(size_ge0).
 while(0<=encrypted /\ encrypted<=visited /\ visited+size todo<=size xs0 /\
 0<=compared /\ compared<=1152+32*visited+1152*encrypted).
 + wp;call(hist_lookup_check_bounds G);auto=> />;smt(sim_behead_decreases).
 auto=> />;smt(size_ge0).
qed.

lemma hist_lookup_check_prepared pk0 suffix0 entry0 ct0 g gm0 :
 acwc2_cache_matches g gm0=>
 hoare[HistLookup(FOGActual).check:
 pk=pk0 /\ suffix=suffix0 /\ entry=entry0 /\ ct=ct0 /\ ROG.m=gm0 ==>
 res.`1=(if hist_lookup_matches pk0 suffix0 g ct0 entry0
         then Some(payload_shared_key entry0.`2) else None) /\ ROG.m=gm0].
proof.
 move=>hg;proc;
 seq 4:(pk=pk0 /\ suffix=suffix0 /\ entry=entry0 /\ ct=ct0 /\ ROG.m=gm0 /\
 answer=None /\ matched=(entry0.`1.`2=suffix0)).
 + wp;call(hist_suffix_spec entry0.`1.`2 suffix0);auto.
 if.
 + wp;ecall(hist_cipher_option_spec candidate ct0);wp;
   call(sim_encrypt_prepared pk0 entry0.`1 entry0.`2 g gm0 hg);
   auto=> />;rewrite /hist_lookup_matches;smt().
 auto=> />;rewrite /hist_lookup_matches;smt().
qed.

lemma hist_lookup_prepared pk0 suffix0 cstar0 xs0 ct0 g gm0 :
 acwc2_cache_matches g gm0=>
 hoare[HistLookup(FOGActual).run:
 xs=xs0 /\ pk=pk0 /\ suffix=suffix0 /\ cstar=cstar0 /\ ct=ct0 /\ ROG.m=gm0 ==>
 res.`1=hist_lookup_spec pk0 suffix0 cstar0 g xs0 ct0 /\ ROG.m=gm0].
proof.
 move=>hg;proc;
 seq 5:(xs=xs0 /\ pk=pk0 /\ suffix=suffix0 /\ ct=ct0 /\ ROG.m=gm0 /\
 answer=None /\ blocked=(cstar0=Some ct0)).
 + wp;call(hist_cipher_option_spec cstar0 ct0);auto.
 if.
 + while(pk=pk0 /\ suffix=suffix0 /\ ct=ct0 /\ ROG.m=gm0 /\
 cstar0<>Some ct0 /\
 (if answer=None then hist_lookup_result pk0 suffix0 g todo ct0 else answer)=
 hist_lookup_result pk0 suffix0 g xs0 ct0).
   - sp 3;wp;ecall(hist_lookup_check_prepared pk0 suffix0 entry ct0 g gm0 hg);
     auto=> />;smt(hist_lookup_step).
   auto=> />;rewrite /hist_lookup_spec;smt(hist_lookup_stop).
 auto=> />;rewrite /hist_lookup_spec;smt().
qed.
lemma hist_lookup_correct pk0 suffix0 cstar0 xs0 ct0 g gm0 :
 acwc2_cache_matches g gm0=>
 phoare[HistLookup(FOGActual).run:
 xs=xs0 /\ pk=pk0 /\ suffix=suffix0 /\ cstar=cstar0 /\ ct=ct0 /\ ROG.m=gm0 ==>
 res.`1=hist_lookup_spec pk0 suffix0 cstar0 g xs0 ct0 /\ ROG.m=gm0]=1%r.
proof.
 move=>hg;conseq (hist_lookup_lossless FOGActual rog_get_ll)
 (hist_lookup_prepared pk0 suffix0 cstar0 xs0 ct0 g gm0 hg);smt().
qed.

(* Each tested candidate invokes the actual G kernel exactly once. *)
lemma hist_lookup_check_g_calls n0 :
 hoare[HistLookup(SecGLogged(FOGActual)).check:
 size SecGHistory.queries=n0 ==>
 size SecGHistory.queries=n0+res.`2].
proof.
 proc;seq 4:(size SecGHistory.queries=n0 /\ encrypted=0).
 + wp;call(_:true ==>true);first by trivial.
   auto.
 if;last by auto.
 wp;call(_:true ==>true);first by trivial.
 wp;call(cost_encrypt_g_length n0);auto=> />;smt().
qed.
lemma hist_lookup_g_calls n0 :
 hoare[HistLookup(SecGLogged(FOGActual)).run:
 size SecGHistory.queries=n0 ==>
 size SecGHistory.queries=n0+res.`3].
proof.
 proc;seq 5:(size SecGHistory.queries=n0 /\ encrypted=0).
 + wp;call(_:true ==>true);first by trivial.
   auto.
 if;last by auto.
 while(size SecGHistory.queries=n0+encrypted).
 + wp;ecall(hist_lookup_check_g_calls (n0+encrypted));auto=> />;smt().
 auto.
qed.
