require import AllCore List Distr FMap.
from Jasmin require import JWord.
require import Array32 Array96 Array192 Array224 Array1152.
require import NTRUPlus768AHState NTRUPlus768HistModel NTRUPlus768HistLookup.
require import NTRUPlus768FOModel NTRUPlus768FOEagerG NTRUPlus768SimModel.
require import NTRUPlus768ROMDomains NTRUPlus768ROMOracles.
require import NTRUPlus768CCAOraclePorts NTRUPlus768CCAGame NTRUPlus768CCADecapOracle NTRUPlus768CCAStatusAdapter.
require import NTRUPlus768RawXOF NTRUPlus768RawXOFSampling NTRUPlus768CCAQueryCodec.

(* Every encryption inside the list scan uses the supplied G port. In
   particular, a supplied logged G backend observes all internal calls. *)
module AHPublicG(O:CCAExtendedOraclePort) : FOGPort = {
 proc get(input:W8.t Array1152.t):W8.t Array192.t = {
  var result;result<@O.g(input);return result;
 }
}.
module AHRecordH(S:AHStore,O:CCAExtendedOraclePort) : SimHPort = {
 proc get(input:fo_h_input):W8.t Array224.t = {
  var hout;hout<@O.h(input);S.record(input,hout);return hout;
 }
}.
module AHOracles(S:AHStore,O:CCAExtendedOraclePort) : CCAExtendedOraclePort = {
 proc e=O.e
 proc f=O.f
 proc g=O.g
 proc h=AHRecordH(S,O).get
 proc raw(input:W8.t list,outlen:int):W8.t list option = {
  var result:W8.t list option;var hout:W8.t Array224.t;
  if(0<=outlen<=raw_xof_max_output){
   match decode_typed input with
   | None => {result<@O.raw(input,outlen);}
   | Some query => {
    match query with
    | E seed => {result<@O.raw(input,outlen);}
    | F pk => {result<@O.raw(input,outlen);}
    | G serialized => {result<@O.raw(input,outlen);}
    | H payload => {
     hout<@AHRecordH(S,O).get(payload);
     result<-Some(raw_xof_output outlen hout);
    }
    end;
   }
   end;
  }else{result<@O.raw(input,outlen);}
  return result;
 }
}.
module AHDecap(S:AHStore,O:CCAExtendedOraclePort) : CCADecapPort = {
 proc decap(ct:W8.t Array1152.t):cca_reply = {
  var st:ah_state;var result:cca_reply*int*int*int;
  st<@S.snapshot();
  result<@HistLookup(AHPublicG(O)).run(st.`ah_rows,st.`ah_pk,st.`ah_suffix,st.`ah_cstar,ct);
  return result.`1;
 }
}.
module AHWrapper(S:AHStore,A:CCAExtendedAdversary,O:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc guess(pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t):bool = {
  var suffix:W8.t Array32.t;var answer:bool;
  suffix<@O.f(pk);S.init(pk,suffix,Some ct);
  answer<@A(AHOracles(S,O),AHDecap(S,O)).guess(pk,ct,key);
  return answer;
 }
}.

lemma ah_public_g_ll (O<:CCAExtendedOraclePort) : islossless O.g=>islossless AHPublicG(O).get.
proof. move=>hl;proc;call hl;auto. qed.
lemma ah_record_h_ll (S<:AHStore)(O<:CCAExtendedOraclePort) :
 islossless O.h=>islossless S.record=>islossless AHRecordH(S,O).get.
proof. move=>ho hs;proc;call hs;call ho;auto. qed.
lemma ah_oracles_raw_ll (S<:AHStore)(O<:CCAExtendedOraclePort) :
 islossless O.h=>islossless O.raw=>islossless S.record=>islossless AHOracles(S,O).raw.
proof.
 move=>hh hr hs;proc;if;last by call hr;auto.
 match;first by call hr;auto.
 match.
 + call hr;auto.
 + call hr;auto.
 + call hr;auto.
 wp;call(ah_record_h_ll S O hh hs);auto.
qed.
lemma ah_decap_ll (S<:AHStore)(O<:CCAExtendedOraclePort) :
 islossless S.snapshot=>islossless O.g=>islossless AHDecap(S,O).decap.
proof.
 move=>hs hg;proc;wp;call(hist_lookup_lossless (AHPublicG(O)) (ah_public_g_ll O hg));call hs;auto.
qed.

lemma ah_public_g_projection (O<:CCAExtendedOraclePort) :
 equiv[AHPublicG(O).get ~ O.g: ={arg,glob O} ==> ={res,glob O}].
proof. proc*;inline{1} AHPublicG(O).get;wp;call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto. auto. qed.

lemma ah_record_h_view (S<:AHStore)(O<:CCAExtendedOraclePort {-S})
 (view:(glob S)->ah_state) st0 input0 :
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y]) =>
 hoare[AHRecordH(S,O).get:view(glob S)=st0 /\ input=input0 ==>
 view(glob S)=ah_record_state st0 input0 res].
proof.
 move=>hs;proc;ecall(hs st0 input0 hout).
 call(_:true ==>true);first by trivial.
 auto.
qed.

lemma ah_raw_invalid_projection (S<:AHStore)(O<:CCAExtendedOraclePort) input0 n0 :
 !(0<=n0<=raw_xof_max_output)=>
 equiv[AHOracles(S,O).raw ~ O.raw:
 ={arg,glob O} /\ input{1}=input0 /\ outlen{1}=n0 ==> ={res,glob O}].
proof.
 move=>hn;proc*;inline{1} AHOracles(S,O).raw;sp 2 0;rcondf{1} 1;first by auto.
 wp;call(_: ={arg,glob O} ==> ={res,glob O});first by proc true;auto.
 auto.
qed.

lemma ah_raw_h_view (S<:AHStore)(O<:CCAExtendedOraclePort {-S})
 (view:(glob S)->ah_state) st0 input0 n0 :
 0<=n0<=raw_xof_max_output=>
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y]) =>
 hoare[AHOracles(S,O).raw:
 view(glob S)=st0 /\ input=raw_query(H input0) /\ outlen=n0 ==>
 exists hout,view(glob S)=ah_record_state st0 input0 hout /\
 res=Some(raw_xof_output n0 hout)].
proof.
 move=>hn hs;have he:=decode_typed_encode(H input0).
 proc;rcondt 1;first by auto.
 match.
 + conseq(_:false ==>_)=> //;clear hs hn;smt().
 match.
 + conseq(_:false ==>_)=> //;clear hs hn;smt().
 + conseq(_:false ==>_)=> //;clear hs hn;smt().
 + conseq(_:false ==>_)=> //;clear hs hn;smt().
 wp;call(ah_record_h_view S O view st0 input0 hs);auto=> />.
 clear hs hn;smt().
qed.

(* A zero-byte request still calls H and records the complete response. *)
lemma ah_raw_zero_h_view (S<:AHStore)(O<:CCAExtendedOraclePort {-S})
 (view:(glob S)->ah_state) st0 input0 :
 (forall st x y,hoare[S.record:view(glob S)=st /\ input=x /\ hout=y ==>
 view(glob S)=ah_record_state st x y]) =>
 hoare[AHOracles(S,O).raw:
 view(glob S)=st0 /\ input=raw_query(H input0) /\ outlen=0 ==>
 (exists hout,view(glob S)=ah_record_state st0 input0 hout) /\ res=Some []].
proof.
 move=>hs;have h0:0<=0<=raw_xof_max_output by rewrite /raw_xof_max_output.
 conseq(ah_raw_h_view S O view st0 input0 0 h0 hs)=> //.
 move=> &hr _ result gs [hout [hv ->]];split;first by exists hout.
 by rewrite /raw_xof_output take0.
qed.
