require import AllCore List Distr.
from Jasmin require import JWord.
require import Array768 Array1152.
require import NTRUPlus768SecModel NTRUPlus768MRecModel NTRUPlus768MRecProof NTRUPlus768MRecDecode.
require import NTRUPlus768PKEModel NTRUPlus768PKEAlgebra NTRUPlus768RRecCodec NTRUPlus768EncapGuardSpec.
require import NTRUPlus768SimLookup.

(* Only payloads that actually occurred in the finite adaptive G log are
   decoded. Each candidate uses fixed-size public message recovery. *)
op [opaque] sec_candidate pk ct query : (pke_poly*pke_poly) option =
 let ro=mrec_decode_randomness query in
 if ro=None then None else
 let mo=mrec_spec pk (oget ro) ct in
 if mo=None then None else Some(oget mo,oget ro).
op [opaque] sec_eligible pk ct (excluded:pke_poly option) query =
 sec_candidate pk ct query<>None /\
 (excluded=None \/ (oget(sec_candidate pk ct query)).`2<>oget excluded).
op [opaque] sec_extract_spec pk ct (excluded:pke_poly option) queries =
 sim_first (sec_eligible pk ct excluded) (fun q=>oget(sec_candidate pk ct q)) queries.
op sec_bad2(s:sec_observation) = exists query m r,
 query \in s.`so_queries /\ mrec_decode_randomness query=Some r /\
 mrec_spec s.`so_pk r s.`so_ct=Some m /\ r<>s.`so_r.
op sec_inj_output(s:sec_observation) : sec_collision =
 let out=sec_extract_spec s.`so_pk s.`so_ct (Some s.`so_r) s.`so_queries in
 if out=None then (s.`so_code,s.`so_code,s.`so_r,s.`so_r)
 else (s.`so_code,(oget out).`1,s.`so_r,(oget out).`2).
op sec_zero:pke_poly = Array768.init(fun _=>W16.zero).
op sec_ow_output(s:sec_observation) : pke_poly =
 let out=sec_extract_spec s.`so_pk s.`so_ct None s.`so_queries in
 if out=None then sec_zero else (oget out).`1.
op sec_valid(s:sec_observation) = encap_key_canonical s.`so_pk /\
 pke_domain s.`so_code /\ pke_domain s.`so_r /\
 pke_enc_spec s.`so_pk s.`so_code s.`so_r=Some s.`so_ct.

lemma sec_candidate_some pk ct query m r :
 sec_candidate pk ct query=Some(m,r) <=>
 mrec_decode_randomness query=Some r /\ mrec_spec pk r ct=Some m.
proof.
 rewrite /sec_candidate.
 case(mrec_decode_randomness query)=>[|r0] /=;first by smt().
 case(r0=r)=>he.
 + subst r0;case(mrec_spec pk r ct)=>[|m0] /=;smt().
 case(mrec_spec pk r0 ct)=>[|m0] /=;smt().
qed.
lemma sec_candidate_sound pk ct query m r : sec_candidate pk ct query=Some(m,r)=>
 pke_domain m /\ pke_domain r /\ query=rr_G_input r /\ pke_enc_spec pk m r=Some ct.
proof.
 rewrite sec_candidate_some;move=>[hd hm].
 have [hr hq]:=mrec_decode_randomness_sound query r hd.
 have hs:=mrec_spec_some pk r ct m hm.
 have he:=mrec_acmr pk r ct m hm;smt().
qed.
lemma sec_candidate_pair pk ct query (out:pke_poly*pke_poly) :
 sec_candidate pk ct query=Some out=>
 mrec_decode_randomness query=Some out.`2 /\ mrec_spec pk out.`2 ct=Some out.`1.
proof. case out=>m r;by rewrite sec_candidate_some. qed.
lemma sec_candidate_sound_pair pk ct query (out:pke_poly*pke_poly) :
 sec_candidate pk ct query=Some out=>
 pke_domain out.`1 /\ pke_domain out.`2 /\ query=rr_G_input out.`2 /\ pke_enc_spec pk out.`1 out.`2=Some ct.
proof. case out=>m r;exact(sec_candidate_sound pk ct query m r). qed.
lemma sec_candidate_honest pk m r ct : encap_key_canonical pk=>pke_domain m=>pke_domain r=>
 pke_enc_spec pk m r=Some ct=>sec_candidate pk ct (rr_G_input r)=Some(m,r).
proof.
 move=>hp hm hr he;rewrite sec_candidate_some;split.
 + exact(mrec_decode_randomness_forward r hr).
 exact(mrec_vcmr pk m r ct hp hm hr he).
qed.
lemma sec_extract_some pk ct excluded queries out :
 sec_extract_spec pk ct excluded queries=Some out=>
 exists query,query \in queries /\ sec_candidate pk ct query=Some out /\
 (excluded=None \/ out.`2<>oget excluded).
proof.
 rewrite /sec_extract_spec;move=>/sim_first_some [q [hq [he hv]]].
 exists q;move:he;rewrite /sec_eligible;smt(some_oget).
qed.
lemma sec_extract_none pk ct excluded queries :
 sec_extract_spec pk ct excluded queries=None <=>
 forall q,q \in queries=>!sec_eligible pk ct excluded q.
proof. by rewrite /sec_extract_spec sim_first_none hasPn. qed.
lemma sec_bad2_scan s : sec_bad2 s <=>
 sec_extract_spec s.`so_pk s.`so_ct (Some s.`so_r) s.`so_queries<>None.
proof.
 split.
 + rewrite /sec_bad2.
   move=>[q m r [hq [hd [hm hr]]]].
   have hc:sec_candidate s.`so_pk s.`so_ct q=Some(m,r) by rewrite sec_candidate_some hd hm.
   apply/negP=>hz;move:hz;rewrite sec_extract_none=>hn;have h:=hn q hq.
   by move:h;rewrite /sec_eligible hc /=;smt().
 move=>hn;have hs:=some_oget (sec_extract_spec s.`so_pk s.`so_ct (Some s.`so_r) s.`so_queries) hn.
 have [q [hq [hc he]]]:=sec_extract_some _ _ _ _ _ hs.
 have [hd hm]:=sec_candidate_pair _ _ _ _ hc.
 rewrite /sec_bad2;exists q (oget(sec_extract_spec s.`so_pk s.`so_ct (Some s.`so_r) s.`so_queries)).`1
 (oget(sec_extract_spec s.`so_pk s.`so_ct (Some s.`so_r) s.`so_queries)).`2.
 split;first exact hq.
 split;first exact hd.
 split;first exact hm.
 by move:he;rewrite /=.
qed.
lemma sec_bad2_inj s : sec_valid s=>sec_bad2 s=>sec_inj_win s.`so_pk (sec_inj_output s).
proof.
 move=>hv hb.
 have hp:encap_key_canonical s.`so_pk by clear hb;move:hv;rewrite /sec_valid;smt().
 have hm:pke_domain s.`so_code by clear hb;move:hv;rewrite /sec_valid;smt().
 have hr:pke_domain s.`so_r by clear hb;move:hv;rewrite /sec_valid;smt().
 have he:pke_enc_spec s.`so_pk s.`so_code s.`so_r=Some s.`so_ct
 by clear hb;move:hv;rewrite /sec_valid;smt().
 have hn:sec_extract_spec s.`so_pk s.`so_ct (Some s.`so_r) s.`so_queries<>None by rewrite -sec_bad2_scan;exact hb.
 have hs:=some_oget (sec_extract_spec s.`so_pk s.`so_ct (Some s.`so_r) s.`so_queries) hn.
 have [query [hq [hc hx]]]:=sec_extract_some _ _ _ _ _ hs.
 have [hm' [hr' [hq' he']]]:=sec_candidate_sound_pair _ _ _ _ hc.
 rewrite /sec_inj_output hs /=.
 apply(sec_inj_witness _ _ _ _ _ _ hm hm' hr hr' _ he he').
 by move:hx;rewrite /=
 -(eq_sym s.`so_r (oget(sec_extract_spec s.`so_pk s.`so_ct (Some s.`so_r) s.`so_queries)).`2).
qed.
lemma sec_hit_good_ow s : sec_valid s=>sec_hit s=>!sec_bad2 s=>sec_ow_output s=s.`so_code.
proof.
 move=>hv hhit hbad.
 have hp:encap_key_canonical s.`so_pk by clear hhit hbad;move:hv;rewrite /sec_valid;smt().
 have hm:pke_domain s.`so_code by clear hhit hbad;move:hv;rewrite /sec_valid;smt().
 have hr:pke_domain s.`so_r by clear hhit hbad;move:hv;rewrite /sec_valid;smt().
 have he:pke_enc_spec s.`so_pk s.`so_code s.`so_r=Some s.`so_ct
 by clear hhit hbad;move:hv;rewrite /sec_valid;smt().
 move:hhit;rewrite /sec_hit=>hhit.
 have honest:=sec_candidate_honest _ _ _ _ hp hm hr he.
 have hn:sec_extract_spec s.`so_pk s.`so_ct None s.`so_queries<>None.
 + apply/negP=>hz;move:hz;rewrite sec_extract_none=>hall;have h:=hall (rr_G_input s.`so_r) hhit.
   by move:h;rewrite /sec_eligible honest /=.
 have hs:=some_oget (sec_extract_spec s.`so_pk s.`so_ct None s.`so_queries) hn.
 have [query [hq [hc hx]]]:=sec_extract_some _ _ _ _ _ hs.
 have [hd hm']:=sec_candidate_pair _ _ _ _ hc.
 have same:(oget(sec_extract_spec s.`so_pk s.`so_ct None s.`so_queries)).`2=s.`so_r.
 + case((oget(sec_extract_spec s.`so_pk s.`so_ct None s.`so_queries)).`2=s.`so_r)=>neq;first by trivial.
   have bad:sec_bad2 s.
   - rewrite /sec_bad2;exists query
     (oget(sec_extract_spec s.`so_pk s.`so_ct None s.`so_queries)).`1
     (oget(sec_extract_spec s.`so_pk s.`so_ct None s.`so_queries)).`2.
     split;first exact hq. split;first exact hd. split;first exact hm'. by trivial.
   by move:hbad;rewrite bad.
 have recovered:=mrec_vcmr _ _ _ _ hp hm hr he.
 move:hm';rewrite same recovered=>/someI heq.
 by rewrite /sec_ow_output hs /= -heq.
qed.
