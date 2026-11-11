"""Raw-query coherence and output cap; no security conclusion from scanning."""
BASE='ntruplus/proof/768/ref/kem_indcca_game/'
SAMPLING=BASE+'NTRUPlus768RawXOFSampling.ec'
STREAMS=BASE+'NTRUPlus768RawXOFStreams.ec'
RAW=BASE+'NTRUPlus768RawXOF.ec'
RULES=(
 (SAMPLING,'reviewed finite XOF output bound',r'op raw_xof_max_output = 224.'),
 (SAMPLING,'output is a prefix, length is not an input key',r'op raw_xof_output (n:int) (s:W8.t Array224.t) = take n (Array224.to_list s).'),
 (SAMPLING,'typed 192-byte prefix is preserved',r'op raw_join192 (p:W8.t Array192.t*W8.t Array32.t) : W8.t Array224.t = Array224.init(fun i=>if i<192 then p.`1.[i] else p.`2.[i-192]).'),
 (STREAMS,'untyped queries cache by full byte-list only',r'var other : (W8.t list,W8.t Array224.t) fmap'),
 (STREAMS,'untyped miss-only independent sampling',r'proc untyped(input:W8.t list) : W8.t Array224.t = { var stream; if(input \notin other){stream <$ uniform224; other.[input]<-stream;} return oget other.[input]; }'),
 (STREAMS,'H already has full 224-byte stream',r'proc h(input:W8.t Array96.t*W8.t Array32.t) : W8.t Array224.t = { var stream; stream <@ SharedCCAOracles.h(input); return stream; }'),
 (RAW,'query-only raw capability',r'module type RawXOFPort = { proc get(input:W8.t list,outlen:int) : W8.t list option }.'),
 (RAW,'invalid output rejected before dispatch',r'proc get(input:W8.t list,outlen:int) : W8.t list option = { var result,stream; result <- None; if(0<=outlen<=raw_xof_max_output){ stream <@ full(input); result <- Some(raw_xof_output outlen stream); } return result; }'),
 (RAW,'decode full raw domain before typed dispatch',r'proc full(input:W8.t list) : W8.t Array224.t = { var stream; match decode_typed input with | None => { stream <@ RawXOFStreams.untyped(input); } | Some query => { match query with | E seed => { stream <@ RawXOFStreams.e(seed); } | F pk => { stream <@ RawXOFStreams.f(pk); } | G serialized => { stream <@ RawXOFStreams.g(serialized); } | H payload => { stream <@ RawXOFStreams.h(payload); } end; } end; return stream; }'),
 (RAW,'extended queries share original typed backing',r'module SharedCCAExtendedOracles : CCAExtendedOraclePort = { proc e=SharedCCAOracles.e proc f=SharedCCAOracles.f proc g=SharedCCAOracles.g proc h=SharedCCAOracles.h proc raw=RawXOF.get }.'),
)
for letter,domain,cache,law,join in (
 ('e','Array32','es','uniform32','raw_join192'),
 ('f','Array1152','fs','uniform192','hash_join'),
 ('g','Array1152','gs','uniform32','raw_join192')):
 RULES+=((STREAMS,'raw '+letter+' preserves shared prefix and caches suffix on miss',
  'proc '+letter+'(input:W8.t '+domain+'.t) : W8.t Array224.t = { var prefix,suffix; prefix <@ SharedCCAOracles.'+letter+'(input); if(input \\notin '+cache+'){suffix <$ '+law+'; '+cache+'.[input]<-suffix;} return '+join+'(prefix,oget '+cache+'.[input]); }'),)
MUTATIONS=(
 ('raw-output-cap-off-by-one',SAMPLING,'op raw_xof_max_output = 224.','op raw_xof_max_output = 225.'),
 ('raw-output-takes-tail-not-prefix',SAMPLING,'take n (Array224.to_list s)','drop n (Array224.to_list s)'),
 ('raw-extension-overwrites-typed-prefix',SAMPLING,'if i<192 then p.`1.[i]','if i<192 then W8.zero'),
 ('raw-untyped-resamples-cache-hit',STREAMS,'if(input \\notin other)','if(true)'),
 ('raw-E-prefix-uses-independent-cache',STREAMS,'prefix <@ SharedCCAOracles.e(input);','prefix <$ uniform192;'),
 ('raw-F-suffix-incorrect-size',STREAMS,'suffix <$ uniform192; fs.[input]','suffix <$ uniform32; fs.[input]'),
 ('raw-G-prefix-uses-F-table',STREAMS,'prefix <@ SharedCCAOracles.g(input);','prefix <@ SharedCCAOracles.f(input);'),
 ('raw-H-ignores-shared-table',STREAMS,'stream <@ SharedCCAOracles.h(input);','stream <$ uniform224;'),
 ('raw-capability-exposes-init',RAW,'module type RawXOFPort = {','module type RawXOFPort = { proc init() : unit'),
 ('raw-negative-length-accepted',RAW,'if(0<=outlen<=raw_xof_max_output)','if(outlen<=raw_xof_max_output)'),
 ('raw-zero-length-rejected',RAW,'if(0<=outlen<=raw_xof_max_output)','if(0<outlen<=raw_xof_max_output)'),
 ('raw-invalid-length-query-has-side-effects',RAW,'result <- None; if(0<=outlen','result <- None; ROE.init(); if(0<=outlen'),
 ('malformed-raw-query-unconditionally-peeled',RAW,'RawXOFStreams.untyped(input)','RawXOFStreams.e(peel32 input)'),
 ('raw-G-dispatch-uses-F-domain',RAW,'RawXOFStreams.g(serialized)','RawXOFStreams.f(serialized)'),
 ('extended-raw-query-uses-detached-table',RAW,'proc raw=RawXOF.get','proc raw=DetachedXOF.get'),
)

RULES += (
 (RAW,'optional budget clamps only configured resource limits',r'proc configure(q:int,maxinput:int) = { attempts<-0; forwarded<-0; limit<-max 0 q; max_input<-max 0 maxinput; }'),
 (RAW,'attempts count all requests and forwarding only valid admitted calls',r'proc get(input:W8.t list,outlen:int) : W8.t list option = { var result,allowed; result<-None; allowed<-attempts<limit /\ size input<=max_input /\ 0<=outlen<=raw_xof_max_output; attempts<-attempts+1; if(allowed){ forwarded<-forwarded+1; result<@RawXOF.get(input,outlen); } return result; }'),
)
MUTATIONS += (
 ('budget-counter-resets-on-each-query',RAW,'attempts<-attempts+1;','attempts<-1;'),
 ('budget-off-by-one-allows-extra-query',RAW,'allowed<-attempts<limit','allowed<-attempts<=limit'),
 ('budget-counts-distinct-keys-instead-of-requests',RAW,'attempts<-attempts+1;','if(input \\notin RawXOFStreams.other){attempts<-attempts+1;}'),
 ('budget-forwards-invalid-output-length',RAW,r'size input<=max_input /\ 0<=outlen<=raw_xof_max_output;','size input<=max_input;'),
 ('budget-erases-core-table-on-rejection',RAW,'result<-None; allowed<-attempts','result<-None; ROE.init(); allowed<-attempts'),
)

LAWS=BASE+'NTRUPlus768RawXOFLaws.ec'
for letter,cache in (('e','es'),('f','fs'),('g','gs')):
 RULES+=((LAWS,'fresh '+letter+' law requires absent prefix and suffix',
  'lemma raw_stream_'+letter+'_uniform &m x0 (event:W8.t Array224.t->bool) : x0 \\notin RO'+letter.upper()+'.m{m} => x0 \\notin RawXOFStreams.'+cache+'{m} => Pr[RawXOFStreams.'+letter+'(x0) @ &m : event res]=mu uniform224 event.'),)
MUTATIONS+=(
 ('fresh-raw-law-ignores-existing-typed-prefix',LAWS,r'x0 \notin ROE.m{m} => x0 \notin RawXOFStreams.es{m} =>',r'x0 \notin RawXOFStreams.es{m} =>'),
 ('fresh-raw-law-ignores-existing-extension-suffix',LAWS,r'x0 \notin ROF.m{m} => x0 \notin RawXOFStreams.fs{m} =>',r'x0 \notin ROF.m{m} =>'),
)
