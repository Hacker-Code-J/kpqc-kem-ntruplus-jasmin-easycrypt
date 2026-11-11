"""Reviewed API seams; structural checks are not EasyCrypt proofs."""
BASE = 'ntruplus/proof/768/ref/kem_indcca_game/'
STATUS = BASE + 'NTRUPlus768CCAStatusAdapter.ec'
DECAP = BASE + 'NTRUPlus768CCADecapOracle.ec'
PORTS = BASE + 'NTRUPlus768CCAOraclePorts.ec'
CODEC = BASE + 'NTRUPlus768CCAQueryCodec.ec'
PROBABILITY = BASE + 'NTRUPlus768CCAProbability.ec'

RULES = (
 (STATUS, 'status is the only option discriminator', r'op cca_status_result (ss:W8.t Array32.t) (status:W32.t) : cca_reply = if status=W32.zero then Some ss else None.'),
 (STATUS, 'actual Decaps with shared G/H and workspace', r'result <@ CompleteDecaps(SHAKEGROM,SHAKEHROM).run(ct,sk,witness); return cca_status_result result.`1 result.`2;'),
 (DECAP, 'adversary decap capability only', r'module type CCADecapPort = { proc decap(ct:W8.t Array1152.t) : cca_reply }.'),
 (DECAP, 'optional challenge initialized absent', r'proc reset() : unit = { sk <- witness; cstar <- None; count <- 0; }'),
 (DECAP, 'installed secret and exact challenge', r'proc init(sk0:W8.t Array2336.t,cstar0:W8.t Array1152.t) : unit = { sk <- sk0; cstar <- Some cstar0; count <- 0; }'),
 (DECAP, 'every request counted before exact-byte challenge exclusion', r'proc decap(ct:W8.t Array1152.t) : cca_reply = { var answer:cca_reply; count <- count+1; if (cstar=Some ct) { answer <- None; } else { answer <@ CCAStatusAdapter.run(ct,sk); } return answer; }'),
 (PORTS, 'query-only typed capability', r'module type CCAOraclePort = { proc e(input:W8.t Array32.t) : W8.t Array192.t proc f(input:W8.t Array1152.t) : W8.t Array32.t proc g(input:W8.t Array1152.t) : W8.t Array192.t proc h(input:W8.t Array96.t*W8.t Array32.t) : W8.t Array224.t }.'),
 (CODEC, 'exact untagged E input length', r'if size s=32 then Some(E(Array32.of_list W8.zero s))'),
 (CODEC, 'F raw tag and length', r'else if size s=1153 /\ nth W8.zero s 0=W8.zero then Some(F(peel1153(Array1153.of_list W8.zero s)))'),
 (CODEC, 'G raw tag and length', r'else if size s=1153 /\ nth W8.zero s 0=W8.one then Some(G(peel1153(Array1153.of_list W8.zero s)))'),
 (CODEC, 'H raw tag and length', r'else if size s=129 /\ nth W8.zero s 0=W8.of_int 2 then Some(H(peel_h(Array129.of_list W8.zero s))) else None.'),
 (PROBABILITY, 'returned abort differs from divergence', r'outcome <@ B.run(qf,qg); fallback <$ dbool; return(outcome,fallback);'),
 (PROBABILITY, 'fallback only for returned None', r'op cca_complete_value (outcome:bool option) (fallback:bool) = if outcome=None then fallback else oget outcome.'),
 (PROBABILITY, 'fallback preserves partial return mass', r'lemma cca_fallback_return (B<:PartialCCABody) &m qf0 qg0 : Pr[CompleteFallback(B).run(qf0,qg0) @ &m:true]= Pr[B.run(qf0,qg0) @ &m:true].'),
 (PROBABILITY, 'losslessness required to center at one half', r'lemma cca_fallback_centered_lossless (B<:PartialCCABody) &m qf0 qg0 : islossless B.run =>'),
)
MUTATIONS = (
 ('zero-shared-key-treated-as-rejection',STATUS,'if status=W32.zero then Some ss else None','if ss=encap_zero_ss then None else Some ss'),
 ('actual-Decaps-substituted',STATUS,'CompleteDecaps(SHAKEGROM,SHAKEHROM).run(ct,sk,witness)','ReferenceDecaps.run(ct,sk,witness)'),
 ('status-and-key-tuple-projection-confused',STATUS,'cca_status_result result.`1 result.`2','cca_status_result result.`1 W32.zero'),
 ('decap-port-exposes-reset',DECAP,'module type CCADecapPort = {','module type CCADecapPort = { proc reset() : unit'),
 ('absent-challenge-confused-with-zero-bytes',DECAP,'cstar <- None;','cstar <- Some witness;'),
 ('challenge-installed-as-absent',DECAP,'cstar <- Some cstar0;','cstar <- None;'),
 ('blocked-query-not-counted',DECAP,'count <- count+1;','count <- count;'),
 ('challenge-comparison-normalizes-ciphertext',DECAP,'if (cstar=Some ct)','if (cstar=Some(normalize_ct ct))'),
 ('blocked-query-mutates-hash-table',DECAP,'answer <- None;','ROG.init(); answer <- None;'),
 ('typed-port-exposes-cache-reset',PORTS,'module type CCAOraclePort = {','module type CCAOraclePort = { proc init() : unit'),
 ('typed-query-resets-cache',PORTS,'var r; r <@ ROE.get(input);','var r; ROE.init(); r <@ ROE.get(input);'),
 ('typed-G-uses-F-cache',PORTS,'r <@ ROG.get(input);','r <@ ROF.get(input);'),
 ('E-raw-wrong-length',CODEC,'if size s=32','if size s=33'),
 ('F-raw-tag-omitted',CODEC,'size s=1153 /\\ nth W8.zero s 0=W8.zero','size s=1153'),
 ('G-raw-length-omitted',CODEC,'size s=1153 /\\ nth W8.zero s 0=W8.one','nth W8.zero s 0=W8.one'),
 ('H-raw-tag-confused',CODEC,'nth W8.zero s 0=W8.of_int 2','nth W8.zero s 0=W8.one'),
 ('fallback-sampled-before-possibly-diverging-body',PROBABILITY,'outcome <@ B.run(qf,qg); fallback <$ dbool;','fallback <$ dbool; outcome <@ B.run(qf,qg);'),
 ('returned-false-replaced-by-fallback',PROBABILITY,'if outcome=None then fallback else oget outcome','if outcome=Some true then true else fallback'),
 ('fallback-assumes-return-mass-one',PROBABILITY,'Pr[CompleteFallback(B).run(qf0,qg0) @ &m:true]= Pr[B.run(qf0,qg0) @ &m:true].','Pr[CompleteFallback(B).run(qf0,qg0) @ &m:true]=1%r.'),
 ('half-centering-omits-losslessness',PROBABILITY,'lemma cca_fallback_centered_lossless (B<:PartialCCABody) &m qf0 qg0 : islossless B.run =>','lemma cca_fallback_centered_lossless (B<:PartialCCABody) &m qf0 qg0 :'),
)

from raw_contract import RULES as RAW_RULES, MUTATIONS as RAW_MUTATIONS
from game_contract import RULES as GAME_RULES, MUTATIONS as GAME_MUTATIONS, check_extra
RULES += GAME_RULES
MUTATIONS += GAME_MUTATIONS
RULES += RAW_RULES
MUTATIONS += RAW_MUTATIONS

def check_model(read, ordered, require):
 from check_kem_indcca_game import compact
 check_extra(read,require)
 for relative, label, expected in RULES:
  require(compact(expected) in read(relative),label)
 ports=read(PORTS)
 for letter, domain, codomain in (('e','W8.t Array32.t','W8.t Array192.t'),('f','W8.t Array1152.t','W8.t Array32.t'),('g','W8.t Array1152.t','W8.t Array192.t'),('h','W8.t Array96.t * W8.t Array32.t','W8.t Array224.t')):
  body='proc '+letter+'(input:'+domain+'):'+codomain+'={var r; r<@RO'+letter.upper()+'.get(input);return r;}'
  require(compact(body) in ports,'typed '+letter+' uses only shared backing table')
