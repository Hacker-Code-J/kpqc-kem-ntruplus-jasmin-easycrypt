"""Effective E dispatch, exact counting, cap responses, and hidden trace state."""
BASE='ntruplus/proof/768/ref/kem_e_erasure/'
MODEL=BASE+'NTRUPlus768ErasureModel.ec'
BUDGET=BASE+'NTRUPlus768ErasureBudget.ec'
RULES=(
 (MODEL,'effective raw E includes zero output and exactly the full 32-byte seed',r'op erasure_raw_seed (input:W8.t list) (outlen:int) : erasure_seed option = if 0<=outlen<=raw_xof_max_output /\ size input=32 then Some(Array32.of_list W8.zero input) else None.'),
 (MODEL,'programmed setup logs every attempt before expanding the seed',r'module LoggedProgrammedExpand = { proc shake(seed:erasure_seed) : W8.t Array192.t = { var y:W8.t Array192.t; ErasureSeedLog.used <- seed::ErasureSeedLog.used; y <@ ProgrammedFreshExpand.shake(seed); return y; } }.'),
 (MODEL,'erased expansion logs attempts while leaving the existing E table intact',r'module LoggedErasedExpand = { proc shake(seed:erasure_seed) : W8.t Array192.t = { var y:W8.t Array192.t; ErasureSeedLog.used <- seed::ErasureSeedLog.used; y <@ FreshExpand.shake(seed); return y; } }.'),
 (MODEL,'table agreement is outside all used seeds including rejected attempts',r'op erasure_tables_agree (s:erasure_seed list) (m1 m2:(erasure_seed,W8.t Array192.t) fmap) = forall x,!(List.mem s x) => m1.[x]=m2.[x].'),
 (MODEL,'request and forwarded counters are distinct and cap is a nonnegative explicit policy',r'module EBudgetState = { var requests,forwarded,limit : int var overflow : bool var queries : erasure_seed list proc configure(q:int) = { requests <- 0; forwarded <- 0; limit <- max 0 q; overflow <- false; queries <- []; } }.'),
 (BUDGET,'all requests advance the request count but only forwarded queries enter the hit trace',r'module ErasureBudgetMonitor = { proc request(seed:erasure_seed) : bool = { var allowed:bool; allowed <- EBudgetState.requests<EBudgetState.limit; EBudgetState.requests <- EBudgetState.requests+1; EBudgetState.overflow <- EBudgetState.overflow \/ !allowed; return allowed; } proc forward(seed:erasure_seed) : unit = { EBudgetState.forwarded <- EBudgetState.forwarded+1; EBudgetState.queries <- seed::EBudgetState.queries; ErasureHit.mark(seed); } }.'),
 (BUDGET,'counting is observational and keeps forwarding after the analysis limit',r'module CountEPort(H:CCAExtendedOraclePort) : CCAExtendedOraclePort = { proc e(input:erasure_seed) : W8.t Array192.t = { var allowed:bool; var result:W8.t Array192.t; allowed <@ ErasureBudgetMonitor.request(input); ErasureBudgetMonitor.forward(input); result <@ H.e(input); return result; } proc f=H.f proc g=H.g proc h=H.h proc raw(input:W8.t list,outlen:int) : W8.t list option = { var seed:erasure_seed option; var allowed:bool; var result:W8.t list option; seed <- erasure_raw_seed input outlen; if(seed<>None){ allowed <@ ErasureBudgetMonitor.request(oget seed); ErasureBudgetMonitor.forward(oget seed); } result <@ H.raw(input,outlen); return result; } }.'),
 (BUDGET,'capped ports preserve non-E dispatch and block backend calls on denied E requests',r'module CapEPort(H:CCAExtendedOraclePort) : CCAExtendedOraclePort = { proc e(input:erasure_seed) : W8.t Array192.t = { var allowed:bool; var result:W8.t Array192.t; allowed <@ ErasureBudgetMonitor.request(input); result <- witness; if(allowed){ ErasureBudgetMonitor.forward(input); result <@ H.e(input); } return result; } proc f=H.f proc g=H.g proc h=H.h proc raw(input:W8.t list,outlen:int) : W8.t list option = { var seed:erasure_seed option; var allowed:bool; var result:W8.t list option; seed <- erasure_raw_seed input outlen; allowed <- true; if(seed<>None){allowed <@ ErasureBudgetMonitor.request(oget seed);} result <- None; if(allowed){ if(seed<>None){ErasureBudgetMonitor.forward(oget seed);} result <@ H.raw(input,outlen); } return result; } }.'),
)
MUTATIONS=(
 ('zero-output-raw-E-is-omitted-from-the-effective-count',MODEL,'if 0<=outlen<=raw_xof_max_output','if 0<outlen<=raw_xof_max_output'),
 ('invalid-output-length-is-falsely-counted-as-E',MODEL,r'if 0<=outlen<=raw_xof_max_output /\ size input=32 then','if size input=32 then'),
 ('raw-E-classification-accepts-a-tag-prefix-instead-of-exact-length',MODEL,'size input=32','32<=size input'),
 ('setup-log-deduplicates-attempt-seeds',MODEL,'ErasureSeedLog.used <- seed::ErasureSeedLog.used;','if(!(seed \\in ErasureSeedLog.used)){ErasureSeedLog.used <- seed::ErasureSeedLog.used;}'),
 ('erased-setup-clears-arbitrary-preexisting-E',MODEL,'y <@ FreshExpand.shake(seed);','ROE.init(); y <@ FreshExpand.shake(seed);'),
 ('erased-setup-still-programs-the-seed',MODEL,'y <@ FreshExpand.shake(seed);','y <@ ProgrammedFreshExpand.shake(seed);'),
 ('table-coupling-reverses-the-outside-used-condition',MODEL,'forall x,!(List.mem s x) =>','forall x,(List.mem s x) =>'),
 ('negative-query-limit-is-not-clamped',MODEL,'limit <- max 0 q;','limit <- q;'),
 ('request-counts-only-fresh-forwarded-positions',BUDGET,'EBudgetState.requests <- EBudgetState.requests+1;','if(allowed){EBudgetState.requests <- EBudgetState.requests+1;}'),
 ('cap-admits-one-more-effective-E-request',BUDGET,'allowed <- EBudgetState.requests<EBudgetState.limit;','allowed <- EBudgetState.requests<=EBudgetState.limit;'),
 ('forwarded-query-log-deduplicates-repeated-requests',BUDGET,'EBudgetState.queries <- seed::EBudgetState.queries;','if(!(seed \\in EBudgetState.queries)){EBudgetState.queries <- seed::EBudgetState.queries;}'),
 ('hit-marker-is-moved-to-denied-request-stage',BUDGET,'EBudgetState.requests <- EBudgetState.requests+1;','EBudgetState.requests <- EBudgetState.requests+1; ErasureHit.mark(seed);'),
 ('observational-counter-silently-enforces-the-cap',BUDGET,'allowed <@ ErasureBudgetMonitor.request(input); ErasureBudgetMonitor.forward(input); result <@ H.e(input);','allowed <@ ErasureBudgetMonitor.request(input); if(allowed){ErasureBudgetMonitor.forward(input); result <@ H.e(input);}'),
 ('capped-typed-E-calls-backend-before-checking-allowance',BUDGET,'result <- witness; if(allowed){','result <@ H.e(input); if(allowed){'),
 ('capped-raw-E-returns-Some-empty-instead-of-None',BUDGET,'result <- None; if(allowed){','result <- Some []; if(allowed){'),
 ('non-E-raw-requests-are-blocked-with-the-E-budget',BUDGET,'allowed <- true; if(seed<>None)','allowed <- false; if(seed<>None)'),
)
