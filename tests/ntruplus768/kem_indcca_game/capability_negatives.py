"""Reject adversaries that read hidden backing state at the actual game theorem."""
TARGET='cca_original_option_equiv'
HEADER='''require import AllCore FMap.
from Jasmin require import JWord.
require import Array32 Array1152 Array2336.
require import NTRUPlus768CCAOraclePorts NTRUPlus768RawXOF.
require import NTRUPlus768CCADecapOracle NTRUPlus768ROMOracles NTRUPlus768CCAGame.
'''
NEGATIVES={}
for name,variable,expression in (
 ('LeakSecretKey','CCADecapOracle.sk','CCADecapOracle.sk=witness'),
 ('LeakROH','ROH.m','ROH.m=empty')):
 source=HEADER+'''module '''+name+'''(H:CCAExtendedOraclePort,D:CCADecapPort) = {
 proc guess(pk:W8.t Array1152.t,ct:W8.t Array1152.t,key:W8.t Array32.t) : bool = {
  return '''+expression+''';
 }
}.
lemma __capability_rejected : true.
proof. have forbidden := '''+TARGET+' '+name+'''. trivial. qed.
'''
 NEGATIVES[name]={'source':source,'forbidden_variable':variable,'semantic_target':TARGET}
