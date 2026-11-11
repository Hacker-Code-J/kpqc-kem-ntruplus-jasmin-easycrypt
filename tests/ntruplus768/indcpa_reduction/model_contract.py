"""Reviewed public-reduction interface checks, separate from proof validity."""
import policy

MODEL = policy.PROOF / "NTRUPlus768CPAModel.ec"


def check(text=None):
    code = policy.compact(MODEL.read_text() if text is None else text)
    policy.shared.ordered(code, (
        "module CPACipher = {", "hout<$uniform224;", "ct<@SimEncrypt(FOGActual).run(pk,msg,hout);", "return oget ct;",
        "module CPAPhase(A:CCAExtendedAdversary)", "suffix<@ROF.get(pk);",
        "SimPublic.init(pk,suffix,ct);SimHistory.init();",
        "answer<@A(SimOracles(FOGActual,SimHActual),SimLookup(FOGActual)).guess(pk,ct,key);",
        "module CPAReduction(A:CCAExtendedAdversary)",
        "pk<-pk0;target<$uniform96;other<$uniform96;", "return(target,other);",
        "key<$uniform32;ignored<@CPAPhase(A).run(pk,ct,key);",
        "return !((target,SimPublic.suffix) \\in SimHistory.h);",
        "module CPAGame(B:CPAAdversary)", "ROMInit.init();RawXOFStreams.init();",
        "(pk,sk)<@Keygen(UniformSeedRNG,FreshExpand,SHAKEFROM).run();",
        "(m0,m1)<@B.choose(pk);bit<$dbool;", "ct<@CPACipher.run(pk,if bit then m1 else m0);",
        "guess<@B.guess(ct);return guess=bit;"))
    phase = code.split("moduleCPAPhase(", 1)[1].split("moduletypeCPAAdversary", 1)[0]
    reducer = code.split("moduleCPAReduction(", 1)[1].split("moduleCPAGame(", 1)[0]
    for body in (phase, reducer):
        for forbidden in ("ROG.init", "ROMInit.init", "ROH.init", "ROG.m<-", "ROH.m.[", "CCADecapOracle", "FOContext"):
            policy.require(forbidden not in body, "reducer altered shared/challenge state: " + forbidden)
    policy.require(".guess(pk,ct,key)" in phase, "adversary received changed challenge arguments")


MUTATIONS = (
    ("challenge-uses-cached-H", "hout<$uniform224;", "hout<@ROH.get((msg,witness));"),
    ("independent-message-collision-erased", "other<$uniform96;", "other<-target;"),
    ("reduction-wrong-membership-polarity", "return !((target,SimPublic.suffix)", "return ((target,SimPublic.suffix)"),
    ("target-suffix-not-bound", "(target,SimPublic.suffix)", "(target,witness)"),
    ("reduction-invents-secret-decapsulation", "SimLookup(FOGActual)", "CCADecapOracle"),
    ("reset-challenge-G-before-adversary", "suffix<@ROF.get(pk);", "ROG.init();suffix<@ROF.get(pk);"),
    ("reset-H-in-adaptive-phase", "suffix<@ROF.get(pk);", "ROH.init();suffix<@ROF.get(pk);"),
    ("raw-H-bypasses-public-history", "SimOracles(FOGActual,SimHActual)", "FOGOracles(FOGActual)"),
    ("CPA-challenge-ignores-bit", "if bit then m1 else m0", "m0"),
)
