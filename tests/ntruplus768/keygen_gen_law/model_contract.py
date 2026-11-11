"""Independent unit and public Gen-law trust boundaries; final APIs pending."""
from unit_contract import RULES as UNIT_RULES, MUTATIONS as UNIT_MUTATIONS
from law_contract import RULES as LAW_RULES, MUTATIONS as LAW_MUTATIONS
from caller_contract import RULES as CALLER_RULES, MUTATIONS as CALLER_MUTATIONS
RULES = UNIT_RULES + LAW_RULES + CALLER_RULES
MUTATIONS = UNIT_MUTATIONS + LAW_MUTATIONS + CALLER_MUTATIONS

def check_model(read, ordered, require):
 from check_keygen_gen_law import compact
 for relative,label,expected in RULES:
  require(compact(expected).replace("op[opaque]","op") in read(relative).replace("op[opaque]","op"),label)
