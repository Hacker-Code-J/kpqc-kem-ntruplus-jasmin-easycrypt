"""E-erasure trust boundaries; final APIs pending."""
from budget_contract import RULES as BUDGET_RULES, MUTATIONS as BUDGET_MUTATIONS
from pool_contract import RULES as POOL_RULES, MUTATIONS as POOL_MUTATIONS
from termination_contract import RULES as TERMINATION_RULES, MUTATIONS as TERMINATION_MUTATIONS
RULES = BUDGET_RULES + POOL_RULES + TERMINATION_RULES
MUTATIONS = BUDGET_MUTATIONS + POOL_MUTATIONS + TERMINATION_MUTATIONS

def check_model(read, ordered, require):
 from check_e_erasure import compact
 for relative,label,expected in RULES:
  require(compact(expected).replace("op[opaque]","op") in read(relative).replace("op[opaque]","op"),label)
