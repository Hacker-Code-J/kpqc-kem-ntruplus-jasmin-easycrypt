"""Joint setup and partial continuation trust boundaries; final APIs pending."""
from setup_contract import RULES as SETUP_RULES, MUTATIONS as SETUP_MUTATIONS
from game_contract import RULES as GAME_RULES, MUTATIONS as GAME_MUTATIONS
from prefix_contract import RULES as PREFIX_RULES, MUTATIONS as PREFIX_MUTATIONS
RULES = SETUP_RULES + GAME_RULES + PREFIX_RULES
MUTATIONS = SETUP_MUTATIONS + GAME_MUTATIONS + PREFIX_MUTATIONS

def check_model(read, ordered, require):
 from check_cca_setup import compact
 for relative,label,expected in RULES:
  require(compact(expected).replace("op[opaque]","op") in read(relative).replace("op[opaque]","op"),label)
