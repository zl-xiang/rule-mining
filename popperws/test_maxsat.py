from . import maxsat
import pickle
import os
def test_exact_sat():
    dir = './test/test-sat-input.pkl'
    if os.path.exists(dir):
        with open(dir, "rb") as f:
            encoding, soft_lit_groups, weights, settings = pickle.load(f)
            maxsat.exact_lex_solve(encoding, soft_lit_groups, weights, settings)