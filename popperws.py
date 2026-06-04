#!/usr/bin/env python

from popperws.util import Settings
# rom popper.loop import learn_solution
from popperws.loop3 import learn_solution
from popperws.trc_subsume_test import test_rule_subsume_trc_positive
from popperws.test_maxsat import test_exact_sat

if __name__ == '__main__':
    settings = Settings(cmd_line=True)
    # test_gen_cons()
    # test_rule_subsume_trc_positive()
    # test_atom_subsumes_positive()
    # test_exact_sat()
    prog = score = stats = None
    # atoms_subsume(c1={},c2={})
    prog, score, stats = learn_solution(settings)
    # print(prog)
    if prog != None:
        settings.print_prog_score(prog, score)
    else:
        print('NO SOLUTION')
    if settings.show_stats:
        stats.show()