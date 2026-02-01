#!/usr/bin/env python

from popper.util import Settings
# rom popper.loop import learn_solution
from popper.loop3 import learn_solution
from popper.trc_subsume_test import test_gen_cons

if __name__ == '__main__':
    settings = Settings(cmd_line=True)
    test_gen_cons()
    # test_rule_subsume_trc_positive()
    # test_atom_subsumes_positive()
    # prog = score = stats = None
    # # atoms_subsume(c1={},c2={})
    # prog, score, stats = learn_solution(settings)
    # # print(prog)
    # if prog != None:
    #     settings.print_prog_score(prog, score)
    # else:
    #     print('NO SOLUTION')
    # if settings.show_stats:
    #     stats.show()