#!/usr/bin/env python

from popper.util import Settings
from popper.loop import learn_solution
from popper.loop3 import atoms_subsume

if __name__ == '__main__':
    settings = Settings(cmd_line=True)
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
