import pytest
from z3 import PbEq, Bool, Solver, sat, Not, And
from itertools import permutations

def test_groups():
    # Create 5 groups that add to 21 using a total of 18x1's, 8x2's, 7x3's, and 10x5's
    s = Solver()
    bvar_matrix = [[[Bool(f'g{group}_1_{x}') for x in range(18)],
                    [Bool(f'g{group}_2_{x}') for x in range(8)],
                    [Bool(f'g{group}_3_{x}') for x in range(7)],
                    [Bool(f'g{group}_5_{x}') for x in range(10)]] for group in range(5)]

    s.add([PbEq([(bvar, 1) for bvar in bvar_matrix[group][0]]
                +[(bvar, 2) for bvar in bvar_matrix[group][1]]
                +[(bvar, 3) for bvar in bvar_matrix[group][2]]
                +[(bvar, 5) for bvar in bvar_matrix[group][3]], 21) for group in range(len(bvar_matrix))])

    s.add([PbEq([(bvar_matrix[group][d][x], 1) for group in range(len(bvar_matrix))], 1) for d in range(len(bvar_matrix[0])) for x in range(len(bvar_matrix[0][d]))])

    num_sat_solutions = 0

    perm_list = list(permutations(range(5)))
    print(perm_list)
    print(len(perm_list))

    while True:
        solver_result = s.check()

        if solver_result == sat:
            num_sat_solutions = num_sat_solutions + 1
            m = s.model()
            solution_forbidding_clause = [[] for _ in range(len(perm_list))]
            print()
            print(f'Solution {num_sat_solutions}:')
            print('Group ' + " ".join(["1"]*18) + " " + " ".join(["2"]*8) + " " + " ".join(["3"]*7) + " " + " ".join(["5"]*10))
            for group_ix, group_list in enumerate(bvar_matrix):
                bvar_assignments = []
                for digit_ix, digit_list in enumerate(group_list):
                    for bvar_ix, bvar in enumerate(digit_list):
                        bvar_assignments.append("X" if m[bvar] else " ")
                        if m[bvar]:
                            for perm in range(len(perm_list)):
                                perm_group_ix = perm_list[perm][group_ix]
                                #print(f'perm {perm} bvar[{group_ix}][{digit_ix}][{bvar_ix}] maps to bvar[{perm_group_ix}][{digit_ix}][{bvar_ix}]')
                                perm_bvar = bvar_matrix[perm_group_ix][digit_ix][bvar_ix]
                                solution_forbidding_clause[perm].append(perm_bvar)
                print(f'{group_ix:>5} ' + " ".join(bvar_assignments))

            s.add([Not(And(clause)) for clause in solution_forbidding_clause])
        else:
            print('unsat')
            break

        #if num_sat_solutions  > 10:
        #    break

