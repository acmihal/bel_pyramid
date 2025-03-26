import argparse
from itertools import chain, combinations_with_replacement, permutations, product
import time
from z3 import And, Bool, Int, Or, PbEq, Solver, sat, Not

def x_ivar(x, h):
    return Int(f'x{x}_h{h}')

def y_ivar(y, h):
    return Int(f'y{y}_h{h}')

def h_ivar(x, y):
    return Int(f'x{x}_y{y}');

def placement_bvar(block, rotation, x, y, h):
    return Bool(f'b{block}_r{rotation}_x{x}_y{y}_h{h}')

def pretty_list(some_list):
    return ' '.join([f'{item:>2}' if isinstance(item, int) else '  ' for item in some_list])

def solve(num_levels):
    print(f'Solving for {num_levels} levels.')

    formulation_start_time = time.process_time()

    #
    # Calculate and print basic problem parameters.
    #

    # Number of rows/cols at each level.
    size_at_level = [2 * level + 1 for level in range(num_levels)]

    # Total number of blocks at each level.
    blocks_at_level = [size * size for size in size_at_level]

    # Total number of blocks for the whole pyramid.
    num_blocks = sum(blocks_at_level)

    # Number of labels on blocks.
    num_labels = 2 * (num_levels - 1) + 1

    # Length of the base of the pyramid.
    base = size_at_level[-1]

    # Pyramid height at a given base level x or y coordinate.
    height_at_xy = list(range(1, 1 + base // 2)) + [num_levels] + list(range(base // 2, 0, -1))

    # List of all labeled blocks.
    block_list = list(combinations_with_replacement(range(num_labels), 3))

    # List of all rotations for each labeled block.
    rotated_block_list = [sorted(list(set(permutations(block)))) for block in block_list]

    # Helper for iterating over all (x,y,h) coordinates in the pyramid.
    xyh_list = [(x, y, h) for x, y in product(range(base), range(base)) for h in range(min(height_at_xy[x], height_at_xy[y]))]

    label_perm_list = list(permutations(range(num_labels)))

    print()
    print('Parameters:')
    print(f'    Level sizes: {size_at_level}')
    print(f'    Level cubes: {blocks_at_level}')
    print(f'    Total cubes: {num_blocks}')
    print(f'    Labels: [0, {num_labels})')
    print(f'    Blocks: {block_list}')
    print(f'    Label Perm List: {label_perm_list}')

    #
    # Construct solver and add constraints.
    #

    outer_solver = Solver()
    fast_inner_solver = Solver()
    fast_inner_solver.set("smt.core.minimize", True)
    full_inner_solver = Solver()
    full_inner_solver.set("smt.core.minimize", True)

    # Solve for the following Integer variables representing the axis label assignments.
    # The variables are organized into convenient arrays that reflect the pyramid geometry.
    xvar_triangle = [[x_ivar(x, h) for h in range(height_at_xy[x])] for x in range(base)]
    yvar_triangle = [[y_ivar(y, h) for h in range(height_at_xy[y])] for y in range(base)]
    hvar_matrix = [[h_ivar(x, y) for x in range(base)] for y in range(base)]

    # Helper to convert (x,y,h) coordinates to axis label variables.
    def coord_to_vars(x, y, h):
        return xvar_triangle[x][h], yvar_triangle[y][h], hvar_matrix[y][x]

    # Any xvar/yvar/zvar assignment consumes a number of faces_per_digit.
    faces_per_digit = sum(block.count(0) for block in block_list)
    print(f'    faces_per_digit: {faces_per_digit}')
    for label in range(num_labels):
        outer_solver.add(PbEq([(hvar_matrix[y][x] == label, min(height_at_xy[x], height_at_xy[y])) for x, y in product(range(base), range(base))]
                              + [(yvar == label, size_at_level[num_levels - 1 - h]) for yvar_list in yvar_triangle for h, yvar in enumerate(yvar_list)]
                              + [(xvar == label, size_at_level[num_levels - 1 - h]) for xvar_list in xvar_triangle for h, xvar in enumerate(xvar_list)],
                              faces_per_digit))
        fast_inner_solver.add(PbEq([(hvar_matrix[y][x] == label, min(height_at_xy[x], height_at_xy[y])) for x, y in product(range(base), range(base))]
                              + [(yvar == label, size_at_level[num_levels - 1 - h]) for yvar_list in yvar_triangle for h, yvar in enumerate(yvar_list)]
                              + [(xvar == label, size_at_level[num_levels - 1 - h]) for xvar_list in xvar_triangle for h, xvar in enumerate(xvar_list)],
                              faces_per_digit))
        full_inner_solver.add(PbEq([(hvar_matrix[y][x] == label, min(height_at_xy[x], height_at_xy[y])) for x, y in product(range(base), range(base))]
                              + [(yvar == label, size_at_level[num_levels - 1 - h]) for yvar_list in yvar_triangle for h, yvar in enumerate(yvar_list)]
                              + [(xvar == label, size_at_level[num_levels - 1 - h]) for xvar_list in xvar_triangle for h, xvar in enumerate(xvar_list)],
                              faces_per_digit))

    length_to_axis_var_map = {}
    for x,y in product(range(base), range(base)):
        hvar = hvar_matrix[y][x]
        length = min(height_at_xy[x], height_at_xy[y])
        length_to_axis_var_map.setdefault(length, []).append(hvar)
    for yvar_list in yvar_triangle:
        for h, yvar in enumerate(yvar_list):
            length = size_at_level[num_levels - 1 - h]
            length_to_axis_var_map.setdefault(length, []).append(yvar)
    for xvar_list in xvar_triangle:
        for h, xvar in enumerate(xvar_list):
            length = size_at_level[num_levels - 1 - h]
            length_to_axis_var_map.setdefault(length, []).append(xvar)
    print(length_to_axis_var_map)

    # Each axis label variable must have a label in [0, num_labels).
    outer_solver.add([And(0 <= var, var < num_labels) for var in chain.from_iterable(xvar_triangle + yvar_triangle + hvar_matrix)])
    fast_inner_solver.add([And(0 <= var, var < num_labels) for var in chain.from_iterable(xvar_triangle + yvar_triangle + hvar_matrix)])
    full_inner_solver.add([And(0 <= var, var < num_labels) for var in chain.from_iterable(xvar_triangle + yvar_triangle + hvar_matrix)])

    # Symmetry breaking: top cube should not explore x/y flips
    outer_solver.add(xvar_triangle[base//2][-1] <= yvar_triangle[base//2][-1])
    # Cake slice mirror:
    bottom_xvars = [xvar_list[0] for xvar_list in xvar_triangle]
    outer_solver.add([bottom_xvars[x] <= bottom_xvars[-x-1] for x in range(base//2)])
    bottom_yvars = [yvar_list[0] for yvar_list in yvar_triangle]
    outer_solver.add([bottom_yvars[y] <= bottom_yvars[-y-1] for y in range(base//2)])
    # Anti-xymirror
    outer_anti_xymirror_constraint = []
    for h in range(num_levels-1):
        #    h=0     h=0     h=1        h=0     h=1        h=2
        #(x < y) or (x==y && x'<y') or (x==y and x'==y' and x''<=y'')
        inner_anti_xymirror_constraint = []
        for prior_h in range(h):
            inner_anti_xymirror_constraint.append(xvar_triangle[base//2][prior_h]==yvar_triangle[base//2][prior_h])
        if h < num_levels-2:
            inner_anti_xymirror_constraint.append(xvar_triangle[base//2][h] < yvar_triangle[base//2][h])
        else:
            inner_anti_xymirror_constraint.append(xvar_triangle[base//2][h] <= yvar_triangle[base//2][h])
        outer_anti_xymirror_constraint.append(And(inner_anti_xymirror_constraint))
    outer_solver.add(Or(outer_anti_xymirror_constraint))
    #outer_solver.add(bottom_xvars[base//2] <= bottom_yvars[base//2])


    # Constraints:
    # 1. Each block must be placed at a specific (x,y,h) coordinate with a specific rotation.
    # 2. All labels along an axis must match.
    for block_ix, rotation_list in enumerate(rotated_block_list):
        placements = []

        include_in_fast = block_list[block_ix].count(0) > 0

        for rotation_ix, rotation in enumerate(rotation_list):
            for x,y,h in xyh_list:
                # Boolean variable indicating that a certain block with a certain rotation is placed at coordinates (x,y,h).
                bvar = placement_bvar(block_ix, rotation_ix, x, y, h)
                placements.append(bvar)

                # Each placement bvar is equivalent to three axis label assignments (Constraint 2).
                xvar, yvar, hvar = coord_to_vars(x, y, h)
                if include_in_fast:
                    fast_inner_solver.add(bvar == And(xvar==rotation[0], yvar==rotation[1], hvar==rotation[2]))
                full_inner_solver.add(bvar == And(xvar==rotation[0], yvar==rotation[1], hvar==rotation[2]))

        # Each block must have exactly one placement (Constraint 1).
        if include_in_fast:
            fast_inner_solver.add(PbEq([(bvar, 1) for bvar in placements], 1))
        full_inner_solver.add(PbEq([(bvar, 1) for bvar in placements], 1))

    # Finished constructing the formulation.
    solver_start_time = time.process_time()
    formulation_elapsed_time = solver_start_time - formulation_start_time
    print()
    print(f'Constraint formulation built in {formulation_elapsed_time:.2f} seconds.')

    num_fast_solutions = 0
    num_fast_unsat_solutions = 0
    num_cached_fast_solutions = 0
    num_outer_model_iterations = 0
    num_outer_model_iterations_fast_sat = 0
    num_outer_model_iterations_full_sat = 0
    num_outer_model_iterations_full_unsat = 0
    known_good_hypothesis_map = {}

    while True:
        # Solve the model.
        outer_result = outer_solver.check()
        solver_elapsed_time = time.process_time() - solver_start_time

        if outer_result == sat:
            num_outer_model_iterations = num_outer_model_iterations + 1
            outer_model = outer_solver.model()

            print()
            header = [" ".join([f'{key}']*len(value)) for key, value in length_to_axis_var_map.items()]
            print(f'Outer Model Iteration={num_outer_model_iterations} finished in {solver_elapsed_time:.2f} seconds.')
            print('Label  ' + " ".join(header))

            sat_table_rows = 0
            unsat_table_rows = 0
            for label in range(num_labels):
                hypothesis = []
                assignments = []
                solution_forbidding_ivars = []
                for key, value in length_to_axis_var_map.items():
                    for ivar in value:
                        outer_assignment = outer_model.eval(ivar).as_long()
                        assignments.append("X" if outer_assignment==label else " ")
                        if outer_assignment == label:
                            hypothesis.append(ivar==0)
                            solution_forbidding_ivars.append(ivar)
                hashable_hypothesis = ' '.join(assignments)

                if hashable_hypothesis in known_good_hypothesis_map:
                    prior_iteration, prior_perm = known_good_hypothesis_map[hashable_hypothesis]
                    print(f'{label:>5}  ' + " ".join(assignments) + f'  fast check SAT (cached, prior iteration={prior_iteration} row={prior_perm})')
                    sat_table_rows = sat_table_rows + 1
                    num_cached_fast_solutions = num_cached_fast_solutions + 1
                    continue

                fast_inner_result = fast_inner_solver.check(hypothesis)

                if fast_inner_result == sat:
                    num_fast_solutions = num_fast_solutions + 1
                    sat_table_rows = sat_table_rows + 1
                    print(f'{label:>5}  ' + " ".join(assignments) + '  fast check SAT')
                    known_good_hypothesis_map[hashable_hypothesis] = (num_outer_model_iterations, label)
                else:
                    unsat_table_rows = unsat_table_rows + 1
                    num_fast_unsat_solutions = num_fast_unsat_solutions + 1
                    unsat_core = fast_inner_solver.unsat_core()
                    outer_solver.add([Not(And([constraint.arg(0)==any_label for constraint in unsat_core])) for any_label in range(num_labels)])
                    print(f'{label:>5}  ' + " ".join(assignments) + f'  fast check UNSAT core={len(unsat_core)-len(hypothesis)}')

            if unsat_table_rows == 0:
                num_outer_model_iterations_fast_sat = num_outer_model_iterations_fast_sat + 1

                # Try solving the entire hypothesis at once.
                hypothesis = []
                for key, value in length_to_axis_var_map.items():
                    for ivar in value:
                        outer_assignment = outer_model.eval(ivar).as_long()
                        hypothesis.append(ivar==outer_assignment)

                print(f'Outer Model Iteration={num_outer_model_iterations} passes all fast checks, running full check.')
                inner_result = full_inner_solver.check(hypothesis)
                solver_elapsed_time = time.process_time() - solver_start_time
                print(f'Full Inner solver finished in {solver_elapsed_time:.2f} seconds.')
                if inner_result == sat:
                    num_outer_model_iterations_full_sat = num_outer_model_iterations_full_sat + 1
                    inner_model = full_inner_solver.model()
                    xint_triangle = [[inner_model.eval(var).as_long() for var in xvar_list] for xvar_list in xvar_triangle]
                    yint_triangle = [[inner_model.eval(var).as_long() for var in yvar_list] for yvar_list in yvar_triangle]
                    hint_matrix = [[inner_model.eval(var).as_long() for var in hvar_list] for hvar_list in hvar_matrix]
                    print()
                    print('Solution:')
                    print('+' + '---'*base + '-+')
                    for y in range(base):
                        print(f'| {pretty_list(hint_matrix[y])} | {pretty_list(yint_triangle[y])}')
                    print('+' + '---'*base + '-+')
                    for level in range(num_levels):
                        padded_xint_triangle_col = [xint_list[level] if level < len(xint_list) else None for xint_list in xint_triangle]
                        print(f'  {pretty_list(padded_xint_triangle_col)}')

                    # Test the solution.
                    discovered_blocks = []
                    for x,y,h in xyh_list:
                        xvar, yvar, hvar = coord_to_vars(x, y, h)
                        xint, yint, hint = inner_model.eval(xvar).as_long(), inner_model.eval(yvar).as_long(), inner_model.eval(hvar).as_long()
                        discovered_blocks.append(tuple(sorted([xint, yint, hint])))
                    assert sorted(discovered_blocks) == block_list, "Solution test failed: not all expected blocks found in pyramid"

                    # Outer solver should never explore any permutation of the table again.
                    solution_forbidding_clause = [[] for _ in range(len(label_perm_list))]
                    for key, value in length_to_axis_var_map.items():
                        for ivar in value:
                            outer_assignment = outer_model.eval(ivar).as_long()
                            for perm_ix, perm in enumerate(label_perm_list):
                                inner_assignment = perm[outer_assignment]
                                solution_forbidding_clause[perm_ix].append(ivar == inner_assignment)
                    outer_solver.add([Not(And(clause)) for clause in solution_forbidding_clause])
                else:
                    num_outer_model_iterations_full_unsat = num_outer_model_iterations_full_unsat + 1
                    unsat_core = full_inner_solver.unsat_core()
                    #for ix, constraint in enumerate(unsat_core):
                    #    print(f'    unsat core constraint {ix} = {[constraint.arg(0), constraint.decl(), constraint.arg(1)]}')
                    print(f'Outer Model Iteration={num_outer_model_iterations} is UNSAT, core={len(unsat_core)-len(hypothesis)}')

                    # Outer solver should never explore any permutation of the unsat core again.
                    solution_forbidding_clause = [[] for _ in range(len(label_perm_list))]
                    for constraint in unsat_core:
                        for perm_ix, perm in enumerate(label_perm_list):
                            solution_forbidding_clause[perm_ix].append(constraint.arg(0)==perm[constraint.arg(1).as_long()])
                    outer_solver.add([Not(And(clause)) for clause in solution_forbidding_clause])

        else:
            # outer model is UNSAT.
            print()
            print(f'Outer Model is exhausted in {solver_elapsed_time:.2f} seconds.')
            break

    # Print summary of good rows.
    print()
    print(f'Found {len(known_good_hypothesis_map)} fast SAT rows.')
    print(f'Solution  Iteration  Permutation  ' + ' '.join(header))
    for ix, (key, (iteration, perm)) in enumerate(known_good_hypothesis_map.items()):
        print(f'{(ix):>8}  {iteration:>9}  {perm:>11}  {key}')

    print()
    print(f'Summary:')
    print(f'    Outer Model Iterations: {num_outer_model_iterations}')
    print(f'    Pass Fast Check: {num_outer_model_iterations_fast_sat}')
    print(f'         Fast SAT rows: {num_fast_solutions}')
    print(f'         Cached Fast SAT rows: {num_cached_fast_solutions}')
    print(f'         Fast UNSAT rows: {num_fast_unsat_solutions}')
    print(f'    Pass Full Check: {num_outer_model_iterations_full_sat}')
    print(f'    Fail Full Check: {num_outer_model_iterations_full_unsat}')

def main():
    parser = argparse.ArgumentParser(description="Solve Bel's Pyramid for N levels")
    parser.add_argument("N", type=int, help="number of levels in the pyramid")
    args = parser.parse_args()
    solve(args.N)

if __name__ == '__main__':
    main()
