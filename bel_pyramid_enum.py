import argparse
from itertools import chain, combinations_with_replacement, permutations, product
import time
from z3 import And, AtMost, AtLeast, Bool, Const, EnumSort, PbEq, Solver, sat, describe_tactics, Then, Tactic, set_param

# Symmetry breaking strategies:
StrategyNone = 'NoSymmetryBreaking'
SymmetryBreakingStrategies = [StrategyNone]

def solve(num_levels, symmetry_breaking_strategy=SymmetryBreakingStrategies[0]):
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

    # Length of the base of the pyramid.
    base = size_at_level[-1]

    # Height of the front or right pyramid elevations, by x or y base coordinate respectively.
    triangle_height = [min(x + 1, base - x) for x in range(base)]

    # Height of the top pyramid elevation by (y,x) coordinate.
    matrix_height = [[min(triangle_height[x], triangle_height[y]) for x in range(base)] for y in range(base)]

    # List of all (x,y,h) coordinates in the pyramid.
    xyh_list = [(x, y, h) for x, y in product(range(base), range(base)) for h in range(matrix_height[y][x])]

    # Number of labels on blocks.
    num_labels = 2 * (num_levels - 1) + 1

    # Enum Sort for block labels.
    label_sort, label_tuple = EnumSort('label', [str(x) for x in range(num_labels)])

    # List of all labeled blocks.
    block_list = list(combinations_with_replacement(label_tuple, 3))

    # List of all rotations for each labeled block.
    rotated_block_list = [sorted(list(set(permutations(block))), key=lambda t: tuple(label_tuple.index(v) for v in t)) for block in block_list]
    #rotated_block_list = [list(set(permutations(block))) for block in block_list]

    print()
    print('Parameters:')
    print(f'    Level sizes: {size_at_level}')
    print(f'    Level cubes: {blocks_at_level}')
    print(f'    Total cubes: {num_blocks}')
    print(f'    Labels: {label_tuple}')
    print(block_list)
    print(rotated_block_list)

    #
    # Construct solver and add constraints.
    #

    s = Solver() # 134.5 seconds

    # Enable the cardinality solver.
    #s.set("local_search", True)
    #describe_tactics()
    #s = Tactic('default').solver()
    #s = Then('dt2bv', 'card2bv', 'simplify', 'solve-eqs', 'bit-blast', 'sat').solver()
    #s = Then('card2bv', 'default').solver()
    #s = Then('symmetry-reduce', 'default').solver()
    #s = Then('collect-statistics', 'default').solver()
    #s = Then('dt2bv', 'default').solver() #1560 seconds
    #s = Then('dt2bv', 'card2bv', 'default').solver() # 114.47 seconds
    #s = Then('dt2bv', 'card2bv', 'qfbv-sls').solver()
    #s = Then('dt2bv', 'pb2bv', 'default').solver() # unsat
    #s = Tactic('pqffd').solver()
    #s = Then('dt2bv', 'card2bv', 'qfbv').solver()
    #set_param('parallel.enable', True)
    #set_param('parallel.threads.max', 16)

    # Axis label assignment variables.
    # Organized into convenient arrays that reflect the pyramid geometry.
    xvar_triangle = [[Const(f'x{x}_h{h}', label_sort) for h in range(triangle_height[x])] for x in range(base)]
    yvar_triangle = [[Const(f'y{y}_h{h}', label_sort) for h in range(triangle_height[y])] for y in range(base)]
    hvar_matrix = [[Const(f'x{x}_y{y}', label_sort) for x in range(base)] for y in range(base)]
    
    # Helper to convert (x,y,h) coordinates to axis label variables.
    def coord_to_vars(x, y, h):
        return xvar_triangle[x][h], yvar_triangle[y][h], hvar_matrix[y][x]

    # Constraints:
    # 1. Each block must be placed at a specific (x,y,h) coordinate with a specific rotation.
    # 2. All labels along an axis must match.
    for block_ix, rotation_list in enumerate(rotated_block_list):
        placement_bvars = []

        for rotation_ix, rotation in enumerate(rotation_list):
            for x,y,h in xyh_list:
                # Boolean variable indicating that a certain block with a certain rotation is placed at coordinates (x,y,h).
                bvar = Bool(f'b{block_ix}_r{rotation_ix}_x{x}_y{y}_h{h}')
                placement_bvars.append(bvar)

                # Each placement bvar is equivalent to three axis label assignments (Constraint 2).
                xvar, yvar, hvar = coord_to_vars(x, y, h)
                s.add(bvar == And(xvar==rotation[0], yvar==rotation[1], hvar==rotation[2]))

        # Each block must have exactly one placement (Constraint 1).
        #s.add(AtMost(*placement_bvars, 1)) # nothing after 2333 sec
        #s.add(AtLeast(*placement_bvars, 1)) # 57.43 sec, 107.6 with dt2bv,card2bv,default, by itself no soln after 427sec
        #s.add(PbEq([(bvar, 1) for bvar in placement_bvars], 1)) # 137.45 sec, 129 with dt2bv,card2bv,default
        s.add(And(AtMost(*placement_bvars, 1), AtLeast(*placement_bvars, 1)))

    # Face Counting Constraints
    #faces_per_label = sum(block.count(label_tuple[0]) for block in block_list)
    #for label in label_tuple:
    #    s.add(PbEq([(hvar_matrix[y][x] == label, matrix_height[y][x]) for y,x in product(range(base), range(base))]
    #               + [(yvar == label, size_at_level[-1-h]) for yvar_list in yvar_triangle for h, yvar in enumerate(yvar_list)]
    #               + [(xvar == label, size_at_level[-1-h]) for xvar_list in xvar_triangle for h, xvar in enumerate(xvar_list)],
    #               faces_per_label))

    #
    # Symmetry breaking constraints:
    #

    # Finished constructing the formulation.
    solver_start_time = time.process_time()
    formulation_elapsed_time = solver_start_time - formulation_start_time
    print()
    print(f'Constraint formulation built in {formulation_elapsed_time:.2f} seconds.')

    # Solve the model.
    solver_result = s.check()
    solver_elapsed_time = time.process_time() - solver_start_time

    print(f'Solver finished in {solver_elapsed_time:.2f} seconds.')

    if solver_result == sat:
        # The pyramid is solvable for num_levels.
        m = s.model()

        # Pretty-print the model values for a list of vars.
        def pretty_solution(var_list):
            return ' '.join([f'{str(m.eval(var)):>2}' if var is not None else '  ' for var in var_list])

        # Print the solution.
        print()
        print('Solution:')

        print('+' + '---'*base + '-+')
        for y in range(base):
            print('| ' + pretty_solution(hvar_matrix[y]) + ' | ' + pretty_solution(yvar_triangle[y]))
        print('+' + '---'*base + '-+')
        for level in range(num_levels):
            padded_xvar_triangle_column = [xvar_list[level] if level < len(xvar_list) else None for xvar_list in xvar_triangle]
            print('  ' + pretty_solution(padded_xvar_triangle_column))

        # Test the solution.
        discovered_blocks = []
        for x,y,h in xyh_list:
            discovered_blocks.append(tuple(sorted([m.eval(var) for var in coord_to_vars(x, y, h)], key=lambda val: label_tuple.index(val))))
        discovered_blocks.sort(key=lambda t: tuple(label_tuple.index(val) for val in t))
        print(block_list)
        print(discovered_blocks)
        assert discovered_blocks == block_list, "Solution test failed: not all expected blocks found in pyramid"

        return True
    else:
        # The pyramid is not solvable for num_levels.
        print(f'No solution exists for {num_levels} levels.')
        return False

def main():
    parser = argparse.ArgumentParser(description="Solve Bel's Pyramid for N levels")
    parser.add_argument("N", type=int, help="number of levels in the pyramid")
    parser.add_argument("--strategy", choices=SymmetryBreakingStrategies, default=StrategyNone, help="symmetry breaking strategy")
    args = parser.parse_args()
    solve(args.N, args.strategy)

if __name__ == '__main__':
    main()
