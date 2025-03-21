import argparse
from itertools import chain, combinations_with_replacement, permutations, product
import time
from z3 import And, Bool, Implies, Int, Not, Or, PbEq, Solver, sat

# Symmetry breaking strategies:
StrategyBottomCenter012 = 'BottomCenter012'
StrategyNone = 'NoSymmetryBreaking'
SymmetryBreakingStrategies = [StrategyBottomCenter012, StrategyNone]

def x_ivar(x, h):
    return Int(f'x{x}_h{h}')

def y_ivar(y, h):
    return Int(f'y{y}_h{h}')

def h_ivar(x, y):
    return Int(f'x{x}_y{y}');

def block_rotation_coordinate_bvar(block, rotation, x, y, h):
    return Bool(f'b{block}_r{rotation}_x{x}_y{y}_h{h}')

def pretty_list(some_list):
    return ' '.join([f'{item:>2}' if isinstance(item, int) else '  ' for item in some_list])

def solve(num_levels, symmetry_breaking_strategy=SymmetryBreakingStrategies[0]):
    print(f'Solving for {num_levels} levels.')

    # Number of rows/cols at each level.
    size_at_level = [2 * level + 1 for level in range(num_levels)]

    # Total number of blocks at each level.
    blocks_at_level = [size * size for size in size_at_level]

    # Length of the base of the pyramid.
    base = size_at_level[-1]

    # Pyramid height at a given base level x or y coordinate.
    height_at_xy = list(range(1, 1 + base // 2)) + [num_levels] + list(range(base // 2, 0, -1))

    # Total number of blocks for the whole pyramid.
    num_blocks = sum(blocks_at_level)

    # Number of labels on blocks.
    num_labels = 2 * (num_levels - 1) + 1

    # List of all labeled blocks.
    block_list = list(combinations_with_replacement(range(num_labels), 3))

    # List of all rotations for each labeled block.
    rotated_block_list = [sorted(list(set(permutations(block)))) for block in block_list]

    # Helper to get the number of unique rotations per block_ix.
    num_rotations = [len(rotation_list) for rotation_list in rotated_block_list]

    # Helper for iterating over all (x,y,h) coordinates in the pyramid.
    xyh_list = [(x, y, h) for x, y in product(range(base), range(base)) for h in range(min(height_at_xy[x], height_at_xy[y]))]

    # Helper for iterating over all (block_ix, rotation_ix) pairs.
    brix_list = [(block_ix, rotation_ix) for block_ix, num_rots in enumerate(num_rotations) for rotation_ix in range(num_rots)]

    # (block_ix, rotation_ix) pairs that don't have a given x, y, or h label.
    # Once an axis has a label assigned, all block-rotations without that axis-label
    # are ruled out at all coordinates along that axis.
    def filter_brix(axis, label):
        return [brix for brix in brix_list if rotated_block_list[brix[0]][brix[1]][axis] != label]

    brix_without_x = [filter_brix(0, label) for label in range(num_labels)]
    brix_without_y = [filter_brix(1, label) for label in range(num_labels)]
    brix_without_h = [filter_brix(2, label) for label in range(num_labels)]

    print()
    print('Parameters:')
    print(f'    Level sizes: {size_at_level}')
    print(f'    Level blocks: {blocks_at_level}')
    print(f'    Total blocks: {num_blocks}')
    print(f'    Labels: [0, {num_labels})')

    #
    # Construct solver and add constraints.
    #

    formulation_start_time = time.process_time()
    s = Solver()

    # Variables to solve for, organized into convenient arrays that reflect the pyramid geometry.
    xvar_triangle = [[x_ivar(x, h) for h in range(height_at_xy[x])] for x in range(base)]
    yvar_triangle = [[y_ivar(y, h) for h in range(height_at_xy[y])] for y in range(base)]
    hvar_matrix = [[h_ivar(x, y) for x in range(base)] for y in range(base)]

    # Helper to convert coordinates to axis label vars.
    def coord_to_vars(x, y, h):
        return xvar_triangle[x][h], yvar_triangle[y][h], hvar_matrix[y][x]

    # Each xvar/yvar/zvar must have a label in [0, num_labels).
    s.add([And(0 <= var, var < num_labels) for var in chain.from_iterable(xvar_triangle + yvar_triangle + hvar_matrix)])

    # Each block must have exactly one coordinate-rotation.
    s.add([PbEq([(block_rotation_coordinate_bvar(block_ix, rot_ix, x, y, h), 1) for rot_ix in range(num_rots) for x,y,h in xyh_list], 1) for block_ix, num_rots in enumerate(num_rotations)])

    # Each coordinate must have exactly one block-rotation.
    s.add([PbEq([(block_rotation_coordinate_bvar(block_ix, rot_ix, x, y, h), 1) for block_ix, rot_ix in brix_list], 1) for x,y,h in xyh_list])

    # Each xvar/yvar/zvar combination implies a block at a coordinate.
    for x,y,h in xyh_list:
        xvar, yvar, hvar = coord_to_vars(x, y, h)

        for label in range(num_labels):
            s.add(Implies(xvar==label, Not(Or([block_rotation_coordinate_bvar(block_ix, rot_ix, x, y, h) for block_ix, rot_ix in brix_without_x[label]]))))
            s.add(Implies(yvar==label, Not(Or([block_rotation_coordinate_bvar(block_ix, rot_ix, x, y, h) for block_ix, rot_ix in brix_without_y[label]]))))
            s.add(Implies(hvar==label, Not(Or([block_rotation_coordinate_bvar(block_ix, rot_ix, x, y, h) for block_ix, rot_ix in brix_without_h[label]]))))

    # Any xvar/yvar/zvar assignment consumes a number of faces_per_digit.
    #faces_per_digit = sum(block.count(0) for block in block_list)
    #for label in range(num_labels):
    #    s.add(PbEq([(zvar_matrix[y][x] == label, min(height_at_xy[x], height_at_xy[y])) for x, y in product(range(base), range(base))]
    #               + [(yvar == label, size_at_level[num_levels - 1 - h]) for yvar_list in yvar_triangle for h, yvar in enumerate(yvar_list)]
    #               + [(xvar == label, size_at_level[num_levels - 1 - h]) for xvar_list in xvar_triangle for h, xvar in enumerate(xvar_list)],
    #               faces_per_digit))

    # Symmetry breaking constraints:

    if symmetry_breaking_strategy == StrategyBottomCenter012:
        # Constrain the xyz labels of the bottom center block to be 000, 001, or 012.
        xvar, yvar, hvar = coord_to_vars(base // 2, base // 2, 0)
        s.add(Or(And(xvar==0, yvar==0, hvar==0), And(xvar==0, yvar==0, hvar==1), And(xvar==0, yvar==1, hvar==2)))

    solver_start_time = time.process_time()
    formulation_elapsed_time = solver_start_time - formulation_start_time
    print()
    print(f'Constraint formulation built in {formulation_elapsed_time:.2f} seconds.')

    # Solve the model.
    solver_result = s.check()
    solver_elapsed_time = time.process_time() - solver_start_time

    print(f'Solver finished in {solver_elapsed_time:.2f} seconds')

    if solver_result == sat:
        # The pyramid is solvable for num_levels.
        m = s.model()

        # Obtain the integer values of the axis labels from the model.
        xint_triangle = [[m.eval(var).as_long() for var in xvar_list] for xvar_list in xvar_triangle]
        yint_triangle = [[m.eval(var).as_long() for var in yvar_list] for yvar_list in yvar_triangle]
        hint_matrix = [[m.eval(var).as_long() for var in hvar_list] for hvar_list in hvar_matrix]

        # Print the solution.
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
            xint, yint, hint = m.eval(xvar).as_long(), m.eval(yvar).as_long(), m.eval(hvar).as_long()
            discovered_blocks.append(tuple(sorted([xint, yint, hint])))
        assert sorted(discovered_blocks) == block_list, "Solution test failed: not all expected blocks found in pyramid"

        return True
    else:
        # The pyramid is not solvable for num_levels.
        print(f'No solution exists for {num_levels} levels.')
        return False

def main():
    parser = argparse.ArgumentParser(description="Solve Bel's Pyramid for N levels")
    parser.add_argument("N", type=int, help="number of levels in the pyramid")
    parser.add_argument("--strategy", choices=SymmetryBreakingStrategies, default=StrategyBottomCenter012, help="symmetry breaking strategy")
    args = parser.parse_args()
    solve(args.N, args.strategy)

