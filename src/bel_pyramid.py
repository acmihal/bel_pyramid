import argparse
from itertools import chain, combinations_with_replacement, permutations, product
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

def block_coordinate_bvar(block, x, y, h):
    return Bool(f'b{block}_x{x}_y{y}_h{h}')

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

    # Map x,y,z labels to a block_list index.
    # This inverts the rotated_block_list.
    rotation_to_block = {rotation: block for block, rotation_list in enumerate(rotated_block_list) for rotation in rotation_list}

    # List of block_ix's that do not have a label.
    blocks_without_label = [[block_ix for block_ix in range(num_blocks) if label not in block_list[block_ix]] for label in range(num_labels)]

    # List of all xyh coordinates in the pyramid.
    xyh_list = [(x, y, h) for x, y in product(range(base), range(base)) for h in range(min(height_at_xy[x], height_at_xy[y]))]

    print()
    print('Parameters:')
    print(f'    Level sizes: {size_at_level}')
    print(f'    Level blocks: {blocks_at_level}')
    print(f'    Total blocks: {num_blocks}')
    print(f'    Labels: [0, {num_labels})')

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

    # Each block must have exactly one coordinate.
    s.add([PbEq([(block_coordinate_bvar(block_ix, x, y, h), 1) for x,y,h in xyh_list], 1) for block_ix in range(num_blocks)])

    # Each coordinate must have exactly one block.
    s.add([PbEq([(block_coordinate_bvar(block_ix, x, y, h), 1) for block_ix in range(num_blocks)], 1) for x,y,h in xyh_list])

    # Each xvar/yvar/zvar combination implies a block at a coordinate.
    for x,y,h in xyh_list:
        xvar, yvar, hvar = coord_to_vars(x, y, h)

        # Assigning all three axis vars implies a specific block at this coordinate.
        for xlabel, ylabel, zlabel in product(range(num_labels), range(num_labels), range(num_labels)):
            block_ix = rotation_to_block[(xlabel, ylabel, zlabel)]
            s.add(Implies(And(xvar==xlabel, yvar==ylabel, hvar==zlabel), block_coordinate_bvar(block_ix, x, y, h)))

        # Any single axis var assignment implies blocks without that label cannot be at this coordinate.
        s.add([Implies(Or(xvar==label, yvar==label, hvar==label),
                       Not(Or([block_coordinate_bvar(block_ix, x, y, h) for block_ix in bad_block_list])))
               for label, bad_block_list in enumerate(blocks_without_label)])

        # Two-axis shortcuts:
        #for label in range(num_labels):
        #    blocks_without_two = [block_ix for block_ix in range(num_blocks) if block_list[block_ix].count(label) < 2]
        #    s.add(Implies(And(xvar==label, yvar==label), Not(Or([block_coordinate_bvar(block_ix, x, y ,h) for block_ix in blocks_without_two]))))
        #    s.add(Implies(And(xvar==label, zvar==label), Not(Or([block_coordinate_bvar(block_ix, x, y ,h) for block_ix in blocks_without_two]))))
        #    s.add(Implies(And(yvar==label, zvar==label), Not(Or([block_coordinate_bvar(block_ix, x, y ,h) for block_ix in blocks_without_two]))))

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

    # Solve the model.
    solver_result = s.check()

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

