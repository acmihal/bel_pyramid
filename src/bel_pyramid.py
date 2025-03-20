import argparse
from itertools import chain, combinations_with_replacement, permutations, product
from z3 import And, Bool, Implies, Int, PbEq, Solver, sat

# Symmetry breaking strategies:
StrategyNone = 'NoSymmetryBreaking'
SymmetryBreakingStrategies = [StrategyNone]

def x_ivar(x, h):
    return Int(f'x{x}_h{h}')

def y_ivar(y, h):
    return Int(f'y{y}_h{h}')

def z_ivar(x, y):
    return Int(f'x{x}_y{y}');

def block_coordinate_bvar(block, x, y, h):
    return Bool(f'b{block}_x{x}_y{y}_h{h}')

def pretty_list(some_list):
    return ' '.join([f'{item:>2}' for item in some_list if item is not None])

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

    print()
    print('Parameters:')
    print(f'    Level sizes: {size_at_level}')
    print(f'    Level blocks: {blocks_at_level}')
    print(f'    Total blocks: {num_blocks}')
    print(f'    Labels: [0, {num_labels})')

    s = Solver()

    # Variables to solve for, organized into convenient arrays that reflect the pyramid geometry.
    zvar_matrix = [[z_ivar(x, y) for x in range(base)] for y in range(base)]
    yvar_triangle = [[y_ivar(y, h) for h in range(height_at_xy[y])] for y in range(base)]
    xvar_triangle = [[x_ivar(x, h) for h in range(height_at_xy[x])] for x in range(base)]

    # Each xvar/yvar/zvar must have a label in [0, num_labels).
    s.add([And(0 <= var, var < num_labels) for var in chain.from_iterable(zvar_matrix + yvar_triangle + xvar_triangle)])

    # Each block must have exactly one coordinate.
    s.add([PbEq([(block_coordinate_bvar(block_ix, x, y, h), 1)
                 for x in range(base)
                 for y in range(base)
                 for h in range(min(height_at_xy[x], height_at_xy[y]))], 1)
           for block_ix in range(num_blocks)])

    # Each xvar/yvar/zvar combination implies a block at a coordinate.
    for x, y in product(range(base), range(base)):
        zvar = zvar_matrix[y][x]
        for h, (xvar, yvar) in enumerate(zip(xvar_triangle[x], yvar_triangle[y])):
            #print(f'y={y} x={x} h={h} zvar={zvar} xvar={xvar} yvar={yvar}')
            for xlabel, ylabel, zlabel in product(range(num_labels), range(num_labels), range(num_labels)):
                block_ix = rotation_to_block[(xlabel, ylabel, zlabel)]
                s.add(Implies(And(xvar==xlabel, yvar==ylabel, zvar==zlabel), block_coordinate_bvar(block_ix, x, y, h)))

    # Solve the model.
    solver_result = s.check()

    if solver_result == sat:
        # The pyramid is solvable for num_levels.
        m = s.model()

        # Print the solution.
        print()
        print('Solution:')

        zint_matrix = [[m.eval(var).as_long() for var in zvar_list] for zvar_list in zvar_matrix]
        yint_triangle = [[m.eval(var).as_long() for var in yvar_list] for yvar_list in yvar_triangle]
        xint_triangle = [[m.eval(var).as_long() for var in xvar_list] + [None]*num_levels for xvar_list in xvar_triangle]

        print('+' + '---'*base + '-+')
        for y in range(base):
            print(f'| {pretty_list(zint_matrix[y])} | {pretty_list(yint_triangle[y])}')
        print('+' + '---'*base + '-+')
        for level in range(num_levels):
            print('  ' + '   '*level + pretty_list([xint_list[level] for xint_list in xint_triangle]))

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

