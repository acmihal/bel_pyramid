import argparse
from itertools import chain, combinations_with_replacement, permutations
from z3 import And, Bool, Int, PbEq, Solver, sat

# Symmetry breaking strategies
StrategyNone = 'NoSymmetryBreaking'
SymmetryBreakingStrategies = [StrategyNone]

def xvar(level, x):
    return Int(f'l{level}_x{x}');

def yvar(level, y):
    return Int(f'l{level}_y{y}');

def zvar(zx, zy):
    return Int(f'zx{zx}_zy{zy}');

def block_coordinate_bvar(block, rotation, level, x, y):
    return Bool(f'b{block}_r{rotation}_l{level}_x{x}_y{y}')

def pretty_list(some_list):
    return ' '.join([f'{item:>2}' for item in some_list if item is not None])

def solve(num_levels, symmetry_breaking_strategy=SymmetryBreakingStrategies[0]):
    print(f'Solving for {num_levels} levels.')

    # Number of rows/cols at each level.
    size_at_level = [2 * level + 1 for level in range(num_levels)]

    # Total number of blocks at each level.
    blocks_at_level = [size * size for size in size_at_level]

    # Pyramid height at a given base level xy coordinate.
    height_at_xy = list(range(1, 1 + size_at_level[-1] // 2)) + [num_levels] + list(range(size_at_level[-1] // 2, 0, -1))

    # Total number of blocks for the whole pyramid.
    num_blocks = sum(blocks_at_level)

    # Number of labels on blocks.
    num_labels = 2 * (num_levels - 1) + 1

    # List of all labeled blocks.
    block_list = list(combinations_with_replacement(range(num_labels), 3))

    # List of all rotations for each labeled block.
    rotated_block_list = [sorted(list(set(permutations(block)))) for block in block_list]

    # Map rotated blocks to block-rotations.
    rotation_to_block_rotation = {rotation: (block, rotation_ix) for block, rotation_list in enumerate(rotated_block_list) for rotation_ix, rotation in enumerate(rotation_list)}

    print()
    print('Parameters:')
    print(f'    Level sizes: {size_at_level}')
    #print(f'    Height at XY: {height_at_xy}')
    print(f'    Level blocks: {blocks_at_level}')
    print(f'    Total blocks: {num_blocks}')
    print(f'    Labels: [0, {num_labels})')
    #print('    Block List:')
    #for ix, block in enumerate(block_list):
    #    print(f'        {ix}: {block}')
    #print('    Rotated blocks:')
    #for ix, rotation_list in enumerate(rotated_block_list):
    #    print(f'        {ix}: {rotation_list}')
    #print('    Rotation to block-rotation map:')
    #for rotation_list in rotated_block_list:
    #    for rotation in rotation_list:
    #        block, rotation_ix = rotation_to_block_rotation[rotation]
    #        print(f'    {rotation}: block={block} rotation={rotation_ix}')

    s = Solver()

    # Variables to solve for, organized into convenient arrays.
    zvar_matrix = [[zvar(zx, zy) for zx in range(size_at_level[-1])] for zy in range(size_at_level[-1])]
    yvar_triangle = [[yvar(num_levels - l - 1, zy - l) for l in range(height_at_xy[zy])] for zy in range(size_at_level[-1])]
    xvar_triangle = [[xvar(num_levels - l - 1, zx - l) for l in range(height_at_xy[zx])] for zx in range(size_at_level[-1])]

    print('zvar_matrix')
    for zvar_list in zvar_matrix:
        print(f'    {zvar_list}')

    print('yvar_triangle')
    for yvar_list in yvar_triangle:
        print(f'    {yvar_list}')

    print('xvar_triangle')
    for xvar_list in xvar_triangle:
        print(f'    {xvar_list}')

    # Each xvar/yvar/zvar must have a label in [0, num_labels).
    s.add([And(0 <= var, var < num_labels) for var in chain.from_iterable(zvar_matrix + yvar_triangle + xvar_triangle)])

    # Each block must have exactly one rotation and coordinate.
    s.add([PbEq([(block_coordinate_bvar(block, rotation, level, x, y), 1)
                 for rotation in range(len(rotated_block_list[block]))
                 for level in range(num_levels)
                 for y in range(size_at_level[level])
                 for x in range(size_at_level[level])], 1)
           for block in range(num_blocks)])
    #for block in range(num_blocks):
    #    print(f'PbEq1 {[block_coordinate_bvar(block, rotation, level, x, y) for rotation in range(len(rotated_block_list[block])) for level in range(num_levels) for y in range(size_at_level[level]) for x in range(size_at_level[level])]}')

    # Each xvar/yvar/zvar combination implies a block-rotation at a coordinate.

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

        print('+' + '---' * size_at_level[-1] + '-+')
        for zy in range(size_at_level[-1]):
            print(f'| {pretty_list(zint_matrix[zy])} | {pretty_list(yint_triangle[zy])}')
        print('+' + '---' * size_at_level[-1] + '-+')
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

