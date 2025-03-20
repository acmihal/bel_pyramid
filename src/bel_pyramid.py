import argparse
from itertools import combinations_with_replacement, permutations
from z3 import And, Int, Solver, sat

# Symmetry breaking strategies
StrategyNone = 'NoSymmetryBreaking'
SymmetryBreakingStrategies = [StrategyNone]

def xvar(level, x):
    return Int(f'l{level}_x{x}');

def yvar(level, y):
    return Int(f'l{level}_y{y}');

def zvar(zx, zy):
    return Int(f'zx{zx}_zy{zy}');

def solve(num_levels, symmetry_breaking_strategy=SymmetryBreakingStrategies[0]):
    print(f'Solving for {num_levels} levels.')

    # Number of rows/cols at each level.
    size_at_level = [2 * level + 1 for level in range(num_levels)]

    # Total number of blocks at each level.
    blocks_at_level = [size * size for size in size_at_level]

    # Total number of blocks for the whole pyramid.
    num_blocks = sum(blocks_at_level)

    # Number of labels on blocks.
    num_digits = 2 * (num_levels - 1) + 1

    # List of labels.
    label_list = [f'{digit}' for digit in range(num_digits)]

    # List of all labeled blocks.
    block_list = list(combinations_with_replacement(label_list, 3))

    # List of all permutations for each labeled block.
    permuted_block_list = [sorted(list(set(permutations(block)))) for block in block_list]

    print()
    print('Parameters:')
    print(f'    Level sizes: {size_at_level}')
    print(f'    Level blocks: {blocks_at_level}')
    print(f'    Total blocks: {num_blocks}')
    print(f'    Labels: {label_list}')
    print('    Block List:')
    for ix, block in enumerate(block_list):
        print(f'        {ix}: {block}')
    print('    Permuted blocks:')
    for ix, perm_list in enumerate(permuted_block_list):
        print(f'        {ix}: {perm_list}')

    s = Solver()

    # Each xvar/yvar/zvar must have a label in label_list.
    s.add([And(0 <= xvar(l, x), xvar(l, x) < num_digits) for l, x in enumerate(size_at_level)])
    s.add([And(0 <= yvar(l, y), yvar(l, y) < num_digits) for l, y in enumerate(size_at_level)])
    s.add([And(0 <= zvar(zx, zy), zvar(zx, zy) < num_digits) for zx in range(size_at_level[-1]) for zy in range(size_at_level[-1])])

    # Solve the model.
    solver_result = s.check()

    if solver_result == sat:
        # The pyramid is solvable for num_levels.
        m = s.model()

        # Print the solution.
        print()
        print('Solution:')
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

