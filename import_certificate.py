import argparse
from functools import partial
from itertools import chain, combinations_with_replacement, permutations, product
import re
import sys
import time
from z3 import And, AtLeast, AtMost, Bool, Const, EnumSort, IntSort, Int, Not, Or, sat, Tactic, Implies

def solve(num_levels, cnf_file, certificate_file):
    print(f'Importing certificate for {num_levels} levels from cnf file {certificate_file}.')

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

    # Z3 Sort for block labels.
    label_sort, label_tuple = IntSort(), list(range(num_labels))
    #label_sort, label_tuple = EnumSort('label', [str(x) for x in range(num_labels)])

    # Key for sorting label_sort values by position in label_tuple.
    def sort_key(val):
        if isinstance(val, tuple):
            return tuple(sort_key(x) for x in val)
        else:
            return label_tuple.index(val)

    # Always use this key for sorting things containing labels.
    sorted_by_label = partial(sorted, key=sort_key)

    # List of all labeled blocks.
    block_list = list(combinations_with_replacement(label_tuple, 3))

    # List of all rotations for each labeled block.
    rotated_block_list = [sorted_by_label(list(set(permutations(block)))) for block in block_list]

    print()
    print('Parameters:')
    print(f'    Level sizes: {size_at_level}')
    print(f'    Level cubes: {blocks_at_level}')
    print(f'    Total cubes: {num_blocks}')
    print(f'    Labels: {label_tuple}')

    #
    # Construct solver and add constraints.
    #

    s = Tactic('qffd').solver()

    # Axis label assignment variables.
    # Organized into convenient arrays that reflect the pyramid geometry.
    xvar_triangle = [[Const(f'x{x}_h{h}', label_sort) for h in range(triangle_height[x])] for x in range(base)]
    yvar_triangle = [[Const(f'y{y}_h{h}', label_sort) for h in range(triangle_height[y])] for y in range(base)]
    hvar_matrix = [[Const(f'x{x}_y{y}', label_sort) for x in range(base)] for y in range(base)]

    # Helper to convert (x,y,h) coordinates to axis label variables.
    def coord_to_vars(x, y, h):
        return xvar_triangle[x][h], yvar_triangle[y][h], hvar_matrix[y][x]

    # Each axis label variable must have a label in [0, num_labels).
    if label_sort == IntSort():
        s.add([And(0 <= var, var < num_labels) for var in chain.from_iterable(xvar_triangle + yvar_triangle + hvar_matrix)])

    # Constraints:
    # 1. Each block must be placed at a specific (x,y,h) coordinate with a specific rotation.
    # 2. All labels along an axis must match.
    all_bvars = set()
    for block_ix, rotation_list in enumerate(rotated_block_list):
        placement_bvars = []

        for rotation_ix, rotation in enumerate(rotation_list):
            for x,y,h in xyh_list:
                # Boolean variable indicating that a certain block with a certain rotation is placed at coordinates (x,y,h).
                bvar = Bool(f'b{block_ix}_r{rotation_ix}_x{x}_y{y}_h{h}')
                all_bvars.add(bvar)
                placement_bvars.append(bvar)

                # Each placement bvar is equivalent to three axis label assignments (Constraint 2).
                xvar, yvar, hvar = coord_to_vars(x, y, h)
                s.add(bvar == And(xvar==rotation[0], yvar==rotation[1], hvar==rotation[2]))

        # Each block must have exactly one placement (Constraint 1).
        s.add(And(AtMost(*placement_bvars, 1), AtLeast(*placement_bvars, 1)))

    # Finished constructing the formulation.
    smt_cnf_start_time = time.process_time()
    formulation_elapsed_time = smt_cnf_start_time - formulation_start_time
    print()
    print(f'Constraint formulation built in {formulation_elapsed_time:.2f} seconds.')

    with open(cnf_file, 'r', encoding='ascii') as cnf:
        pattern = '^c b(\d+)_r(\d+)_x(\d+)_y(\d+)_h(\d+) <-> (\d+)$'
        prog = re.compile(pattern)
        cnf_to_bvar_map = {}
        found_bvars_in_cnf = set()
        for line in cnf:
            line = line.rstrip()
            result = prog.fullmatch(line)
            if result is not None:
                block_ix, rotation_ix, x, y, h, cnf_var = result.groups()
                #print(f'Found bvar b{block_ix}_r{rotation_ix}_x{x}_y{y}_h{h} <-> {cnf_var}')
                bvar = Bool(f'b{block_ix}_r{rotation_ix}_x{x}_y{y}_h{h}')
                cnf_to_bvar_map[int(cnf_var)] = bvar
                found_bvars_in_cnf.add(bvar)

        found_bvars_in_certificate = set()
        with open(certificate_file, 'r', encoding='ascii') as certificate:
            for line in certificate:
                line = line.rstrip()
                if line.startswith("v "):
                    var_list = line.split()
                    int_list = [int(var) for var in var_list[1:-1]]
                    for assignment in int_list:
                        if assignment in cnf_to_bvar_map:
                            bvar = cnf_to_bvar_map[assignment]
                            s.add(bvar)
                            found_bvars_in_certificate.add(bvar)
                            #print(f'Certificate sets {bvar} = True')
                        elif -assignment in cnf_to_bvar_map:
                            bvar = cnf_to_bvar_map[-assignment]
                            s.add(Not(bvar))
                            found_bvars_in_certificate.add(bvar)
                            #print(f'Certificate sets {bvar} = False')

        print()
        if all_bvars == found_bvars_in_cnf:
            print(f'Found all placement variables in CNF map.')
        else:
            cnf_vars_not_in_all_bvars = found_bvars_in_cnf - all_bvars
            all_bvars_not_in_cnf_vars = all_bvars - found_bvars_in_cnf
            for ix, cnf_var in enumerate(cnf_vars_not_in_all_bvars):
                print(f'CNF map contains unexpected placement var: [{ix}] = {cnf_var}')
            for ix, all_var in enumerate(all_bvars_not_in_cnf_vars):
                print(f'CNF map is missing expected placement var: [{ix}] = {all_var}')

        if found_bvars_in_cnf == found_bvars_in_certificate:
            print(f'Found all CNF map variable assignments in certificate.')
        else:
            cnf_vars_not_in_certificate = found_bvars_in_cnf - found_bvars_in_certificate
            for ix, cnf_var in enumerate(cnf_vars_not_in_certificate):
                print(f'Certificate is missing placement var in CNF map: [{ix}] = {cnf_var}')

    # Finished constructing the smt2 and cnf file formats.
    solver_start_time = time.process_time()
    smt_cnf_elapsed_time = solver_start_time - smt_cnf_start_time
    print()
    print(f'CNF and certificate import completed in {smt_cnf_elapsed_time:.2f} seconds.')

    # Solve the model.
    solver_result = s.check()
    solver_elapsed_time = time.process_time() - solver_start_time

    print()
    print(f'Solver finished in {solver_elapsed_time:.2f} seconds.')

    if solver_result == sat:
        # The pyramid is solvable for num_levels.
        m = s.model()

        # Pretty-print the model values for a list of vars.
        def pretty_solution(var_list):
            if label_sort == IntSort():
                return ' '.join([f'{m.eval(var).as_long():>2}' if var is not None else '  ' for var in var_list])
            else:
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
        discovered_blocks = sorted_by_label([tuple(sorted_by_label([m.eval(var) for var in coord_to_vars(x, y, h)])) for x, y, h in xyh_list])
        assert discovered_blocks == block_list, "Solution test failed: not all expected blocks found in pyramid"

        return True
    else:
        # The pyramid is not solvable for num_levels.
        print(f'No solution exists for {num_levels} levels.')
        return False

def main():
    parser = argparse.ArgumentParser(description="Print solution Bel's Pyramid for N levels")
    parser.add_argument("N", type=int, help="number of levels in the pyramid")
    parser.add_argument("cnf_file", type=str, help="problem CNF file")
    parser.add_argument("certificate_file", type=str, help="solution certificate file")
    args = parser.parse_args()
    assert args.N >= 1, 'Number of levels must be >= 1.'
    solve(args.N, args.cnf_file, args.certificate_file)

if __name__ == '__main__':
    main()
