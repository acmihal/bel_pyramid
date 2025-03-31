import argparse
from functools import partial
from itertools import chain, combinations_with_replacement, permutations, product
import sys
import time
from z3 import And, AtLeast, AtMost, Bool, Const, EnumSort, IntSort, Int, Or, sat, Tactic, Implies

# Symmetry breaking strategies:
StrategyBottomCenter012 = 'BottomCenter012'
StrategyIncreasingAxes = 'IncreasingAxes'
StrategyBothIncreasingAxes = 'BothIncreasingAxes'
StrategyConstructiveBottom = 'ConstructiveBottom'
StrategyConstructiveBottomRecursive = 'ConstructiveBottomRecursive'
StrategyConstructiveShell = 'ConstructiveShell'
StrategyConstructiveShellRecursive = 'ConstructiveShellRecursive'
StrategyAntiMirror = 'AntiMirror'
StrategyIncreasingHvars = 'IncreasingHvars'
StrategyIncreasingVars = 'IncreasingVars'
StrategyKitchenSink = 'KitchenSink'
StrategyTripleDiagonal = 'TripleDiagonal'
StrategyConstructiveDiagonal = 'ConstructiveDiagonal'
StrategyNone = 'NoSymmetryBreaking'
SymmetryBreakingStrategies = [StrategyBottomCenter012,
                              StrategyIncreasingAxes,
                              StrategyBothIncreasingAxes,
                              StrategyConstructiveBottom,
                              StrategyConstructiveBottomRecursive,
                              StrategyConstructiveShell,
                              StrategyConstructiveShellRecursive,
                              StrategyAntiMirror,
                              StrategyIncreasingHvars,
                              StrategyIncreasingVars,
                              StrategyKitchenSink,
                              StrategyTripleDiagonal,
                              StrategyConstructiveDiagonal,
                              StrategyNone]

def indent_str(indent):
    return '  ' * indent

def print_formula(f, indent=0, recursive=True):
    f_str_single_line = ''.join(str(f).splitlines())
    print(f'{indent_str(indent)}f = {f_str_single_line}')
    if (recursive):
        print(f'{indent_str(indent+1)}decl = {f.decl()}')
        print(f'{indent_str(indent+1)}num_args = {f.num_args()}')
        print(f'{indent_str(indent+1)}params = {f.params()}')
        arg_list = [f.arg(arg_ix) for arg_ix in range(f.num_args())]
        print(f'{indent_str(indent+1)}args = {arg_list}')
        for child_ix, child in enumerate(f.children()):
            print(f'{indent_str(indent+1)} child {child_ix}')
            print_formula(child, indent + 2)

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

    # Z3 Sort for block labels.
    #label_sort, label_tuple = IntSort(), list(range(num_labels))
    label_sort, label_tuple = EnumSort('label', [str(x) for x in range(num_labels)])

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

    #s = Tactic('qflia').solver()
    s = Tactic('qffd').solver()
    #s = Tactic('qfbv').solver()

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
        s.add(And(AtMost(*placement_bvars, 1), AtLeast(*placement_bvars, 1)))

    # blocks with at least one zero
    #blocks_with_zero = sum(block.count(0) > 0 for block in block_list)
    ##print(f'block_list={block_list}')
    ##print(f'blocks_with_zero={blocks_with_zero}')
    #from z3 import PbLe
    #for label in label_tuple:
    #    s.add(PbLe([(yvar==label, size_at_level[-1-h]) for yvar_list in yvar_triangle for h, yvar in enumerate(yvar_list)], blocks_with_zero))
    #    s.add(PbLe([(xvar==label, size_at_level[-1-h]) for xvar_list in xvar_triangle for h, xvar in enumerate(xvar_list)], blocks_with_zero))
    #    s.add(PbLe([(hvar_matrix[y][x]==label, matrix_height[y][x]) for x, y in product(range(base), range(base))], blocks_with_zero))

    #
    # Symmetry breaking constraints:
    #

    # Auxiliary Variable representing the closed upper bound on an axis assignment variable.
    # Used by some symmetry breaking strategies.
    def upper_bound(var):
        return Const(f'max_{var}', label_sort)

    if symmetry_breaking_strategy == StrategyBottomCenter012:
        # Constrain the xyz labels of the bottom center block to be 000, 001, or 012.
        xvar, yvar, hvar = coord_to_vars(base // 2, base // 2, 0)
        s.add(Or(And(xvar==label_tuple[0], yvar==label_tuple[0], hvar==label_tuple[0]),
                 And(xvar==label_tuple[0], yvar==label_tuple[0], hvar==label_tuple[1]),
                 And(xvar==label_tuple[0], yvar==label_tuple[1], hvar==label_tuple[2])))

    elif symmetry_breaking_strategy == StrategyIncreasingAxes:
        # Constrain the bottom layer xvar_triangle to be increasing left-to-right.
        bottom_xvars = [xvar_list[0] for xvar_list in xvar_triangle]
        s.add([xvar <= ix for ix, xvar in enumerate(bottom_xvars)])

    elif symmetry_breaking_strategy == StrategyBothIncreasingAxes:
        # Swap pyramid slices so that the bottom xyvars break mirror symmetries.
        bottom_xvars = [xvar_list[0] for xvar_list in xvar_triangle]
        s.add([bottom_xvars[x] <= bottom_xvars[-x-1] for x in range(base // 2)])
        bottom_yvars = [yvar_list[0] for yvar_list in yvar_triangle]
        s.add([bottom_yvars[y] <= bottom_yvars[-y-1] for y in range(base // 2)])

    elif symmetry_breaking_strategy == StrategyConstructiveBottom:
        # Experiment to determine if a constructive solution is possible
        # where the top N-1 layers are a solution to the N-1 layer problem.
        # Not recursive: no constraints on layers N-2 and higher.
        if num_levels > 1:
            s.add([xvar < (num_labels - 2) for xvar_list in xvar_triangle for xvar in xvar_list[1:]])
            s.add([yvar < (num_labels - 2) for yvar_list in yvar_triangle for yvar in yvar_list[1:]])
            s.add([hvar_matrix[y][x] < (num_labels - 2) for x,y in product(range(1, base-1), range(1, base-1))])

    elif symmetry_breaking_strategy == StrategyConstructiveBottomRecursive:
        # Recursive version of the constructive bottom strategy.
        # UNSAT for N=4.
        for level in range(1, num_levels):
            s.add([xvar < (num_labels - 2*level) for xvar_list in xvar_triangle for xvar in xvar_list[level:]])
            s.add([yvar < (num_labels - 2*level) for yvar_list in yvar_triangle for yvar in yvar_list[level:]])
            s.add([hvar_matrix[y][x] < (num_labels - 2*level) for x,y in product(range(level, base-level), range(level, base-level))])

    elif symmetry_breaking_strategy == StrategyConstructiveShell:
        # Experiment to determine if a constructive solution is possible
        # where the "inner pyramid" is a solution to the N-1 layer problem,
        # and the additional layer N blocks are a "shell" on top of the inner pyramid.
        # Not recursive: no constraints on the N-2 pyramid inside the N-1 pyramid, etc.
        if num_levels > 1:
            s.add([xvar < (num_labels - 2) for xvar_list in xvar_triangle for xvar in xvar_list[:-1]])
            s.add([yvar < (num_labels - 2) for yvar_list in yvar_triangle for yvar in yvar_list[:-1]])
            s.add([hvar_matrix[y][x] < (num_labels - 2) for x,y in product(range(1, base-1), range(1, base-1))])

    elif symmetry_breaking_strategy == StrategyConstructiveShellRecursive:
        # Recursive version of the constructive shell strategy.
        # Additional inner pyramids are also constrained to N-2 solutions, N-3, etc.
        # UNSAT for N=4.
        for level in range(1, num_levels):
            s.add([xvar < (num_labels - 2*level) for xvar_list in xvar_triangle for xvar in xvar_list[:-level]])
            s.add([yvar < (num_labels - 2*level) for yvar_list in yvar_triangle for yvar in yvar_list[:-level]])
            s.add([hvar_matrix[y][x] < (num_labels - 2*level) for x,y in product(range(level, base-level), range(level, base-level))])

    elif symmetry_breaking_strategy == StrategyAntiMirror:
        # Top cube must not explore x/y flips
        s.add(xvar_triangle[base//2][-1] <= yvar_triangle[base//2][-1])
        # Cake slices must be increasing.
        bottom_xvars = [xvar_list[0] for xvar_list in xvar_triangle]
        s.add([bottom_xvars[x] <= bottom_xvars[-x-1] for x in range(base // 2)])
        bottom_yvars = [yvar_list[0] for yvar_list in yvar_triangle]
        s.add([bottom_yvars[y] <= bottom_yvars[-y-1] for y in range(base // 2)])
        # Center x/y column must be sorted.
        outer_sort_constraint = []
        for h in range(num_levels - 1):
            inner_sort_constraint = []
            for prior_h in range(h):
                inner_sort_constraint.append(xvar_triangle[base//2][prior_h] == yvar_triangle[base//2][prior_h])
            if h < num_levels - 2:
                inner_sort_constraint.append(xvar_triangle[base//2][h] < yvar_triangle[base//2][h])
            else:
                inner_sort_constraint.append(xvar_triangle[base//2][h] <= yvar_triangle[base//2][h])
            outer_sort_constraint.append(And(inner_sort_constraint))
        if len(outer_sort_constraint) > 0:
            s.add(Or(outer_sort_constraint))
        # Constrain the xyz labels of the bottom center block to be 000, 001, or 012.
        xvar, yvar, hvar = coord_to_vars(base // 2, base // 2, 0)
        s.add(Or(And(xvar==0, yvar==0, hvar==0), And(xvar==0, yvar==0, hvar==1), And(xvar==0, yvar==1, hvar==2)))

    elif symmetry_breaking_strategy == StrategyIncreasingHvars:
        flat_hvars = [hvar_matrix[y][x] for y,x in product(range(base), range(base))]
        s.add(flat_hvars[0] == 0)
        s.add(Int(f'max_{flat_hvars[0]}') == 0)
        for hvar, next_hvar in zip(flat_hvars, flat_hvars[1:]):
            s.add(Implies(next_hvar<=Int(f'max_{hvar}'), Int(f'max_{next_hvar}') == Int(f'max_{hvar}')))
            s.add(Implies(next_hvar>Int(f'max_{hvar}'), Int(f'max_{next_hvar}') == next_hvar))
            s.add(next_hvar<=(Int(f'max_{hvar}') + 1))

    elif symmetry_breaking_strategy == StrategyIncreasingVars:
        #flat_vars = [xvar_triangle[base//2][0], yvar_triangle[base//2][0], hvar_matrix[base//2][base//2]]
        flat_x = [xvar_triangle[base//2][l] for l in range(num_levels)]
        flat_y = [yvar_triangle[base//2][l] for l in range(num_levels)]
        flat_vars = [hvar_matrix[base//2][base//2]] + [xy for pair in zip(flat_x, flat_y) for xy in pair]
        s.add(Int(f'max_{flat_vars[0]}') == 0)
        s.add(flat_vars[0] == 0)
        for v, next_v in zip(flat_vars, flat_vars[1:]):
            s.add(Implies(next_v <= Int(f'max_{v}'), Int(f'max_{next_v}') == Int(f'max_{v}')))
            s.add(Implies(next_v >  Int(f'max_{v}'), Int(f'max_{next_v}') == next_v))
            s.add(next_v <= (Int(f'max_{v}') + 1))

    elif symmetry_breaking_strategy == StrategyKitchenSink and num_levels > 1:
        # Top cube must not explore x/y flips
        s.add(xvar_triangle[base//2][-1] <= yvar_triangle[base//2][-1])

        # Cake slices must be increasing.
        bottom_xvars = [xvar_list[0] for xvar_list in xvar_triangle]
        s.add([bottom_xvars[x] <= bottom_xvars[-x-1] for x in range(base // 2)])
        bottom_yvars = [yvar_list[0] for yvar_list in yvar_triangle]
        s.add([bottom_yvars[y] <= bottom_yvars[-y-1] for y in range(base // 2)])

        # Center xyz vars must be ordered.
        center_x = [xvar_triangle[base//2][l] for l in range(num_levels)]
        center_y = [yvar_triangle[base//2][l] for l in range(num_levels)]
        ordered_vars = [hvar_matrix[base//2][base//2]] + [xy for pair in zip(center_x, center_y) for xy in pair]
        s.add(ordered_vars[0] == label_tuple[0])
        if label_sort == IntSort():
            s.add([And(0 <= upper_bound(v), upper_bound(v) < num_labels) for v in ordered_vars])
        s.add(upper_bound(ordered_vars[0]) == ordered_vars[0])
        for v, next_v in zip(ordered_vars, ordered_vars[1:]):
            s.add(Implies(next_v <= upper_bound(v), upper_bound(next_v) == upper_bound(v)))
            s.add(Implies(next_v >  upper_bound(v), upper_bound(next_v) == next_v))
            s.add(next_v <= upper_bound(v) + 1)

    elif symmetry_breaking_strategy == StrategyTripleDiagonal:
        # Top cube must not explore x/y flips
        #s.add(xvar_triangle[base//2][-1] <= yvar_triangle[base//2][-1])

        # Blocks with all three faces the same must appear along the diagonal on the bottom layer.
        triple_blocks = [block_ix for block_ix, block in enumerate(block_list) if all(x == block[0] for x in block[1:])]
        s.add([Bool(f'b{block_ix}_r0_x{x}_y{x}_h0') for x, block_ix in enumerate(triple_blocks)])

    elif symmetry_breaking_strategy == StrategyConstructiveDiagonal:
        # Blocks with all three faces the same must appear along the diagonal on the bottom layer.
        # UNSAT for num_levels=5
        triple_blocks = [block_ix for block_ix, block in enumerate(block_list) if all(x == block[0] for x in block[1:])]
        s.add([Bool(f'b{block_ix}_r0_x{x}_y{x}_h0') for x, block_ix in enumerate(triple_blocks)])

        for level in range(num_levels):
            l_base = 2 * level + 1
            l_triangle_height = [min(x + 1, l_base - x) for x in range(l_base)]
            s.add([xvar_triangle[x][h] <= 2*level for x in range(l_base) for h in range(l_triangle_height[x])])
            s.add([yvar_triangle[y][h] <= 2*level for y in range(l_base) for h in range(l_triangle_height[y])])
            s.add([hvar_matrix[y][x] <= 2*level for x,y in product(range(l_base), range(l_base))])

    # Finished constructing the formulation.
    smt_cnf_start_time = time.process_time()
    formulation_elapsed_time = smt_cnf_start_time - formulation_start_time
    print()
    print(f'Constraint formulation built in {formulation_elapsed_time:.2f} seconds.')

    with open('bp.smt2', 'w') as smt2_file:
        smt2_file.write(s.to_smt2())

    with open('bp.cnf', 'w', encoding='ascii') as cnf:
        from z3 import Goal, Z3_OP_UNINTERPRETED, is_not, Then, With
        #set_param("cardinality.encoding", "grouped")
        #set_param("pb.solver", "totalizer")
        goal = Goal()
        goal.add(s.assertions())
        #tactic = Then('simplify', 'propagate-values', 'card2bv', 'simplify', 'max-bv-sharing', 'bv1-blast')
        #tactic = Then('lia2pb', 'lia2card', 'eq2bv', 'card2bv', 'pb2bv', 'bv1-blast')
        #tactic = Then('preamble_st', 'lia2pb', With('card2bv', ':cardinality.encoding', 'circuit'), With('pb2bv', ':pb.solver', 'totalizer', ':cardinality.encoding', 'circuit'))
        #tactic = Tactic('lia2card')

        # leaves multi-level statements instead of 2-level logic
        #tactic = Then('lia2card', 'simplify', 'propagate-values', 'simplify')

        #tactic = Tactic('lia2pb')
        #tactic = Tactic('dt2bv')
        #tactic = Then('dt2bv', 'bit-blast', 'tseitin-cnf')
        #tactic = Then('dt2bv', 'bit-blast', 'tseitin-cnf', With('card2bv', 'keep_cardinality_constraints', False, ':cardinality.encoding', 'unate'))
        #tactic = Then('dt2bv', 'bit-blast', 'tseitin-cnf', 'card2bv', With('sat-preprocess', 'cardinality.solver', False))
        #tactic = Then('dt2bv', 'bit-blast', 'tseitin-cnf', With('card2bv', 'keep_cardinality_constraints', False), With('sat-preprocess', 'cardinality.solver', False), 'simplify')

        # GOOD ONE
        #tactic = Then('dt2bv', 'bit-blast', 'tseitin-cnf', 'card2bv', With('sat-preprocess', 'cardinality.solver', False), 'simplify')

        #tactic = Tactic('lia2pb')
        #tactic = Then('lia2pb', 'pb2bv')
        #tactic = Tactic('qffd')
        #tactic = Tactic('dt2bv')
        #tactic = Then('dt2bv', 'bit-blast', 'card2bv')
        #tactic = Then('dt2bv', 'bit-blast', With('card2bv', 'keep_cardinality_constraints', False))
        #tactic = Then('dt2bv', 'bit-blast', With('card2bv', 'cardinality.encoding', 'grouped'))
        #tactic = Then('dt2bv', 'bit-blast', With('card2bv', 'keep_cardinality_constraints', False, 'cardinality.encoding', 'grouped'))
        #tactic = Then('dt2bv', 'bit-blast', 'card2bv', 'tseitin-cnf')
        #tactic = Tactic('card2bv')
        tactic = With('card2bv', 'keep_cardinality_constraints', True)
        applyResult = tactic(goal)

        #  dictionary maps from BoolExpr to int
        var2id = {}
        result = applyResult[0]  #  result is a Goal
        for f in result:
            print_formula(f, recursive=False)
            if (is_not(f)):
                #  a clause with just one literal
                var2id[f.arg(0)] = 0
            elif f.kind() == Z3_OP_UNINTERPRETED:
                #  single non-inverted literal
                var2id[f] = 0
            else:
                for ix, e in enumerate(f.children()):
                    if is_not(e):
                        var2id[e.arg(0)] = 0
                    else:
                        var2id[e] = 0

        # Assign ids to everything in var2id starting at 1 and incrementing.
        # Also make the reverse map.
        id = 0
        id2var = {}
        for key in var2id.keys():
            var2id[key] = (id := id+1)
            id2var[id] = key

        cnf.write(f"c {' '.join(sys.argv)}\n")
        cnf.write("c DIMACS CNF file\n")

        cnf.write("c\n")
        cnf.write("c Translation table between variable names and literal IDs\n")
        for k, v in id2var.items():
            name = v.decl().name()
            if not (('!' in name) or (name.startswith("_"))):
                #  no auxiliary switching variables
                cnf.write(f"c {name} <-> {k}\n")
        cnf.write("c\n")

        cnf.write(f"p cnf {len(var2id)} {len(result)}\n")
        for f in result:
            if is_not(f):
                cnf.write(f"-{var2id[f.arg(0)]} ")
            elif f.kind() == Z3_OP_UNINTERPRETED:
                #  single non-inverted literal
                cnf.write(f"{var2id[f]} ")
            else:
                for e in f.children():
                    if is_not(e):
                        cnf.write(f"-{var2id[e.arg(0)]} ")
                    else:
                        cnf.write(f"{var2id[e]} ")

            cnf.write("0\n")

    # Finished constructing the smt2 and cnf file formats.
    solver_start_time = time.process_time()
    smt_cnf_elapsed_time = solver_start_time - smt_cnf_start_time
    print()
    print(f'SMT2/CNF output completed in {smt_cnf_elapsed_time:.2f} seconds.')

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
    parser = argparse.ArgumentParser(description="Solve Bel's Pyramid for N levels")
    parser.add_argument("N", type=int, help="number of levels in the pyramid")
    parser.add_argument("--strategy", choices=SymmetryBreakingStrategies, default=StrategyBottomCenter012, help="symmetry breaking strategy")
    args = parser.parse_args()
    assert args.N >= 1, 'Number of levels must be >= 1.'
    solve(args.N, args.strategy)

