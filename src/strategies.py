from itertools import chain, product
from z3 import And, If, Int, Or, PbEq, PbLe

# Generate a lexicographical ordering constraint between lists of integer variables.
def precedes(a, b):
    if not a:
        return True
    if not b:
        return False
    return Or(a[0] < b[0], And(a[0] == b[0], precedes(a[1:], b[1:])))

# Generates a constraint that the list of integer variables be monotonically increasing.
def monotonic(a):
    if len(a) < 2:
        return True
    else:
        return And(a[0] <= a[1], monotonic(a[1:]))

# Generates a constraint that the list of integer variables uses the lexicographically first label permutation.
def first_permutation(a, num_labels, previous_max=-1):
    if not a:
        return True
    else:
        # Auxiliary variable representing the closed upper bound on the labels seen so far in the list.
        next_max = Int(f'max_{str(a[0])}')
        return And(0 <= next_max,
                   next_max < num_labels,
                   If(a[0] <= previous_max, next_max==previous_max, next_max==a[0]),
                   a[0] <= previous_max + 1,
                   first_permutation(a[1:], num_labels, next_max))

def strategy_bottom_center_012(formulation):
    # Constrain the xyz labels of the bottom center cube to be 000, 001, or 012.
    # This is a weak label permutation symmetry breaking constraint.
    xvar, yvar, hvar = formulation.coord_to_vars(formulation.base // 2, formulation.base // 2, 0)
    a = formulation.label_tuple[0]
    b = formulation.label_tuple[1]
    c = formulation.label_tuple[2]
    return [Or(And(xvar==a, yvar==a, hvar==a),
               And(xvar==a, yvar==a, hvar==b),
               And(xvar==a, yvar==b, hvar==c))]

def strategy_top_cube_ordering(formulation):
    # Top cube must be x/y flipped so that x <= y.
    # This is a weak geometric symmetry breaking constraint.
    top_x = formulation.xvar_triangle[formulation.base//2][-1]
    top_y = formulation.yvar_triangle[formulation.base//2][-1]
    return [top_x <= top_y]

def strategy_cake_slice_ordering(formulation):
    # Swap pyramid cake slices so that x/y var stacks break geometric symmetries on the x/y axes.
    constraints = []
    constraints.extend([precedes(formulation.xvar_triangle[x], formulation.xvar_triangle[-x-1]) for x in range(formulation.base // 2)])
    constraints.extend([precedes(formulation.yvar_triangle[y], formulation.yvar_triangle[-y-1]) for y in range(formulation.base // 2)])
    return constraints

def strategy_anti_mirror(formulation):
    # A stronger geometric and label permutation symmetry breaking strategy that combines a few of the weaker strategies.
    constraints = []
    constraints.extend(strategy_bottom_center_012(formulation))
    constraints.extend(strategy_top_cube_ordering(formulation))
    constraints.extend(strategy_cake_slice_ordering(formulation))
    flat_xvars = list(chain.from_iterable(formulation.xvar_triangle))
    flat_yvars = list(chain.from_iterable(formulation.yvar_triangle))
    constraints.append(precedes(flat_xvars, flat_yvars))
    return constraints

def strategy_constructive_triple_diagonal(formulation):
    # Blocks with all three faces the same must appear along the diagonal on the bottom layer.
    # This is a constructive approach.
    triple_cubes = [cube_ix for cube_ix, cube in enumerate(formulation.cube_list) if all(x == cube[0] for x in cube[1:])]
    return [formulation.placement_var(cube_ix, 0, x, x, 0) for x, cube_ix in enumerate(triple_cubes)]

def strategy_constructive_bottom(formulation):
    # Constructive approach where layer N is added underneath a solved N-1 layer pyramid.
    # Known to be UNSAT for N=4.
    constraints = []
    for level in range(1, formulation.num_levels):
        max_label = formulation.num_labels - 2 * level
        constraints.extend([xvar < max_label for xvar_list in formulation.xvar_triangle for xvar in xvar_list[level:]])
        constraints.extend([yvar < max_label for yvar_list in formulation.yvar_triangle for yvar in yvar_list[level:]])
        constraints.extend([formulation.hvar_matrix[y][x] < max_label for x,y in product(range(level, formulation.base-level), range(level, formulation.base-level))])
    return constraints

def strategy_constructive_shell(formulation):
    # Constructive approach where the "inner pyramid" is a solution to the N-1 layer problem,
    # and the additional layer N cubes are a "shell" on top of the inner pyramid.
    # Known to be UNSAT for N=4.
    constraints = []
    for level in range(1, formulation.num_levels):
        max_label = formulation.num_labels - 2 * level
        constraints.extend([xvar < max_label for xvar_list in formulation.xvar_triangle for xvar in xvar_list[:-level]])
        constraints.extend([yvar < max_label for yvar_list in formulation.yvar_triangle for yvar in yvar_list[:-level]])
        constraints.extend([formulation.hvar_matrix[y][x] < max_label for x,y in product(range(level, formulation.base-level), range(level, formulation.base-level))])
    return constraints

def strategy_constructive_diagonal(formulation):
    # Constructive approach where the solved N-1 pyramid is in the upper-left corner of the new N pyramid,
    # and the additional cubes are added diagonally in the front, right, and above.
    # Known to be UNSAT for N=5.
    constraints = []
    for level in range(formulation.num_levels):
        max_label = 2 * level + 1
        base = 2 * level + 1
        triangle = [min(x + 1, base - x) for x in range(base)]
        constraints.extend([formulation.xvar_triangle[x][h] < max_label for x in range(base) for h in range(triangle[x])])
        constraints.extend([formulation.yvar_triangle[y][h] < max_label for y in range(base) for h in range(triangle[y])])
        constraints.extend([formulation.hvar_matrix[y][x] < max_label for x, y in product(range(base), range(base))])
    return constraints

def strategy_increasing_x_axis(formulation):
    return [monotonic([xvar_list[0] for xvar_list in formulation.xvar_triangle])]

def strategy_label_permutation(formulation):
    # This is a strong label permutation symmetry breaking constraint.
    flat_vars = list(chain.from_iterable(formulation.hvar_matrix + formulation.xvar_triangle + formulation.yvar_triangle))
    return [first_permutation(flat_vars, formulation.num_labels)]

def strategy_face_pbeq_constraints(formulation):
    faces = sum(cube.count(formulation.label_tuple[0]) for cube in formulation.cube_list)
    constraints = []
    for label in formulation.label_tuple:
        constraints.append(PbEq([(formulation.hvar_matrix[y][x]==label, formulation.matrix_height[y][x]) for x, y in product(range(formulation.base), range(formulation.base))]
                                + [(yvar==label, formulation.size_at_level[-1-h]) for yvar_list in formulation.yvar_triangle for h, yvar in enumerate(yvar_list)]
                                + [(xvar==label, formulation.size_at_level[-1-h]) for xvar_list in formulation.xvar_triangle for h, xvar in enumerate(xvar_list)]
                                , faces))
    return constraints

def strategy_face_pble_constraints(formulation):
    faces = sum(cube.count(formulation.label_tuple[0]) > 0 for cube in formulation.cube_list)
    constraints = []
    for label in formulation.label_tuple:
        constraints.append(PbLe([(yvar==label, formulation.size_at_level[-1-h]) for yvar_list in formulation.yvar_triangle for h, yvar in enumerate(yvar_list)], faces))
        constraints.append(PbLe([(xvar==label, formulation.size_at_level[-1-h]) for xvar_list in formulation.xvar_triangle for h, xvar in enumerate(xvar_list)], faces))
        constraints.append(PbLe([(formulation.hvar_matrix[y][x]==label, formulation.matrix_height[y][x]) for x, y in product(range(formulation.base), range(formulation.base))], faces))
    return constraints

StrategyMap = {'BottomCenter012': strategy_bottom_center_012,
               'TopCubeOrdering': strategy_top_cube_ordering,
               'ConstructiveTripleDiagonal': strategy_constructive_triple_diagonal,
               'ConstructiveBottom': strategy_constructive_bottom,
               'ConstructiveShell': strategy_constructive_shell,
               'ConstructiveDiagonal': strategy_constructive_diagonal,
               'CakeSliceOrdering': strategy_cake_slice_ordering,
               'AntiMirror': strategy_anti_mirror,
               'IncreasingXAxis': strategy_increasing_x_axis,
               'LabelPermutation': strategy_label_permutation,
               'FacePBEQ': strategy_face_pbeq_constraints,
               'FacePBLE': strategy_face_pble_constraints}

