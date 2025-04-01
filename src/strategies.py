from itertools import chain, product
from z3 import And, Or

# Generate a lexicographical ordering constraint between lists of integer variables.
def precedes(a, b):
    if not a:
        return True
    if not b:
        return False
    return Or(a[0] < b[0], And(a[0] == b[0], precedes(a[1:], b[1:])))

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
    # and the additional layer N blocks are a "shell" on top of the inner pyramid.
    # Known to be UNSAT for N=4.
    constraints = []
    for level in range(1, formulation.num_levels):
        max_label = formulation.num_labels - 2 * level
        constraints.extend([xvar < max_label for xvar_list in formulation.xvar_triangle for xvar in xvar_list[:-level]])
        constraints.extend([yvar < max_label for yvar_list in formulation.yvar_triangle for yvar in yvar_list[:-level]])
        constraints.extend([formulation.hvar_matrix[y][x] < max_label for x,y in product(range(level, formulation.base-level), range(level, formulation.base-level))])
    return constraints

def strategy_constructive_diagonal(formulation):
    constraints = []
    for level in range(formulation.num_levels):
        max_label = 2 * level + 1
        base = 2 * level + 1
        triangle = [min(x + 1, base - x) for x in range(base)]
        constraints.extend([formulation.xvar_triangle[x][h] < max_label for x in range(base) for h in range(triangle[x])])
        constraints.extend([formulation.yvar_triangle[y][h] < max_label for y in range(base) for h in range(triangle[y])])
        constraints.extend([formulation.hvar_matrix[y][x] < max_label for x, y in product(range(base), range(base))])
    return constraints

StrategyMap = {'BottomCenter012': strategy_bottom_center_012,
               'TopCubeOrdering': strategy_top_cube_ordering,
               'ConstructiveTripleDiagonal': strategy_constructive_triple_diagonal,
               'ConstructiveBottom': strategy_constructive_bottom,
               'ConstructiveShell': strategy_constructive_shell,
               'ConstructiveDiagonal': strategy_constructive_diagonal,
               'CakeSliceOrdering': strategy_cake_slice_ordering,
               'AntiMirror': strategy_anti_mirror}

