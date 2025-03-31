from z3 import And, Or

def strategy_bottom_center_012(formulation):
    # Constrain the xyz labels of the bottom center cube to be 000, 001, or 012.
    xvar, yvar, hvar = formulation.coord_to_vars(formulation.base // 2, formulation.base // 2, 0)
    a = formulation.label_tuple[0]
    b = formulation.label_tuple[1]
    c = formulation.label_tuple[2]
    return [Or(And(xvar==a, yvar==a, hvar==a),
               And(xvar==a, yvar==a, hvar==b),
               And(xvar==a, yvar==b, hvar==c))]

def strategy_top_cube_ordering(formulation):
    # Top cube must be x/y flipped so that x <= y.
    top_x = formulation.xvar_triangle[formulation.base//2][-1]
    top_y = formulation.yvar_triangle[formulation.base//2][-1]
    return [top_x <= top_y]

def strategy_triple_diagonal(formulation):
    # Blocks with all three faces the same must appear along the diagonal on the bottom layer.
    triple_cubes = [cube_ix for cube_ix, cube in enumerate(formulation.cube_list) if all(x == cube[0] for x in cube[1:])]
    return [formulation.placement_var(cube_ix, 0, x, x, 0) for x, cube_ix in enumerate(triple_cubes)]

def strategy_cake_slice_ordering(formulation):
    # Swap pyramid cake slices so that the bottom xyvars break mirror symmetries.
    bottom_xvars = [xvar_list[0] for xvar_list in formulation.xvar_triangle]
    bottom_yvars = [yvar_list[0] for yvar_list in formulation.yvar_triangle]
    return (  [bottom_xvars[x] <= bottom_xvars[-x-1] for x in range(formulation.base // 2)]
            + [bottom_yvars[y] <= bottom_yvars[-y-1] for y in range(formulation.base // 2)])

StrategyMap = {'BottomCenter012': strategy_bottom_center_012,
               'TopCubeOrdering': strategy_top_cube_ordering,
               'TripleDiagonal': strategy_triple_diagonal,
               'CakeSliceOrdering': strategy_cake_slice_ordering}

