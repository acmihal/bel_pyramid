from itertools import chain, combinations_with_replacement, permutations, product
from z3 import And, AtLeast, AtMost, Bool, Const, EnumSort, IntSort

class Formulation:

    def __init__(self, num_levels, use_enum=False):
        # Pyramid size.
        self.num_levels = num_levels

        # Number of rows/cols at each level.
        self.size_at_level = [2 * level + 1 for level in range(self.num_levels)]

        # Total number of cubes at each level.
        self.cubes_at_level = [size * size for size in self.size_at_level]

        # Total number of cubes for the whole pyramid.
        self.num_cubes = sum(self.cubes_at_level)

        # Length of the base of the pyramid.
        self.base = self.size_at_level[-1]

        # Height of the front or right pyramid elevations, by x or y base coordinate respectively.
        self.triangle_height = [min(x + 1, self.base - x) for x in range(self.base)]

        # Height of the top pyramid elevation by (y,x) coordinate.
        self.matrix_height = [[min(self.triangle_height[x], self.triangle_height[y]) for x in range(self.base)] for y in range(self.base)]

        # List of all (x,y,h) coordinates in the pyramid.
        self.xyh_list = [(x, y, h) for x, y in product(range(self.base), range(self.base)) for h in range(self.matrix_height[y][x])]

        # Number of labels on cubes.
        self.num_labels = 2 * (self.num_levels - 1) + 1

        # Z3 Sort for cube labels.
        if use_enum:
            self.label_sort, self.label_tuple = EnumSort('label', [str(x) for x in range(self.num_labels)])
        else:
            self.label_sort, self.label_tuple = IntSort(), list(range(self.num_labels))

        # List of all labeled cubes.
        self.cube_list = list(combinations_with_replacement(self.label_tuple, 3))

        # List of all rotations for each labeled cube.
        self.rotated_cube_list = [self.sorted_by_label(list(set(permutations(cube)))) for cube in self.cube_list]

        # Axis label assignment variables.
        # Organized into convenient arrays that reflect the pyramid geometry.
        self.xvar_triangle = [[Const(f'x{x}_h{h}', self.label_sort) for h in range(self.triangle_height[x])] for x in range(self.base)]
        self.yvar_triangle = [[Const(f'y{y}_h{h}', self.label_sort) for h in range(self.triangle_height[y])] for y in range(self.base)]
        self.hvar_matrix = [[Const(f'x{x}_y{y}', self.label_sort) for x in range(self.base)] for y in range(self.base)]

        # Cube-Rotation-Coordinate placement variables.
        self.placement_bvar_map = {(cube_ix, rotation_ix, x, y, h): Bool(f'c{cube_ix}_r{rotation_ix}_x{x}_y{y}_h{h}')
                                   for cube_ix, rotation_list in enumerate(self.rotated_cube_list)
                                   for rotation_ix, rotation in enumerate(rotation_list)
                                   for x,y,h in self.xyh_list}

    # Key for sorting label_sort values by position in label_tuple.
    def sort_key(self, val):
        if isinstance(val, tuple):
            return tuple(self.sort_key(x) for x in val)
        else:
            return self.label_tuple.index(val)

    # Sort a list of label_sort values using sort_key.
    def sorted_by_label(self, some_list):
        return sorted(some_list, key=self.sort_key)

    # Helper to convert (x,y,h) coordinates to axis label variables.
    def coord_to_vars(self, x, y, h):
        return self.xvar_triangle[x][h], self.yvar_triangle[y][h], self.hvar_matrix[y][x]

    # Helper to fetch placement bvars.
    def placement_var(self, cube_ix, rotation_ix, x, y, h):
        return self.placement_bvar_map[(cube_ix, rotation_ix, x, y, h)]

    # Variables that the formulation wants to import from a certificate.
    def import_vars(self):
        return sorted(self.placement_bvar_map.values(), key=lambda var: str(var))

    def get_constraints(self):
        self.axis_label_bounds = []
        self.placement_equalities = []
        self.cube_uniqueness_constraints = []

        # Each axis label variable must have a label in [0, num_labels).
        if self.label_sort == IntSort():
            self.axis_label_bounds = [And(0 <= var, var < self.num_labels) for var in chain.from_iterable(self.xvar_triangle + self.yvar_triangle + self.hvar_matrix)]

        # Constraints:
        # 1. Each cube must be placed at a specific (x,y,h) coordinate with a specific rotation.
        # 2. All labels along an axis must match.
        for cube_ix, rotation_list in enumerate(self.rotated_cube_list):
            cube_placement_bvars = []

            for rotation_ix, rotation in enumerate(rotation_list):
                for x,y,h in self.xyh_list:
                    bvar = self.placement_var(cube_ix, rotation_ix, x, y, h)
                    cube_placement_bvars.append(bvar)

                    # Each placement bvar is equivalent to three axis label assignments (Constraint 2).
                    xvar, yvar, hvar = self.coord_to_vars(x, y, h)
                    self.placement_equalities.append(bvar == And(xvar==rotation[0], yvar==rotation[1], hvar==rotation[2]))

            # Each cube must have exactly one placement (Constraint 1).
            self.cube_uniqueness_constraints.append(And(AtMost(*cube_placement_bvars, 1), AtLeast(*cube_placement_bvars, 1)))

        return self.axis_label_bounds + self.placement_equalities + self.cube_uniqueness_constraints

    def validate_model(self, model):
        # Test if the given model correctly solves the problem.
        discovered_cubes = self.sorted_by_label([tuple(self.sorted_by_label([model.eval(var) for var in self.coord_to_vars(x, y, h)])) for x, y, h in self.xyh_list])
        return discovered_cubes == self.cube_list

    def print_parameters(self):
        print(f'Parameters:')
        print(f'    Levels: {self.num_levels}')
        print(f'    Level Sizes: {self.size_at_level}')
        print(f'    Level Cubes: {self.cubes_at_level}')
        print(f'    Total Cubes: {self.num_cubes}')
        print(f'    Labels: {self.label_tuple}')
        print(f'    Label Sort: {self.label_sort}', flush=True)

    def print_variable_stats(self):
        print(f'Variables:')
        print(f'    X Axis Variables: {sum(len(sublist) for sublist in self.xvar_triangle)}')
        print(f'    Y Axis Variables: {sum(len(sublist) for sublist in self.yvar_triangle)}')
        print(f'    Z Axis Variables: {sum(len(sublist) for sublist in self.hvar_matrix)}')
        print(f'    Placement Variables: {len(self.placement_bvar_map)}', flush=True)

    def print_constraint_stats(self):
        print(f'Constraints:')
        print(f'    Axis Label Bounds: {len(self.axis_label_bounds)}')
        print(f'    Placement Equalities: {len(self.placement_equalities)}')
        print(f'    Cube Uniqueness Constraints: {len(self.cube_uniqueness_constraints)}', flush=True)

    def print_model(self, model):
        # Pretty-print the model values for a list of vars.
        def pretty_evals(var_list):
            if self.label_sort == IntSort():
                return ' '.join([f'{model.eval(var).as_long():>2}' if var is not None else '  ' for var in var_list])
            else:
                return ' '.join([f'{str(model.eval(var)):>2}' if var is not None else '  ' for var in var_list])

        # Print the solution.
        print('Solution:')

        print('+' + '---'*self.base + '-+')
        for y in range(self.base):
            print('| ' + pretty_evals(self.hvar_matrix[y]) + ' | ' + pretty_evals(self.yvar_triangle[y]))
        print('+' + '---'*self.base + '-+')
        for level in range(self.num_levels):
            padded_xvar_triangle_column = [xvar_list[level] if level < len(xvar_list) else None for xvar_list in self.xvar_triangle]
            print('  ' + pretty_evals(padded_xvar_triangle_column))

