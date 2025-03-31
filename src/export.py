import sys
from z3 import Goal, is_not, Not, Tactic, Then, With, Z3_OP_UNINTERPRETED

def print_formula(formula, indent=0, recursive=True):
    i0 = '  ' * (indent)
    i1 = '  ' * (indent + 1)

    formula_str_single_line = ''.join(str(formula).splitlines())
    print(f'{i0}f = {formula_str_single_line}')

    if (recursive):
        print(f'{i1}decl = {formula.decl()}')
        print(f'{i1}num_args = {formula.num_args()}')
        print(f'{i1}params = {formula.params()}')

        arg_list = [formula.arg(arg_ix) for arg_ix in range(formula.num_args())]
        print(f'{i1}args = {arg_list}')

        for child_ix, child in enumerate(formula.children()):
            print(f'{i1} child {child_ix}')
            print_formula(child, indent + 2)

def export_smt2(solver, filename):
    with open(filename, 'w', encoding='ascii') as smt2_file:
        smt2_file.write(solver.to_smt2())

def export_cnf(formulation, solver, filename):
    # Create a goal and add constraints.
    goal = Goal()
    goal.add(solver.assertions())

    # Apply a set of tactics to convert a purely CNF formulation.
    tactic = Then('lia2card', 'dt2bv', 'bit-blast', 'card2bv', 'tseitin-cnf')
    subgoal = tactic(goal)
    formulas = subgoal[0]

    # Collect all variables in all formulas.
    all_vars = set()
    for f in formulas:
        if is_not(f):
            # Formula is a single inverted literal.
            all_vars.add(f.arg(0))
        elif f.kind() == Z3_OP_UNINTERPRETED:
            # Formula is a single positive literal.
            all_vars.add(f)
        else:
            # Formula is a sum of literals.
            for child in f.children():
                if is_not(child):
                    all_vars.add(child.arg(0))
                else:
                    all_vars.add(child)

    # Split all the CNF vars into the placement/nonplacement groups.
    placement_vars_to_bvars = {}
    nonplacement_vars = set()
    for var in all_vars:
        if (bvar := formulation.placement_var_by_name(str(var))) is not None:
            placement_vars_to_bvars[var] = bvar
        else:
            nonplacement_vars.add(var)

    # Map placement vars to integers starting at 1.
    # Enumerating the variables this way allows import to work even if the tactic or finite-domain sort changes.
    sorted_keys = sorted(placement_vars_to_bvars.keys(), key=lambda var: str(var))
    var_to_ix_map = {var:ix for ix, var in enumerate(sorted_keys, start=1)}

    # Nonplacement vars are numbered after the placement vars.
    var_to_ix_map.update({var:ix for ix, var in enumerate(nonplacement_vars, start=1+len(placement_vars_to_bvars))})
        
    with open(filename, 'w', encoding='ascii') as cnf_file:
        # Write cnf header
        cnf_file.write(f"c {' '.join(sys.argv)}\n")
        cnf_file.write(f"p cnf {len(var_to_ix_map)} {len(formulas)}\n")

        for f in formulas:
            if is_not(f):
                # Formula is a single inverted literal.
                cnf_file.write(f"-{var_to_ix_map[f.arg(0)]} ")
            elif f.kind() == Z3_OP_UNINTERPRETED:
                # Formula is a single positive literal.
                cnf_file.write(f"{var_to_ix_map[f]} ")
            else:
                # Formula is a sum of literals.
                for child in f.children():
                    if is_not(child):
                        cnf_file.write(f"-{var_to_ix_map[child.arg(0)]} ")
                    else:
                        cnf_file.write(f"{var_to_ix_map[child]} ")

            cnf_file.write("0\n")

def import_certificate(formulation, filename):
    # Sorting all of the placement bvars in the formulation by name should match the numbering used in the CNF export.
    # One additional list element at the beginning is necessary because CNF starts numbering at 1, not 0.
    sorted_placement_bvars = [None] + sorted(formulation.placement_bvar_map.values(), key=lambda var: str(var))

    assertions = []

    with open(filename, 'r', encoding='ascii') as certificate:
        for line in certificate:
            if line.startswith("v "):
                var_list = line.rstrip().split()
                int_list = [int(var) for var in var_list[1:]]
                for assignment in int_list:
                    if 0 < assignment and assignment < len(sorted_placement_bvars):
                        assertions.append(sorted_placement_bvars[assignment])
                    elif 0 < -assignment and -assignment < len(sorted_placement_bvars):
                        assertions.append(Not(sorted_placement_bvars[-assignment]))

    return assertions

