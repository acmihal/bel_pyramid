import sys
from tqdm import tqdm
from z3 import Goal, is_false, is_not, is_or, Not, Tactic, Then, With, Z3_OP_UNINTERPRETED

def print_formula(formula, indent=0, recursive=True):
    i0 = '  ' * (indent)
    i1 = '  ' * (indent + 1)

    formula_str_single_line = ''.join(str(formula).splitlines())
    print(f'{i0}f = {formula_str_single_line}')

    if (recursive):
        print(f'{i1}decl = {formula.decl()}')
        print(f'{i1}name = {formula.decl().name()} type={type(formula.decl().name())}')
        print(f'{i1}num_args = {formula.num_args()}')
        print(f'{i1}params = {formula.params()}')
        print(f'{i1}is_not = {is_not(formula)}')
        print(f'{i1}uninterpreted = {formula.kind() == Z3_OP_UNINTERPRETED}')

        arg_list = [formula.arg(arg_ix) for arg_ix in range(formula.num_args())]
        print(f'{i1}args = {arg_list}')

        for arg_ix, arg in enumerate(arg_list):
            print(f'{i1}arg {arg_ix}')
            print_formula(arg, indent+2)

def export_smt2(solver, filename):
    with open(filename, 'w', encoding='ascii') as smt2_file:
        smt2_file.write(solver.to_smt2())

def export_cnf(formulation, solver, filename):
    # Create a goal and add constraints.
    goal = Goal()
    goal.add(solver.assertions())

    # Apply a set of tactics to convert to a purely CNF formulation.
    tactic = Then('lia2card', 'dt2bv', With('card2bv', 'pb.solver', 'totalizer'), 'bit-blast', 'tseitin-cnf')
    subgoal = tactic(goal)
    formulas = subgoal[0]

    # Collect all variables in all formulas.
    all_vars = set()
    num_false_formulas = 0
    for f in tqdm(formulas, desc="Variable Enumeration"):
        #print_formula(f)
        num_args = f.num_args()
        if num_args == 0:
            if is_false(f):
                print(f'Tactics reduced formula to False. Problem is UNSAT.')
                num_false_formulas = num_false_formulas + 1
            else:
                # Formula is a single positive literal.
                assert f.kind() == Z3_OP_UNINTERPRETED, f'Tactics left unexpected formula:\n{print_formula(f)}'
            all_vars.add(f.decl().name())
        elif num_args == 1:
            # Formula is a single negative literal.
            assert is_not(f), f'Tactics left unexpected formula:\n{print_formula(f)}'
            all_vars.add(f.arg(0).decl().name())
        else:
            # Formula is an Or of multiple literals.
            assert is_or(f), f'Tactics left unexpected formula:\n{print_formula(f)}'
            for arg_ix in range(num_args):
                arg = f.arg(arg_ix)
                num_subargs = arg.num_args()
                if num_subargs == 0:
                    # Positive literal.
                    assert arg.kind() == Z3_OP_UNINTERPRETED, f'Tactics left unexpected formula:\n{print_formula(arg)}'
                    all_vars.add(arg.decl().name())
                else:
                    # Negative literal
                    assert is_not(arg), f'Tactics left unexpected formula:\n{print_formula(arg)}'
                    all_vars.add(arg.arg(0).decl().name())

    # Split all the CNF vars into the placement/nonplacement groups.
    placement_vars = []
    nonplacement_vars = []
    for var in all_vars:
        if formulation.placement_var_by_name(var) is not None:
            placement_vars.append(var)
        else:
            nonplacement_vars.append(var)

    # Map sorted placement vars to integers starting at 1.
    # Nonplacement vars are numbered after the placement vars and don't need to be sorted.
    # Enumerating the variables this way allows import to work even if the tactic or finite-domain sort changes.
    var_to_ix_map = {var:ix for ix, var in enumerate(sorted(placement_vars) + nonplacement_vars, start=1)}

    with open(filename, 'w', encoding='ascii') as cnf_file:
        # Write cnf header
        cnf_file.write(f"c {' '.join(sys.argv)}\n")
        cnf_file.write(f"p cnf {len(var_to_ix_map)} {len(formulas) + num_false_formulas}\n")

        for f in tqdm(formulas, desc="Formula Generation"):
            literals = []
            num_args = f.num_args()
            if num_args == 0:
                if is_false(f):
                    cnf_file.write(f'{var_to_ix_map[f.decl().name()]} 0\n')
                    cnf_file.write(f'{-var_to_ix_map[f.decl().name()]} 0\n')
                    continue
                else:
                    # Formula is a single positive literal.
                    literals.append(var_to_ix_map[f.decl().name()])
            elif num_args == 1:
                # Formula is a single negative literal.
                literals.append(-var_to_ix_map[f.arg(0).decl().name()])
            else:
                for arg_ix in range(num_args):
                    arg = f.arg(arg_ix)
                    num_subargs = arg.num_args()
                    if num_subargs == 0:
                        # Positive literal.
                        literals.append(var_to_ix_map[arg.decl().name()])
                    else:
                        # Netagive literal.
                        literals.append(-var_to_ix_map[arg.arg(0).decl().name()])

            cnf_file.write(' '.join(map(str, literals)) + ' 0\n')

def import_certificate(formulation, filename):
    # Sorting all of the placement bvars in the formulation by name should match the numbering used in the CNF export.
    # One additional list element at the beginning is necessary because CNF starts numbering at 1, not 0.
    sorted_placement_bvars = [None] + sorted(formulation.placement_bvar_map.values(), key=lambda var: str(var))

    assertions = []

    with open(filename, 'r', encoding='ascii') as certificate:
        for line in certificate:
            if line.startswith("s UNSATISFIABLE"):
                assertions.append(False)
                print('Certificate indicates problem is UNSAT.')
            elif line.startswith("v "):
                var_list = line.rstrip().split()
                for assignment in map(int, var_list[1:]):
                    if 0 < assignment and assignment < len(sorted_placement_bvars):
                        assertions.append(sorted_placement_bvars[assignment])
                    elif 0 < -assignment and -assignment < len(sorted_placement_bvars):
                        assertions.append(Not(sorted_placement_bvars[-assignment]))

    return assertions

