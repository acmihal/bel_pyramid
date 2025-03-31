import sys
import time
from z3 import Goal, is_not, Not, Tactic, Then, With, Z3_OP_UNINTERPRETED

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

    # Apply a set of tactics to convert a purely CNF formulation.
    print()
    print(f'Applying tactics to convert formulation to CNF.', flush=True)
    tactic_start_time = time.process_time()
    tactic = Then('lia2card', 'dt2bv', 'bit-blast', 'card2bv', 'tseitin-cnf')
    subgoal = tactic(goal)
    formulas = subgoal[0]
    tactic_end_time = time.process_time()
    tactic_elapsed_time = tactic_end_time - tactic_start_time
    print(f'Tactics generated {len(formulas)} formulas in {tactic_elapsed_time:.2f} seconds.', flush=True)

    # Collect all variables in all formulas.
    print()
    print(f'Starting CNF variable enumeration.', flush=True)
    var_enum_start_time = time.process_time()
    all_vars = set()
    for f in formulas:
        #print_formula(f)
        num_args = f.num_args()
        if num_args == 0:
            # Formula is a single positive literal.
            all_vars.add(f.decl().name())
        elif num_args == 1:
            # Formula is a single negative literal.
            all_vars.add(f.arg(0).decl().name())
        else:
            # Formula is an Or of multiple literals.
            for arg_ix in range(num_args):
                arg = f.arg(arg_ix)
                num_subargs = arg.num_args()
                if num_subargs == 0:
                    # Positive literal.
                    all_vars.add(arg.decl().name())
                else:
                    # Negative literal
                    all_vars.add(arg.arg(0).decl().name())
    var_enum_end_time = time.process_time()
    var_enum_elapsed_time = var_enum_end_time - var_enum_start_time
    print(f'CNF variable enumeration finished in {var_enum_elapsed_time:.2f} seconds.', flush=True)

    # Split all the CNF vars into the placement/nonplacement groups.
    print()
    print(f'Splitting placement/non-placement CNF variables.', flush=True)
    var_split_start_time = time.process_time()
    placement_vars = []
    nonplacement_vars = []
    for var in all_vars:
        if formulation.placement_var_by_name(var) is not None:
            placement_vars.append(var)
        else:
            nonplacement_vars.append(var)
    var_split_end_time = time.process_time()
    var_split_elapsed_time = var_split_end_time - var_split_start_time
    print(f'CNF variable splitting finished in {var_split_elapsed_time:.2f} seconds.', flush=True)

    print()
    print(f'Assigning indices to CNF variables.', flush=True)
    index_assign_start_time = time.process_time()

    # Map placement vars to integers starting at 1.
    # Nonplacement vars are numbered after the placement vars.
    # Enumerating the variables this way allows import to work even if the tactic or finite-domain sort changes.
    var_to_ix_map = {var:ix for ix, var in enumerate(sorted(placement_vars) + nonplacement_vars, start=1)}

    index_assign_end_time = time.process_time()
    index_assign_elapsed_time = index_assign_end_time - index_assign_start_time
    print(f'CNF variable index assignment finished in {index_assign_elapsed_time:.2f} seconds.', flush=True)

    print()
    print(f'Writing CNF output file.', flush=True)
    cnf_write_start_time = time.process_time()

    with open(filename, 'w', encoding='ascii') as cnf_file:
        # Write cnf header
        cnf_file.write(f"c {' '.join(sys.argv)}\n")
        cnf_file.write(f"p cnf {len(var_to_ix_map)} {len(formulas)}\n")

        for f in formulas:
            literals = []
            num_args = f.num_args()
            if num_args == 0:
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

    cnf_write_end_time = time.process_time()
    cnf_write_elapsed_time = cnf_write_end_time - cnf_write_start_time
    print(f'CNF file write finished in {cnf_write_elapsed_time:.2f} seconds.', flush=True)

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

