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

    # Map import_vars from the formulation to integers starting at 1.
    var_to_ix_map = {str(var):ix for ix, var in enumerate(formulation.import_vars(), start=1)}

    # All other variables will be added dynamically during formula traversal.
    def get_lit(name):
        return var_to_ix_map.setdefault(name, len(var_to_ix_map) + 1)

    # Lines in the CNF output, as lists of integer lits, without the 0 terminators.
    cnf = []

    # Formula traversal can be slow.
    for f in tqdm(formulas, desc="CNF Export"):
        #print_formula(f)
        num_args = f.num_args()
        if num_args == 0:
            if is_false(f):
                print(f'Tactics reduced formula to False. Problem is UNSAT.')
                lit = get_lit(f.decl().name())
                cnf.extend([[lit], [-lit]])
            else:
                # Formula is a single positive literal.
                assert f.kind() == Z3_OP_UNINTERPRETED, f'Tactics left unexpected formula:\n{print_formula(f)}'
                cnf.append([get_lit(f.decl().name())])
        elif num_args == 1:
            # Formula is a single negative literal.
            assert is_not(f), f'Tactics left unexpected formula:\n{print_formula(f)}'
            cnf.append([-get_lit(f.arg(0).decl().name())])
        else:
            # Formula is an Or of multiple literals.
            assert is_or(f), f'Tactics left unexpected formula:\n{print_formula(f)}'
            literals = []
            for arg_ix in range(num_args):
                arg = f.arg(arg_ix)
                num_subargs = arg.num_args()
                if num_subargs == 0:
                    # Positive literal.
                    assert arg.kind() == Z3_OP_UNINTERPRETED, f'Tactics left unexpected formula:\n{print_formula(arg)}'
                    literals.append(get_lit(arg.decl().name()))
                else:
                    # Negative literal
                    assert is_not(arg), f'Tactics left unexpected formula:\n{print_formula(arg)}'
                    literals.append(-get_lit(arg.arg(0).decl().name()))
            cnf.append(literals)

    # Write out the CNF file.
    with open(filename, 'w', encoding='ascii') as cnf_file:
        # Write cnf header
        cnf_file.write(f"c {' '.join(sys.argv)}\n")
        cnf_file.write(f"p cnf {len(var_to_ix_map)} {len(cnf)}\n")
        for f in cnf:
            cnf_file.write(' '.join(map(str, f)) + ' 0\n')

def import_certificate(formulation, filename):
    # One additional list element at the beginning is necessary because CNF starts numbering at 1, not 0.
    import_vars = [None] + formulation.import_vars()

    assertions = []

    with open(filename, 'r', encoding='ascii') as certificate:
        for line in certificate:
            if line.startswith("s UNSATISFIABLE"):
                assertions.append(False)
                print('Certificate indicates problem is UNSAT.')
            elif line.startswith("v "):
                var_list = line.rstrip().split()
                for assignment in map(int, var_list[1:]):
                    if 0 < assignment and assignment < len(import_vars):
                        assertions.append(import_vars[assignment])
                    elif 0 < -assignment and -assignment < len(import_vars):
                        assertions.append(Not(import_vars[-assignment]))

    return assertions

