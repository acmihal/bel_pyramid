import argparse
from export import export_cnf, export_smt2, import_certificate
from formulation import Formulation
from strategies import StrategyMap
import time
from z3 import Solver, Tactic, sat

UsableTactics = ['qffd', 'qflia', 'z3-default']
FiniteDomains = ['int', 'enum']

def main():
    # Parse arguments.
    parser = argparse.ArgumentParser(description="Solve Bel's Pyramid for N levels")
    parser.add_argument("N", type=int, help="number of levels in the pyramid")
    parser.add_argument("--strategy", choices=StrategyMap.keys(), action="append", help="symmetry breaking strategy")
    parser.add_argument("--smt2", type=str, help="export formulation to smt2 file")
    parser.add_argument("--cnf", type=str, help="export formulation to cnf file")
    parser.add_argument("--certificate", type=str, help="import certificate from file")
    parser.add_argument("--skip-solver", action="store_true", help="exit before solving the formulation")
    parser.add_argument("--tactic", choices=UsableTactics, default=UsableTactics[0], help="solver tactic")
    parser.add_argument("--finite-domain", choices=FiniteDomains, default=FiniteDomains[0], help="finite domain formulation")
    args = parser.parse_args()

    # Validate arguments.
    assert args.N >= 1, 'Number of levels must be >= 1.'

    print(f"Solving Bel's Pyramid for {args.N} levels.", flush=True)

    # Initialize the formulation.
    f = Formulation(args.N, use_enum=(args.finite_domain=="enum"))

    print()
    f.print_parameters()

    print()
    f.print_variable_stats()

    # Construct the Z3 solver.
    if args.tactic == 'z3-default':
        solver = Solver()
    else:
        solver = Tactic(args.tactic).solver()

    # Add constraints from the formulation to the solver.
    constraints_start_time = time.process_time()
    solver.add(f.get_constraints())
    constraints_end_time = time.process_time()
    constraints_elapsed_time = constraints_end_time - constraints_start_time

    print()
    f.print_constraint_stats()

    # Apply strategies in order.
    if args.strategy is not None:
        print()
        strategy_functions = [StrategyMap[strategy] for strategy in args.strategy]
        for strategy in args.strategy:
            constraints = StrategyMap[strategy](f)
            solver.add(constraints)
            print(f'Strategy {strategy} applied {len(constraints)} constraint(s).', flush=True)

    print()
    print(f'Constraint formulation built in {constraints_elapsed_time:.2f} seconds.', flush=True)
 
    if args.smt2 is not None:
        print()
        print(f'Exporting formulation to smt2 file "{args.smt2}".', flush=True)
        export_smt2(solver, args.smt2)

    if args.cnf is not None:
        print()
        print(f'Exporting formulation to cnf file "{args.cnf}".', flush=True)
        cnf_start_time = time.process_time()
        export_cnf(f, solver, args.cnf)
        cnf_end_time = time.process_time()
        cnf_elapsed_time = cnf_end_time - cnf_start_time
        print(f'CNF exported in {cnf_elapsed_time:.2f} seconds.', flush=True)

    if args.certificate is not None:
        print()
        print(f'Importing certificate from file "{args.certificate}".', flush=True)
        certificate_assertions = import_certificate(f, args.certificate)
        solver.add(certificate_assertions)
        print(f'Certificate applied {len(certificate_assertions)} assertion(s).', flush=True)

    if args.skip_solver:
        print()
        print(f'Skipping the solver.')
        return

    print()
    print(f'Starting solver with tactic "{args.tactic}".', flush=True)
    solver_start_time = time.process_time()
    result = solver.check()
    solver_end_time = time.process_time()
    solver_elapsed_time = solver_end_time - solver_start_time
    print(f'Solver finished in {solver_elapsed_time:.2f} seconds.', flush=True)

    if result == sat:
        # The pyramid is solvable for num_levels.
        model = solver.model()

        print()
        f.print_model(model)

        correct = f.validate_model(model)
        assert f.validate_model(model), "Solution validation failed."

    else:
        # The pyramid is not solvable for num_levels.
        print(f'No solution exists for {args.N} levels.')

