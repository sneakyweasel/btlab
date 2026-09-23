"""Registry of Juggler and Collatz applications."""
from research.open_problems.definition import ProblemDefinition, STATUSES

__all__ = ['ProblemDefinition', 'STATUSES', 'get_problem', 'list_problems']


def list_problems() -> tuple[ProblemDefinition, ...]:
    from research.juggler_sequence.problem import PROBLEM as JUGGLER
    from research.collatz.problem import PROBLEM as COLLATZ
    from research.collatz_finite_descent.problem import PROBLEM as FINITE_DESCENT
    from research.syracuse.problem import PROBLEM as SYRACUSE
    return JUGGLER, COLLATZ, FINITE_DESCENT, SYRACUSE


def get_problem(problem_id: str) -> ProblemDefinition:
    for problem in list_problems():
        if problem.id == problem_id:
            return problem
    raise KeyError(problem_id)
