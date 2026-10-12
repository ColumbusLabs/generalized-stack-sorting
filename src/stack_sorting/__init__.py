"""Research infrastructure for the generalized (2,2)-stack.

Exact finite oracles and an direct structural derivation.
"""

__version__ = "0.1.0"
MODEL_DESCRIPTION = (
    "One stack, top first: push into slot 0 or 1; pop from slot 0 or 1. "
    "An empty stack permits push into slot 0 only. "
    "Read the input permutation left to right and output 1, 2, ..., n."
)


def validate_permutation(values):
    """Return a tuple; reject anything other than a permutation of 1..n.

    The empty permutation is valid. Booleans and non-integers are rejected.
    """
    values = tuple(values)
    if any(type(value) is not int for value in values):
        raise ValueError("expected integers")
    if sorted(values) != list(range(1, len(values) + 1)):
        raise ValueError("expected a permutation of 1..n")
    return values
