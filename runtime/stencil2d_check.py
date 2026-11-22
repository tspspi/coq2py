#!/usr/bin/env python3
"""stencil2d_check.py -- run the extracted rank-2 5-point stencil
(examples/physics/Discretize.v's `laplace5_step_expr`, produced by
`make stencil2d_check` through the real coq2py CLI) on a random 6x7
grid of doubles and compare it bit for bit against the numpy one-liner
it was written to mirror.

The extracted function takes and returns a tuple of row tuples (the
nested rank-1 representation Lang.v uses for rank 2); the only thing
this script adds is the conversion to and from numpy and the comparison.
Exact equality is the expectation, not a tolerance: both sides perform
the same IEEE-754 double operations in the same order, which
`laplace5_symbolic_3x3` states symbolically for a 3x3 grid."""

import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "generated"))
from laplace5_step import laplace5_step  # noqa: E402  (generated, see module docstring)


def reference(r, U):
    out = np.zeros_like(U)
    out[1:-1, 1:-1] = U[1:-1, 1:-1] + r * (
        ((U[:-2, 1:-1] + U[2:, 1:-1]) + (U[1:-1, :-2] + U[1:-1, 2:])) - 4.0 * U[1:-1, 1:-1]
    )
    return out


def main():
    rng = np.random.default_rng(0)
    U = rng.standard_normal((6, 7))
    r = 0.3
    T = tuple(tuple(float(v) for v in row) for row in U)
    got = np.array(laplace5_step(r, T))
    ref = reference(r, U)
    same = got.shape == ref.shape and np.array_equal(got, ref)
    print(f"grid shape: {U.shape}")
    print(f"extracted rank-2 stencil vs numpy reference: "
          f"{'bit-identical' if same else 'DIFFERENT'} "
          f"(max |diff| = {float(np.max(np.abs(got - ref))) if got.shape == ref.shape else float('nan'):.3g})")
    if not same:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
