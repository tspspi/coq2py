#!/usr/bin/env python3
"""wave1d_vec.py -- the same 1D wave simulation as wave1d.py, driven by
the *whole-grid* step extracted from examples/physics/Discretize.v's
`one_pass_vec_expr`, and checked bit for bit against wave1d.py's own
numpy path.

What moved inside the proven fragment compared to wave1d.py: there, only
the per-point update formula (`leapfrog_update`) was extracted, and the
slicing (`u_curr[:-2]`, `u_curr[1:-1]`, `u_curr[2:]`, `u_prev[1:-1]`),
the broadcasting of the scalar `r` against those slices, the boundary
handling (`u_next[0] = u_next[-1] = 0`) and the allocation of the next
array were all hand-written numpy glue in this directory. Here every one
of those is part of `generated/one_pass_vec.py`'s `one_pass_vec`, which
`make wave_sim_vec` produces by piping `one_pass_vec_expr`'s JSON
encoding through the real coq2py CLI -- so what this script still
contributes unproven is only the time loop (`prev, curr = curr, next`),
the initial condition, and the comparison/plotting at the end.

The extracted function works on Python tuples, not numpy arrays (that is
what Lang.v's `VArray` renders as, see PyPrint.v), so this runs the grid
as a tuple of floats: slower than numpy, but every arithmetic operation
it performs is the same IEEE-754 double operation in the same order as
wave1d.py's numpy path (Discretize.v's `one_pass_vec_symbolic_7point`
is the symbolic form of that claim for a 7-point grid), which is why the
final comparison below demands *exact* equality, not a tolerance."""

import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "generated"))
from one_pass_vec import one_pass_vec  # noqa: E402  (generated, see module docstring)

import wave1d  # noqa: E402  (the numpy reference path, same directory)


def run_simulation_vec(nx=400, nt=1600, c=1.0, dx=0.01, cfl=0.5, x0=1.0, sigma=0.05):
    """Same parameters, initial condition and conventions as
    wave1d.run_simulation; returns (x, dt, u_final) with u_final a tuple."""
    dt = cfl * dx / c
    wave1d.validate_parameters(c, dx, dt)
    r = (c * dt / dx) ** 2

    x = np.linspace(0.0, (nx - 1) * dx, nx)
    u0 = np.exp(-((x - x0) ** 2) / (2.0 * sigma * sigma))
    u_curr = tuple(float(v) for v in u0)
    u_prev = u_curr

    for _ in range(nt):
        u_prev, u_curr = u_curr, one_pass_vec(r, u_curr, u_prev)
    return x, dt, u_curr


def main():
    nx, nt = 400, 1600
    x, dt, u_vec = run_simulation_vec(nx=nx, nt=nt)
    _, _, snapshots = wave1d.run_simulation(nx=nx, nt=nt)
    u_np = snapshots[-1][1]
    assert len(snapshots) > 0 and snapshots[-1][0] == nt * dt

    same = np.array_equal(np.array(u_vec), u_np)
    print(f"grid points: {nx}, time steps: {nt}")
    print(f"extracted whole-grid step vs numpy per-point path, final grid: "
          f"{'bit-identical' if same else 'DIFFERENT'} "
          f"(max |diff| = {float(np.max(np.abs(np.array(u_vec) - u_np))):.3g})")
    if not same:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
