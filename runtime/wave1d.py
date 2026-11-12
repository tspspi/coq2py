#!/usr/bin/env python3
"""wave1d.py -- the external runtime for coq2py's extracted 1D wave
simulator.

This is deliberately *not* part of the proven Gallina pipeline -- per
GOAL.md's non-goals ("a numpy subset is a plausible future extension but
is explicitly deferred") and docs/roadmap.md's discretization entry, array
allocation, boundary conditions, and the time-stepping loop are not
(yet) formalized in expr/pyexpr. This script is that missing plumbing,
hand-written and unproven, in exactly the same trust category as
ocaml/driver/main.ml (the CLI's file-I/O glue) or PyPrint.v's
pretty-printer: peripheral, not semantics-affecting for the one piece
that *is* proven.

That one proven piece is `generated/leapfrog_update.py`'s
`leapfrog_update` function -- not hand-written here, but produced by
`make wave_sim` piping examples/physics/Discretize.v's
`leapfrog_update_expr` (JSON-encoded) through the real coq2py CLI
(ocaml/driver/main.exe), the same binary extracted from the proven
Gallina pipeline. This script imports and calls that exact generated
function for every grid update; it does not re-derive the update formula
independently. `leapfrog_exact_for_cubic_profile` (Discretize.v) is the
theorem backing that formula's correctness (see its comment for exactly
what it proves and does not prove).

The one trick that makes an unmodified, scalar-looking extracted
function run at numpy speed over a whole grid: `leapfrog_update`'s body
is pure `+`/`-`/`*` arithmetic (see its generated source) with no
Python-`float`-specific operations, so calling it with numpy array slices
instead of scalars "just works" via Python's normal operator overloading
-- numpy's `__add__`/`__sub__`/`__mul__` make every operation apply
element-wise across the whole interior of the grid in one call. No
separate "vectorized version" of the formula was written.

Known, deliberately-not-formally-justified simplification: the standard
leapfrog scheme needs a value one time step *before* t=0 to take its
first step; for a "starts at rest" (zero initial velocity) initial
condition, this script approximates that with u(-dt) := u(0), which is
only first-order accurate for that one single step (a standard,
textbook simplification, not specific to this project) -- every
subsequent step uses the real, second-order-consistent scheme."""

import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "generated"))
from leapfrog_update import leapfrog_update  # noqa: E402  (generated, see module docstring)


def run_simulation(nx=400, nt=1600, c=1.0, dx=0.01, cfl=0.5, x0=1.0, sigma=0.05):
    """Simulate the 1D scalar wave equation u_tt = c^2 u_xx on [0, (nx-1)*dx]
    with Dirichlet (u=0) boundaries, starting from a Gaussian pulse at rest.

    Returns (x, dt, snapshots) where snapshots is a list of (t, u) pairs."""
    dt = cfl * dx / c
    r = (c * dt / dx) ** 2  # courant_sq c dt dx, from Discretize.v

    x = np.linspace(0.0, (nx - 1) * dx, nx)
    u_curr = np.exp(-((x - x0) ** 2) / (2.0 * sigma * sigma))
    u_prev = u_curr.copy()  # zero initial velocity (see module docstring)

    snapshots = [(0.0, u_curr.copy())]
    snapshot_every = max(1, nt // 8)

    for step in range(1, nt + 1):
        u_next = np.empty_like(u_curr)
        u_next[1:-1] = leapfrog_update(
            r, u_prev[1:-1], u_curr[:-2], u_curr[1:-1], u_curr[2:]
        )
        u_next[0] = 0.0
        u_next[-1] = 0.0
        u_prev, u_curr = u_curr, u_next
        if step % snapshot_every == 0:
            snapshots.append((step * dt, u_curr.copy()))

    return x, dt, snapshots


def main():
    x, dt, snapshots = run_simulation()

    energy0 = float(np.sum(snapshots[0][1] ** 2))
    energy_last = float(np.sum(snapshots[-1][1] ** 2))
    print(f"grid points: {len(x)}, dt: {dt:.6g}, snapshots: {len(snapshots)}")
    print(f"sum(u^2) at t=0: {energy0:.6g}, at t={snapshots[-1][0]:.4g}: {energy_last:.6g}")
    print(
        "(a genuine wave equation solution should split the initial pulse "
        "into two counter-propagating humps of about half the original "
        "peak height each, reflecting off the fixed Dirichlet boundaries -- "
        "see wave1d.png)"
    )

    try:
        import matplotlib

        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        fig, ax = plt.subplots()
        for t, u in snapshots:
            ax.plot(x, u, label=f"t={t:.3f}")
        ax.set_xlabel("x")
        ax.set_ylabel("u(x, t)")
        ax.set_title("1D wave equation -- coq2py-extracted leapfrog_update")
        ax.legend(fontsize="small", ncol=2)
        outfile = os.path.join(os.path.dirname(__file__), "wave1d.png")
        fig.savefig(outfile, dpi=120)
        print(f"wrote {outfile}")
    except ImportError:
        print("matplotlib not available; skipping plot")


if __name__ == "__main__":
    main()
