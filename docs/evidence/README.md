# Verification

Run `python3 scripts/check.py` from the repository root to build the library and vendored
modules, compile the four consumer example files, and check the transitive axioms and
documentation. The toolchain and dependency revisions are pinned in the repository.

The [GitHub build and audit](https://github.com/igor-kortchemski/random-trees-lean/actions/runs/42603152635)
for the sources released in `v0.1.0` checked 12,925 constants across 901 modules.
The only axioms used were `propext`, `Classical.choice`, and `Quot.sound`.
The documentation check reported no errors. A separate Lake project fetched the library
as a Git dependency and compiled examples using the finite-tree API and the BGW law.

See the [independent kernel replay](KERNEL_REPLAY.md) for the additional checks on those
sources and the [coverage index](../../CLASSICAL_THEORY_COVERAGE.md) for statement scope.
