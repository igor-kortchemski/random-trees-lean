# Independent kernel replay

A local diagnostic, run on 9 November 2026 on macOS (4 cores, 24 GB). It is **not** the official Lake
Comparator or a Palomar verification. It rechecks the compiled library with several kernels that
are independent of the elaborator that produced the proofs.

**Snapshot.** The replay used the Lean sources in `v0.1.0`, with Lean 4.35.0
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

| Check | What it does | Result |
| --- | --- | --- |
| `leanchecker BGW` | replays every compiled module of the library (870) through Lean's kernel | **pass** (5 h 31 min) |
| `leanexport BGW` | exports the library and its whole import closure | 416,202 declarations, 2.83 GB, SHA-256 `6389f9e42723a53db7e690bd03ca4513886eec568862e642d2515f99335d32c4` |
| `leanchecker-paranoid --from-export` | Lean's kernel on the export, paranoid mode | **pass** (26 min) |
| `con-leche --verified` | independent checker (Lean) | **accepted 416,202 declarations** (7 min) |
| `con-ron --verified` | independent checker (Rust) | **accepted 416,202 declarations** (3 min) |
| `lean4lean --import` | the Lean kernel reimplemented in Lean | **checked 416,199 declarations**, pass (27 min) |
| `nanoda_bin` | independent kernel (Rust) | **not completed**: with the three standard axioms it stops at the declaration of `sorryAx` (see below); with `sorryAx` permitted it was killed for lack of memory (peak footprint 30.5 GB on a 24 GB machine, after 100 min on one thread; a 4-thread run was killed after 14 min). No error was reported before the kill. |

**Axioms.** The export declares exactly four axioms: `propext`, `Quot.sound`, `Classical.choice` and
`sorryAx`. `sorryAx` is declared by Lean's core in every environment; a scan of the whole export found
**no reference** to it among the 700,129 constant nodes of the 416,202 declarations, so no declaration
of the library or of its Mathlib closure uses it. This agrees with the repository's transitive axiom
audit (`scripts/check.py`: only `propext`, `Classical.choice`, `Quot.sound`). `nanoda`, run with the
three standard axioms only, stopped at the declaration of `sorryAx` (its policy rejects any declared
axiom outside the list); it was then run with `sorryAx` permitted as a declaration, and ran out of memory.

**Summary.** The library's 870 modules pass Lean's kernel replay, and the whole export (the library
and its Mathlib closure) is accepted by four further checkers, three of them independent
implementations (`con-leche`, `con-ron`, `lean4lean`). `nanoda` needs more memory than this machine
has for an export of this size; splitting the export into smaller closures, or a larger machine,
would be needed to complete it.
