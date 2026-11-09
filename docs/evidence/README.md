# Statement evidence

This folder contains the public statement contracts and verification summaries behind
[CLASSICAL_THEORY_COVERAGE.md](../../CLASSICAL_THEORY_COVERAGE.md). From a checkout of the
library, `python3 scripts/check.py` rebuilds the targets, compiles the examples and audits
the transitive axioms. The format-4 freeze records belong to the local campaign archive.
The public index gives their hashes and provenance.

- [contracts/](contracts/) holds the audited **contracts** of the 2026 campaigns (123 files).
  A contract is a Lean file that states the public definitions and theorems of one proof node,
  with `sorry` in place of every proof, and a module docstring giving the source statement,
  the truth check and the proof plan. Each contract was audited against its informal source
  before any proof was written (by an independent Sonnet review, and for the main interfaces
  also by a GPT review); the proved library declarations must then match it exactly.
  These files are **not** part of the library: they are outside the `BGW` build target, their
  `sorry` holes are intentional, and their imports refer to the library state at the time of the
  contract. A few contracts were later superseded, parked or merged into another node; the
  coverage index and the [formalization report](../../FORMALIZATION_REPORT.md) say which
  declarations were delivered.
- [FREEZE_RECORDS.md](FREEZE_RECORDS.md) lists the active freeze records (all in format 4 since 9
  November 2026) that fix the statements of
  the sealed nodes, with the commit at which each was recorded and the SHA-256 of the record, and the
  successor records created when a frozen statement was changed on purpose (the predecessors are kept).

Most record names match a contract name. The exceptions name the classical item in the record:
`CT8_K08_C35_VervaatIto` (contract `CT8_K08_VervaatItoIdentity`), `CT8_K13_C27_ForestTriple`
(`CT8_K13_ForestTriple`), `CT8_K13b_C27_VectorPath` (`CT8_K13b_ForestTripleVector`),
`CT8_K14_C28_TailPair` (`CT8_K14_TailPair`), `CT8_K16_C29_ExactContour` (`CT8_K16_ContourC29`),
`CT8_K17_C26_BrownianHeight` (`CT8_K17_BrownianHeight`), `CT8_K19_C30_FiniteVarianceContour`
(`CT8_K19_FiniteVarianceC30`), `CT10_PolishTightness` (`CT10_PolishD`), `CT9_C37_C38_Adapters`
(`CT9_C37_GHCompat` and the adapters it reuses) and `Port_StableAttraction` (a verbatim port of
the author's arXiv:1110.2163 stable-attraction modules, checked by a diff audit instead of a
contract).

[KERNEL_REPLAY.md](KERNEL_REPLAY.md) records an independent kernel replay of the compiled library
(9 November 2026): Lean's kernel on all modules, and four further checkers on the full export.

The contracts keep the names in force when they were audited. Declarations renamed later are listed
in [docs/renames/](../renames/), and the corresponding freeze records have linked successors.
