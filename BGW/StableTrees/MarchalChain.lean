/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalChainTwo

/-!
# Finite Marchal growth chains

This entry module exports the finite labelled-tree state space, grafting and
its quotient transition, and the binary Rémy specialization at `α = 2`.

References: P. Marchal, *A note on the fragmentation of a stable tree*, DMTCS Proc. (2008);
N. Curien and B. Haas, *The stable trees are nested*, arXiv:1207.5418, §§1.1, 1.3. The exact law
formula and the uniform binary law at `α = 2` are proved separately.
-/

@[expose] public section
