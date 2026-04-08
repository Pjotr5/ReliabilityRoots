/-
Copyright (c) 2026 Pjotr Buys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys
-/
import ReliabilityRoots.ReliabilityProof

/-!
# Real reliability roots of simple graphs are dense in [-1, 0]

## Definition

The **reliability polynomial** of a simple graph `G` evaluated at failure probability `q` is

  `Rel(G; q) = ∑_{A ⊆ E(G)} [G[A] connected] · (1-q)^|A| · q^(|E(G)|-|A|)`.

## Main result

**Theorem** (`reliabilityRoots_dense_in_Icc`):
Every point of `[-1, 0]` is a limit of real numbers `q` at which some connected simple
graph has `Rel(G; q) = 0`.

The proof constructs, for each `q₀ ∈ (-1, 0)` and `ε > 0`, a connected simple graph
whose reliability polynomial vanishes within `ε` of `q₀`, using the cycle-substitution
gadget `C_n[K_m]` and the intermediate value theorem. See `ReliabilityRoots.ReliabilityProof`
for the full proof.

-/

open Set SimpleGraph

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Main Theorem**: The closed interval `[-1, 0]` is contained in the closure of the set of
real reliability roots of connected simple graphs. -/
theorem reliabilityRoots_dense_in_Icc :
    Icc (-1 : ℝ) 0 ⊆ closure {q : ℝ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V), G.Connected ∧ G.reliabilityFun q = 0} :=
  icc_subset_closure_reliabilityRootSet

end
