/-
Copyright (c) 2026 Pjotr Buys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Powerset
import Mathlib.Topology.MetricSpace.Basic

/-!
# Reliability polynomial definitions

This file defines the reliability polynomial and split-reliability polynomial of a simple graph,
as well as the set of real reliability roots of connected simple graphs.

## Main definitions

* `SimpleGraph.reliabilityFun G q`: the reliability polynomial of `G` evaluated at `q ∈ ℝ`.
* `SimpleGraph.splitRelFun G u v q`: the split-reliability polynomial of `G` w.r.t. vertices
  `u, v`, evaluated at `q ∈ ℝ`.
* `reliabilityRootSet`: the set of real numbers that are roots of the reliability polynomial of
  some connected simple graph.
-/

open SimpleGraph Finset

attribute [local instance] Classical.propDecidable

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The reliability polynomial of a simple graph `G`, evaluated at `q`.

`Rel(G; q) = ∑_{A ⊆ E(G)} [G[A] connected] · (1-q)^|A| · q^(|E(G)|-|A|)`

This models the probability that `G` remains connected when each edge independently
fails with probability `q`. -/
def SimpleGraph.reliabilityFun (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) : ℝ :=
  ∑ A ∈ G.edgeFinset.powerset,
    if (SimpleGraph.fromEdgeSet (↑A : Set (Sym2 V))).Connected then
      (1 - q) ^ A.card * q ^ (G.edgeFinset.card - A.card)
    else 0

/-- The split-reliability polynomial of a simple graph `G` with respect to vertices `u` and `v`,
evaluated at `q`.

`splitRel_{u,v}(G; q) = ∑_{A ⊆ E(G)} [u,v separated, 2 components] · (1-q)^|A| · q^(|E|-|A|)`

This is the probability that in the random subgraph (each edge failing independently with
probability `q`), u and v end up in different components and every vertex is reachable
from either u or v. -/
def SimpleGraph.splitRelFun (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (q : ℝ) : ℝ :=
  let H (A : Finset (Sym2 V)) := SimpleGraph.fromEdgeSet (↑A : Set (Sym2 V))
  ∑ A ∈ G.edgeFinset.powerset,
    if ¬(H A).Reachable u v ∧ ∀ w, (H A).Reachable u w ∨ (H A).Reachable v w then
      (1 - q) ^ A.card * q ^ (G.edgeFinset.card - A.card)
    else 0

/-- The set of real reliability roots of connected simple graphs. -/
def reliabilityRootSet : Set ℝ :=
  { q : ℝ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      G.Connected ∧ G.reliabilityFun q = 0 }

end
