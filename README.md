# ReliabilityRoots

A Lean 4 formalization (using [Mathlib](https://github.com/leanprover-community/mathlib4)) of the following result.

**Theorem.** *The real roots of reliability polynomials of connected simple graphs are dense in $[-1, 0]$.*

This is a formalization of item 2 of the main theorem of the paper:

> P. Buys, *Density of reliability roots of simple graphs in the unit disk*, (2026).

## Reliability polynomial

Let $G = (V, E)$ be a connected graph. If each edge fails independently with probability $q$, the probability that the remaining edges still form a connected spanning subgraph is the **reliability polynomial**

$$\textrm{Rel}(G;\, q) \;=\; \sum_{\substack{S \subseteq E \\\ (V,S)\ \text{connected}}} (1-q)^{|S|}\, q^{\,|E|-|S|}.$$

## Formal statement

The main theorem is located in [`ReliabilityRoots/MainTheorem.lean`](ReliabilityRoots/MainTheorem.lean):

```lean
theorem reliabilityRoots_dense_in_Icc :
    Icc (-1 : ℝ) 0 ⊆ closure {q : ℝ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V), G.Connected ∧ G.reliabilityFun q = 0}
```


## Authorship

The definition of `reliabilityFun` and the main theorem statement were carefully checked by the author. The rest of the formalization was auto-formalized with [Claude Code](https://claude.ai/code).

## File structure

| File | Contents |
|------|----------|
| `Defs.lean` | Definitions of `reliabilityFun`, `splitRelFun`, and `reliabilityRootSet` |
| `BlockAlgebra.lean` | Algebraic identity for cycle and path compositions of blocks |
| `CycleGadget.lean` | Cycle-substitution graph $C_n[H]$: construction, connectivity, and reliability formula |
| `LimCompleteGraph.lean` | Asymptotic limits: $\textrm{Rel}(K_n; q) \to 1$ and $\textrm{splitRel}(K_n; q)/q^{n-1} \to 2$ for $|q| < 1$ |
| `ReliabilityProof.lean` | Core density argument via IVT applied to $\textrm{Rel}(K_m; q) + n \cdot \textrm{splitRel}(K_m; q)$ |
| `MainTheorem.lean` | Clean theorem statement |

## TODO

- Formalize item 1 of the main theorem: complex reliability roots of simple graphs are dense in the closed unit disk. The main obstacle is formalizing Rouch&eacute;'s theorem.

## Building

Requires Lean 4 (v4.28.0) and Mathlib (v4.28.0). To build:

```
lake exe cache get   # download precompiled Mathlib
lake build
```
