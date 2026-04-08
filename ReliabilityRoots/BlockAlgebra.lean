/-
Copyright (c) 2026 Pjotr Buys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys
-/
import Mathlib.Topology.MetricSpace.Basic

/-!
# Block algebra for series and cycle compositions

Both the cycle-substitution (Lemma 3.1) and path-substitution (Lemma 3.2) gadgets
are built by composing "blocks" in series. Each block contributes a reliability `R`
(probability of connecting its terminals) and a split-reliability `S` (probability
of separating its terminals into exactly two components covering all vertices).

This file contains the pure algebraic identities for such compositions.

## Main definitions

* `cycleBlockRel R S n`: reliability of a cycle of `n` identical blocks
* `pathBlockSplit R₁ S₁ a R₂ S₂ b`: split-reliability of a path with `a` blocks
  of type 1 and `b` blocks of type 2

## Key identities

* A cycle of `n` blocks is connected iff at most one block splits:
  `cycleBlockRel R S n = R^(n-1) * (R + n * S)`
* A path of `a + b` mixed blocks splits iff exactly one block splits:
  `pathBlockSplit R₁ S₁ a R₂ S₂ b = a * S₁ * R₁^(a-1) * R₂^b + b * S₂ * R₁^a * R₂^(b-1)`
-/

open Finset

/-! ### Cycle composition -/

/-- Reliability of a cycle of `n` identical blocks, each with reliability `R` and
split-reliability `S`. The cycle is connected iff all blocks connect OR exactly
one block splits while the rest connect. -/
noncomputable def cycleBlockRel (R S : ℝ) (n : ℕ) : ℝ :=
  R ^ n + ↑n * S * R ^ (n - 1)

theorem cycleBlockRel_eq (R S : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    cycleBlockRel R S n = R ^ (n - 1) * (R + ↑n * S) := by
  unfold cycleBlockRel
  have : R ^ n = R ^ (n - 1) * R := by
    rw [← pow_succ]; congr 1; omega
  rw [this]; ring

/-! ### Path composition (split-reliability) -/

/-- Split-reliability of a path of `a` blocks of type 1 (reliability `R₁`, split `S₁`)
and `b` blocks of type 2 (reliability `R₂`, split `S₂`). The path splits its endpoints
iff exactly one of the `a + b` blocks splits while all others connect. -/
noncomputable def pathBlockSplit (R₁ S₁ : ℝ) (a : ℕ) (R₂ S₂ : ℝ) (b : ℕ) : ℝ :=
  ↑a * S₁ * R₁ ^ (a - 1) * R₂ ^ b + ↑b * S₂ * R₁ ^ a * R₂ ^ (b - 1)

/-- The path-substitution split-reliability can be rewritten using
`γ = -(1-q) * S / (q * R)` when `S₁ = q`, `R₁ = 1-q`, `S₂ = S`, `R₂ = R`,
and `γ(q₀) = a/b`. -/
theorem pathBlockSplit_eq_gamma (R S : ℝ) (q : ℝ) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hR : R ≠ 0) (hq : q ≠ 0)
    (gamma_q₀ : ℝ) (hgamma : gamma_q₀ = ↑a / ↑b) :
    pathBlockSplit (1 - q) q a R S b =
      ↑b * R ^ b * (1 - q) ^ (a - 1) * q *
      (gamma_q₀ - (-(1 - q) * S / (q * R))) := by
  unfold pathBlockSplit
  rw [hgamma]
  have ha' : (a : ℝ) = ↑(a - 1) + 1 := by
    rw [Nat.cast_sub ha]; ring
  have hb' : (b : ℝ) = ↑(b - 1) + 1 := by
    rw [Nat.cast_sub hb]; ring
  rw [show (1 - q) ^ a = (1 - q) ^ (a - 1) * (1 - q) from by
    rw [← pow_succ]; congr 1; omega]
  rw [show R ^ b = R ^ (b - 1) * R from by
    rw [← pow_succ]; congr 1; omega]
  field_simp
  ring

/-! ### Single edge as a block -/

/-- A single edge has reliability `1 - q` and split-reliability `q`. -/
theorem singleEdge_rel (q : ℝ) : (1 - q) ^ 1 * q ^ 0 = 1 - q := by ring

theorem singleEdge_split (q : ℝ) : (1 - q) ^ 0 * q ^ 1 = q := by ring
