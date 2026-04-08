/-
Copyright (c) 2026 Pjotr Buys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys
-/
import ReliabilityRoots.LimCompleteGraph
import ReliabilityRoots.CycleGadget
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial

/-!
# Proof of the main theorem: real reliability roots are dense in [-1, 0]

From the paper "Real reliability roots of simple graphs are dense in [-1, 0]"
by Pjotr Buys.

This file contains the full proof machinery. The clean theorem statement is in
`ReliabilityRoots.MainTheorem`.

## Proof strategy

We use the cycle-substitution gadget `C_n[K_m]` together with the intermediate
value theorem. For any `q₀ ∈ (-1, 0)` and `ε > 0`:

1. Pick `q₁ = q₀ + δ ∈ (q₀, 0)` within `ε` of `q₀` with `|q₁| < |q₀|`.
2. For large even `m`: `Rel(K_m; q₀) > 0` and `splitRel(K_m; q₀) < 0`
   (using the limits `Rel → 1` and `splitRel/q^{m-1} → 2` with `q₀^{odd} < 0`).
3. Choose `n = ⌈-Rel(K_m; q₀)/splitRel(K_m; q₀)⌉ ≥ 3`.
4. The function `f_n(q) = Rel(K_m; q) + n · splitRel(K_m; q)` satisfies
   `f_n(q₀) ≤ 0` and `f_n(q₁) > 0` (since `|q₁|^{m-1} ≪ |q₀|^{m-1}`).
5. By IVT, `f_n` has a root `q* ∈ (q₀, q₁) ⊂ B(q₀, ε)`.
6. Then `Rel(C_n[K_m]; q*) = Rel(K_m; q*)^{n-1} · f_n(q*) = 0`,
   and `C_n[K_m]` is a connected simple graph, so `q* ∈ Z`.
-/

open SimpleGraph Set Finset Filter Metric

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Cycle substitution produces reliability roots -/

/-- Given a connected graph `H` on `Fin k` with `H.Adj u v`, and `n ≥ 3`,
if `Rel(H; q*) + n · splitRel(H; q*) = 0` and `Rel(H; q*) ≠ 0`,
then `q*` is a reliability root of the connected graph `C_n[H]`. -/
theorem cycleSubst_root_in_reliabilityRootSet {k : ℕ}
    (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hH : H.Connected) (u v : Fin k) (huv : u ≠ v)
    (n : ℕ) (hn : 3 ≤ n) (q : ℝ)
    (hfn : H.reliabilityFun q + ↑n * H.splitRelFun u v q = 0) :
    q ∈ reliabilityRootSet := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨CycleSubstVertex n u v, inferInstance, inferInstance,
    cycleSubst H u v n, cycleSubst_connected H hH u v huv n hn, ?_⟩
  rw [cycleSubst_reliabilityFun H hH u v huv n hn q,
      cycleBlockRel_eq _ _ _ (by omega)]
  exact mul_eq_zero_of_right _ hfn

/-! ### Continuity of reliability polynomials -/

private lemma continuous_reliabilityFun {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Continuous G.reliabilityFun :=
  continuous_finset_sum _ fun A _ => by split_ifs <;> fun_prop

private lemma continuous_splitRelFun {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    Continuous (G.splitRelFun u v) := by
  unfold SimpleGraph.splitRelFun; dsimp only []
  exact continuous_finset_sum _ fun A _ => by split_ifs <;> fun_prop

/-! ### The interior (-1, 0) -/

set_option maxHeartbeats 400000 in
-- The proof involves many `set` definitions and `field_simp`/`nlinarith` calls on
-- graph polynomial expressions that are slow to elaborate.
/-- **Core density lemma**: `(-1, 0) ⊆ closure(reliabilityRootSet)`.

For any `q₀ ∈ (-1, 0)` and `ε > 0`, we produce a reliability root within `ε`
of `q₀` using the cycle substitution `C_n[K_m]` and the intermediate value theorem. -/
theorem ioo_subset_closure :
    Ioo (-1 : ℝ) 0 ⊆ closure reliabilityRootSet := by
  intro q₀ ⟨hq₀_gt, hq₀_lt⟩
  have hq₀_neg : q₀ < 0 := hq₀_lt
  have hq₀_ne0 : q₀ ≠ 0 := ne_of_lt hq₀_neg
  have hq₀_abs : |q₀| < 1 := by rw [abs_lt]; constructor <;> linarith
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- Step 1: Pick q₁ ∈ (q₀, 0) within ε of q₀, with |q₁| < |q₀|
  set δ := min (ε / 2) ((-q₀) / 2) with hδ_def
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set q₁ := q₀ + δ with hq₁_def
  have hq₁_neg : q₁ < 0 := by
    simp only [hq₁_def]; linarith [min_le_right (ε / 2) (-q₀ / 2)]
  have hq₁_gt : q₀ < q₁ := by linarith
  have hq₁_in : q₁ ∈ Ioo (-1 : ℝ) 0 := ⟨by linarith, hq₁_neg⟩
  have hq₁_ne0 : q₁ ≠ 0 := ne_of_lt hq₁_neg
  have hq₁_abs : |q₁| < 1 := by rw [abs_lt]; constructor <;> linarith [hq₁_in.1]
  -- Key: |q₁| < |q₀| (since both negative and q₁ closer to 0)
  have habs_lt : |q₁| < |q₀| := by
    rw [abs_of_neg hq₁_neg, abs_of_neg hq₀_neg]; linarith
  have habs_ratio_lt : |q₁| / |q₀| < 1 := by
    rw [div_lt_one (abs_pos.mpr hq₀_ne0)]; exact habs_lt
  -- Step 2: Geometric decay sequences
  have h_q0_pow : Tendsto (fun n => |q₀| ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hq₀_abs
  have h_ratio_pow : Tendsto (fun n => (|q₁| / |q₀|) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg (abs_nonneg _) (abs_nonneg _))
      habs_ratio_lt
  -- Step 3: Extract bounds from limits
  -- Rel(K_n; q) → 1 as n → ∞
  have h_rel_q₀ := lim_rel_completeGraph q₀ hq₀_abs
  have h_rel_q₁ := lim_rel_completeGraph q₁ hq₁_abs
  -- splitRel(K_{n+2}; q) / q^{n+1} → 2 as n → ∞
  have h_srel_q₀ := lim_srel_completeGraph_normalized q₀ hq₀_abs hq₀_ne0
  have h_srel_q₁ := lim_srel_completeGraph_normalized q₁ hq₁_abs hq₁_ne0
  rw [Metric.tendsto_atTop] at h_rel_q₀ h_rel_q₁ h_srel_q₀ h_srel_q₁ h_q0_pow h_ratio_pow
  obtain ⟨N₁, hN₁⟩ := h_rel_q₀ (1/4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := h_rel_q₁ (1/4) (by positivity)
  obtain ⟨N₃, hN₃⟩ := h_srel_q₀ 1 (by positivity)
  obtain ⟨N₄, hN₄⟩ := h_srel_q₁ 1 (by positivity)
  obtain ⟨N₅, hN₅⟩ := h_q0_pow (1/16) (by positivity)
  obtain ⟨N₆, hN₆⟩ := h_ratio_pow (1/16) (by positivity)
  -- Step 4: Choose p large enough for all conditions.
  -- Graph K_{2p+2} has 2p+2 vertices; the srel limit uses index 2p (graph Fin(2p+2)).
  set p := max (max (max (max (max N₁ N₂) (max N₃ N₄)) N₅) N₆) 1 with hp_def
  have hp_ge : 1 ≤ p := le_max_right _ _
  have hp_N₁ : N₁ ≤ 2 * p + 2 := by omega
  have hp_N₂ : N₂ ≤ 2 * p + 2 := by omega
  have hp_N₃ : N₃ ≤ 2 * p := by omega
  have hp_N₄ : N₄ ≤ 2 * p := by omega
  have hp_N₅ : N₅ ≤ 2 * p + 1 := by omega
  have hp_N₆ : N₆ ≤ 2 * p + 1 := by omega
  -- Step 5: Extract concrete bounds.
  -- We work directly with index types to avoid Fin conversion issues.
  -- Rel bounds: |Rel(K_{2p+2}; q) - 1| < 1/4
  have hR₀_near : dist ((⊤ : SimpleGraph (Fin (2 * p + 2))).reliabilityFun q₀) 1 < 1/4 :=
    hN₁ (2 * p + 2) hp_N₁
  have hR₁_near : dist ((⊤ : SimpleGraph (Fin (2 * p + 2))).reliabilityFun q₁) 1 < 1/4 :=
    hN₂ (2 * p + 2) hp_N₂
  -- splitRel bounds at index 2p (graph Fin(2p+2), power q^{2p+1})
  have hS₀_near : dist ((⊤ : SimpleGraph (Fin (2 * p + 2))).splitRelFun
      ⟨0, by omega⟩ ⟨1, by omega⟩ q₀ / q₀ ^ (2 * p + 1)) 2 < 1 :=
    hN₃ (2 * p) hp_N₃
  have hS₁_near : dist ((⊤ : SimpleGraph (Fin (2 * p + 2))).splitRelFun
      ⟨0, by omega⟩ ⟨1, by omega⟩ q₁ / q₁ ^ (2 * p + 1)) 2 < 1 :=
    hN₄ (2 * p) hp_N₄
  -- |q₀|^{2p+1} < 1/16
  have hq₀_pow_small : |q₀| ^ (2 * p + 1) < 1/16 := by
    have := hN₅ (2 * p + 1) hp_N₅; rw [Real.dist_eq, sub_zero] at this
    rwa [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)] at this
  -- (|q₁|/|q₀|)^{2p+1} < 1/16
  have hratio_pow_small : (|q₁| / |q₀|) ^ (2 * p + 1) < 1/16 := by
    have := hN₆ (2 * p + 1) hp_N₆; rw [Real.dist_eq, sub_zero] at this
    rwa [abs_of_nonneg (pow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _)] at this
  -- |q₁|^{2p+1} < |q₀|^{2p+1} (since |q₁| < |q₀|)
  have hq₁_pow_small : |q₁| ^ (2 * p + 1) < 1/16 :=
    lt_trans (pow_lt_pow_left₀ habs_lt (abs_nonneg _) (by omega)) hq₀_pow_small
  -- Now introduce abbreviations for the graph quantities
  set m := 2 * p + 2
  set u : Fin m := ⟨0, by omega⟩
  set v : Fin m := ⟨1, by omega⟩
  have huv : u ≠ v := by simp [u, v]
  set R₀ := (⊤ : SimpleGraph (Fin m)).reliabilityFun q₀
  set S₀ := (⊤ : SimpleGraph (Fin m)).splitRelFun u v q₀
  set R₁ := (⊤ : SimpleGraph (Fin m)).reliabilityFun q₁
  set S₁ := (⊤ : SimpleGraph (Fin m)).splitRelFun u v q₁
  -- Transfer the bounds to the abbreviated names
  -- (Fin m = Fin (2*p+2) definitionally, u and v match the limit's ⟨0,_⟩ and ⟨1,_⟩)
  change dist R₀ 1 < 1 / 4 at hR₀_near
  change dist R₁ 1 < 1 / 4 at hR₁_near
  change dist (S₀ / q₀ ^ (2 * p + 1)) 2 < 1 at hS₀_near
  change dist (S₁ / q₁ ^ (2 * p + 1)) 2 < 1 at hS₁_near
  rw [Real.dist_eq] at hR₀_near hR₁_near hS₀_near hS₁_near
  -- Extract explicit inequalities from the absolute value bounds
  have ⟨hR₀_lo, hR₀_hi⟩ := abs_lt.mp hR₀_near
  have ⟨hR₁_lo, hR₁_hi⟩ := abs_lt.mp hR₁_near
  have ⟨hS₀_lo, hS₀_hi⟩ := abs_lt.mp hS₀_near
  have ⟨hS₁_lo, hS₁_hi⟩ := abs_lt.mp hS₁_near
  -- So R₀ > 3/4, R₁ > 3/4, R₀ < 5/4
  have hR₀_pos : (3 : ℝ)/4 < R₀ := by linarith
  have hR₁_pos : (3 : ℝ)/4 < R₁ := by linarith
  have hR₀_le : R₀ < 5/4 := by linarith
  -- S₀/q₀^{2p+1} ∈ (1, 3) and S₁/q₁^{2p+1} ∈ (1, 3)
  have hS₀_ratio_lo : 1 < S₀ / q₀ ^ (2 * p + 1) := by linarith
  have hS₀_ratio_hi : S₀ / q₀ ^ (2 * p + 1) < 3 := by linarith
  have hS₁_ratio_lo : 1 < S₁ / q₁ ^ (2 * p + 1) := by linarith
  have hS₁_ratio_hi : S₁ / q₁ ^ (2 * p + 1) < 3 := by linarith
  -- q₀^{2p+1} < 0 (odd power of negative number)
  have hodd : Odd (2 * p + 1) := ⟨p, by ring⟩
  have hq₀_pow_neg : q₀ ^ (2 * p + 1) < 0 := hodd.pow_neg hq₀_neg
  have hq₁_pow_neg : q₁ ^ (2 * p + 1) < 0 := hodd.pow_neg hq₁_neg
  have hq₀_pow_ne : q₀ ^ (2 * p + 1) ≠ 0 := ne_of_lt hq₀_pow_neg
  have hq₁_pow_ne : q₁ ^ (2 * p + 1) ≠ 0 := ne_of_lt hq₁_pow_neg
  -- Since S₀/(q₀^{2p+1}) > 1 and q₀^{2p+1} < 0, we get S₀ < 0
  have hS₀_neg : S₀ < 0 := by
    by_contra h; push_neg at h
    have : S₀ / q₀ ^ (2 * p + 1) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos h (le_of_lt hq₀_pow_neg)
    linarith
  have hS₀_ne : S₀ ≠ 0 := ne_of_lt hS₀_neg
  -- Similarly S₁ < 0
  have hS₁_neg : S₁ < 0 := by
    by_contra h; push_neg at h
    have : S₁ / q₁ ^ (2 * p + 1) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos h (le_of_lt hq₁_pow_neg)
    linarith
  -- Step 6: Bound |S₀| from above
  -- From S₀/q₀^{2p+1} < 3 and q₀^{2p+1} < 0: S₀ > 3·q₀^{2p+1}
  -- So |S₀| = -S₀ < 3·|q₀|^{2p+1} < 3/16
  have hS₀_abs_bound : -S₀ < 3/16 := by
    -- From ratio < 3: multiply both sides of S₀/q₀^{2p+1} < 3 by q₀^{2p+1} < 0, reversing
    have h := mul_lt_mul_of_neg_left hS₀_ratio_hi hq₀_pow_neg
    rw [mul_div_cancel₀ _ hq₀_pow_ne] at h
    -- h : 3 * q₀^{2p+1} < S₀, so -S₀ < -(3 * q₀^{2p+1}) = 3 * |q₀|^{2p+1}
    have habs_pow : -q₀ ^ (2 * p + 1) = |q₀| ^ (2 * p + 1) := by
      rw [← abs_pow, abs_of_neg hq₀_pow_neg]
    linarith
  -- Step 7: Define t = -R₀/S₀ and bound t ≥ 3
  -- t = R₀/(-S₀) > (3/4)/(3/16) = 4 > 3
  set t := -R₀ / S₀ with ht_def
  have ht_pos : 0 < t := div_pos_of_neg_of_neg (by linarith) hS₀_neg
  have ht_ge : 3 ≤ t := by
    rw [ht_def, le_div_iff_of_neg hS₀_neg]
    -- Goal: -R₀ ≤ 3 * S₀, equivalently 3*(-S₀) ≤ R₀.
    -- From hS₀_abs_bound: -S₀ < 3/16, so 3*(-S₀) < 9/16 < 3/4 < R₀.
    nlinarith
  set n := Nat.ceil t with hn_def
  have hn_ge : 3 ≤ n := by
    exact_mod_cast ht_ge.trans (Nat.le_ceil t)
  -- Step 8: f(q₀) ≤ 0
  -- f(q₀) = R₀ + n·S₀. Since n ≥ t = -R₀/S₀ and S₀ < 0:
  -- n·S₀ ≤ t·S₀ = -R₀, so R₀ + n·S₀ ≤ 0.
  have hfn_q₀ : R₀ + ↑n * S₀ ≤ 0 := by
    have hn_ge_t : (t : ℝ) ≤ ↑n := Nat.le_ceil t
    have h1 : ↑n * S₀ ≤ t * S₀ := mul_le_mul_of_nonpos_right hn_ge_t (le_of_lt hS₀_neg)
    have h2 : t * S₀ = -R₀ := by rw [ht_def]; field_simp
    linarith
  -- Step 9: f(q₁) > 0
  -- Auxiliary: ↑n < t + 1
  have hn_lt : (↑n : ℝ) < t + 1 := Nat.ceil_lt_add_one (le_of_lt ht_pos)
  -- Auxiliary: -S₀ > |q₀|^{2p+1} (from ratio > 1)
  have hS₀_lo : |q₀| ^ (2 * p + 1) < -S₀ := by
    have : S₀ < q₀ ^ (2 * p + 1) := by
      by_contra h; push_neg at h
      have : S₀ / q₀ ^ (2 * p + 1) ≤ 1 := (div_le_one_of_neg hq₀_pow_neg).mpr h
      linarith
    linarith [show -q₀ ^ (2 * p + 1) = |q₀| ^ (2 * p + 1) from by
      rw [← abs_pow, abs_of_neg hq₀_pow_neg]]
  -- Auxiliary: -S₁ < 3·|q₁|^{2p+1} (from ratio < 3)
  have hS₁_abs_bound : -S₁ < 3 * |q₁| ^ (2 * p + 1) := by
    have : 3 * q₁ ^ (2 * p + 1) < S₁ := by
      by_contra h; push_neg at h
      have : 3 ≤ S₁ / q₁ ^ (2 * p + 1) := by rwa [le_div_iff_of_neg hq₁_pow_neg]
      linarith
    linarith [show -q₁ ^ (2 * p + 1) = |q₁| ^ (2 * p + 1) from by
      rw [← abs_pow, abs_of_neg hq₁_pow_neg]]
  -- Auxiliary: |q₁|^k = ratio^k · |q₀|^k
  have hpow_factor : |q₁| ^ (2 * p + 1) =
      (|q₁| / |q₀|) ^ (2 * p + 1) * |q₀| ^ (2 * p + 1) := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (abs_ne_zero.mpr hq₀_ne0))]
  -- Abbreviations
  set r := (|q₁| / |q₀|) ^ (2 * p + 1) with hr_def
  set a₀ := |q₀| ^ (2 * p + 1) with ha₀_def
  have ha₀_pos : 0 < a₀ := pow_pos (abs_pos.mpr hq₀_ne0) _
  have hr_nonneg : 0 ≤ r := pow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _
  have ha₁_eq : |q₁| ^ (2 * p + 1) = r * a₀ := hpow_factor
  -- We bound t * a₀ < R₀ (since t = R₀/(-S₀) and -S₀ > a₀)
  have ht_upper : t * a₀ < R₀ := by
    have h_neg_S₀_pos : 0 < -S₀ := by linarith
    -- t * a₀ < t * (-S₀) = R₀
    calc t * a₀
        < t * (-S₀) := mul_lt_mul_of_pos_left hS₀_lo ht_pos
      _ = R₀ := by rw [ht_def]; field_simp
  -- Main bound: n * (-S₁) < 3/4 < R₁
  -- Strategy: show (↑n)*(-S₁) < (t+1)*3*(r*a₀)
  --   = 3*t*a₀*r + 3*r*a₀ < 3*R₀*r + 3*r*a₀ < 3*(5/4)*(1/16) + 3*(1/16)*(1/16)
  --   = 15/64 + 3/256 < 1/4 < 3/4
  have hfn_q₁ : R₁ + ↑n * S₁ > 0 := by
    suffices h : ↑n * (-S₁) < 3/4 by linarith
    -- All key numerical bounds:
    have hS₁_pos : 0 < -S₁ := by linarith
    have hB : -S₁ < 3 * (r * a₀) := by rwa [← ha₁_eq]
    -- (t+1)*(-S₁) < (t+1)*3*r*a₀ = 3*r*((t+1)*a₀)
    -- We use: ↑n*(-S₁) < (t+1)*(-S₁) and then bound (-S₁) and (t+1) separately
    -- Instead, let's directly bound using: ↑n < t+1, -S₁ < 3*r*a₀, t*a₀ < R₀ < 5/4
    -- So ↑n*(-S₁) < (t+1)*3*r*a₀ = 3*r*t*a₀ + 3*r*a₀ < 3*r*R₀ + 3*r*a₀
    -- < 3*(1/16)*(5/4) + 3*(1/16)*(1/16) = 15/64 + 3/256 = 63/256 < 3/4
    have hr_lt : r < 1/16 := hratio_pow_small
    have ha₀_lt : a₀ < 1/16 := hq₀_pow_small
    -- r > 0 (since q₁ ≠ 0)
    have hr_pos : 0 < r := pow_pos (div_pos (abs_pos.mpr hq₁_ne0) (abs_pos.mpr hq₀_ne0)) _
    -- Key products we'll need as hints for linarith
    have h_prod1 : r * a₀ < 1/16 * (1/16) :=
      mul_lt_mul hr_lt ha₀_lt.le ha₀_pos (by norm_num)
    have h_prod2 : R₀ * r < (5/4) * (1/16) :=
      mul_lt_mul hR₀_le hr_lt.le hr_pos (by norm_num)
    have h_ta₀r : t * a₀ * r < R₀ * r :=
      mul_lt_mul_of_pos_right ht_upper hr_pos
    -- Now ↑n * (-S₁) < (t+1) * (3*(r*a₀)) by step
    have h_step1 : ↑n * (-S₁) < (t + 1) * (-S₁) := mul_lt_mul_of_pos_right hn_lt hS₁_pos
    have h_step2 : (t + 1) * (-S₁) < (t + 1) * (3 * (r * a₀)) :=
      mul_lt_mul_of_pos_left hB (by linarith)
    -- Now bound (t+1) * (3*(r*a₀)) = 3*(t*a₀*r + r*a₀)
    -- ≤ 3*(R₀*r + r*a₀) < 3*((5/4)*(1/16) + (1/16)*(1/16)) = 3*(5/64 + 1/256)
    -- = 3 * 21/256 = 63/256 < 3/4
    -- Let's compute directly
    have h_expand : (t + 1) * (3 * (r * a₀)) = 3 * (t * (r * a₀) + r * a₀) := by ring
    have h_mid : t * (r * a₀) + r * a₀ < R₀ * r + 1/16 * (1/16) := by
      have : t * (r * a₀) = t * a₀ * r := by ring
      linarith [h_ta₀r, h_prod1]
    have h_final : R₀ * r + 1/16 * (1/16) < 5/64 + 1/256 := by linarith [h_prod2]
    linarith
  -- Step 10: IVT gives root in [q₀, q₁]
  set f := fun q => (⊤ : SimpleGraph (Fin m)).reliabilityFun q +
    ↑n * (⊤ : SimpleGraph (Fin m)).splitRelFun u v q
  have hf_cont : Continuous f :=
    (continuous_reliabilityFun _).add (continuous_const.mul (continuous_splitRelFun _ u v))
  have hle : q₀ ≤ q₁ := le_of_lt hq₁_gt
  have h0_mem : (0 : ℝ) ∈ Icc (f q₀) (f q₁) := ⟨hfn_q₀, le_of_lt hfn_q₁⟩
  obtain ⟨q_star, hqs_mem, hqs_val⟩ :=
    intermediate_value_Icc hle hf_cont.continuousOn h0_mem
  -- Step 11: q_star is a reliability root
  refine ⟨q_star, cycleSubst_root_in_reliabilityRootSet (⊤ : SimpleGraph (Fin m))
    (by rw [← completeGraph_eq_top]; exact connected_top)
    u v huv n hn_ge q_star hqs_val, ?_⟩
  -- Step 12: dist q₀ q_star < ε
  rw [Real.dist_eq]
  calc |q₀ - q_star|
      ≤ q₁ - q₀ := by
        rw [abs_le]; exact ⟨by linarith [hqs_mem.2], by linarith [hqs_mem.1]⟩
    _ = δ := by ring
    _ < ε := hδ_lt_ε

/-! ### Assembly: [-1, 0] from (-1, 0) plus closure -/

/-- `[-1, 0] ⊆ closure(reliabilityRootSet)`, proved from `ioo_subset_closure`.
The clean statement is re-exported in `ReliabilityRoots.MainTheorem`. -/
theorem icc_subset_closure_reliabilityRootSet :
    Icc (-1 : ℝ) 0 ⊆ closure reliabilityRootSet := by
  calc Icc (-1 : ℝ) 0
      = closure (Ioo (-1 : ℝ) 0) := by
        rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
    _ ⊆ closure (closure reliabilityRootSet) :=
        closure_mono ioo_subset_closure
    _ = closure reliabilityRootSet :=
        isClosed_closure.closure_eq

end
