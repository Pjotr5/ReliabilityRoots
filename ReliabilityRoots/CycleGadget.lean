/-
Copyright (c) 2026 Pjotr Buys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys
-/
import ReliabilityRoots.Defs
import ReliabilityRoots.BlockAlgebra
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Cycle-substitution gadget graph

Given a connected graph `H` on `Fin k` with distinguished vertices `u, v`,
the **cycle-substitution graph** `cycleSubst H u v n` is obtained from the cycle `Cₙ`
by replacing each edge with a copy of `H` (identifying the endpoints with `u` and `v`).

## Vertex type

The vertex set consists of:
- **Cycle vertices** `cycle i` for `i ∈ Fin n`: shared terminals of consecutive copies.
- **Internal vertices** `internal i j` for `i ∈ Fin n` and `j ∈ Fin k` with `j ≠ u, j ≠ v`:
  the non-terminal vertices of copy `i`.

Copy `i` of `H` maps vertex `u` to `cycle i`, vertex `v` to `cycle ((i+1) mod n)`,
and all other vertices `j` to `internal i ⟨j, _⟩`.

## Main results

* `cycleSubst_connected`: the cycle-substitution graph is connected
* `cycleSubst_reliabilityFun`: its reliability equals `cycleBlockRel (Rel(H;q)) (splitRel(H;q)) n`
-/

open SimpleGraph Finset

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℕ}

/-! ### Vertex type -/

/-- Vertex type for the cycle-substitution graph.
    Internal vertices exclude `u` and `v` since those are identified with cycle vertices. -/
inductive CycleSubstVertex (n : ℕ) {k : ℕ} (u v : Fin k) where
  | cycle : Fin n → CycleSubstVertex n u v
  | internal : Fin n → {j : Fin k // j ≠ u ∧ j ≠ v} → CycleSubstVertex n u v
deriving DecidableEq

instance {n : ℕ} {u v : Fin k} : Fintype (CycleSubstVertex n u v) :=
  Fintype.ofEquiv (Fin n ⊕ (Fin n × {j : Fin k // j ≠ u ∧ j ≠ v}))
    { toFun := fun x => match x with
        | Sum.inl i => .cycle i
        | Sum.inr ⟨i, j⟩ => .internal i j
      invFun := fun x => match x with
        | .cycle i => Sum.inl i
        | .internal i j => Sum.inr ⟨i, j⟩
      left_inv := fun x => by cases x <;> rfl
      right_inv := fun x => by cases x <;> rfl }

/-! ### Vertex mapping -/

/-- Map a vertex of copy `i` of `H` to a vertex of the cycle-substitution graph.
Terminal `u` maps to `cycle i`, terminal `v` maps to `cycle ((i+1) mod n)`,
and other vertices map to `internal i ⟨j, ...⟩`. -/
def copyVertex (u v : Fin k) (n : ℕ) [NeZero n] (i : Fin n) (j : Fin k) :
    CycleSubstVertex n u v :=
  if h : j = u then .cycle i
  else if h' : j = v then .cycle ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
  else .internal i ⟨j, h, h'⟩

/-! ### Adjacency -/

/-- The cycle-substitution graph on `CycleSubstVertex n u v`.
Two vertices are adjacent if they belong to the same copy of `H` (after the
terminal identification) and the corresponding `H`-vertices are adjacent. -/
def cycleSubstAdj (H : SimpleGraph (Fin k)) (u v : Fin k) (n : ℕ) [NeZero n]
    (x y : CycleSubstVertex n u v) : Prop :=
  x ≠ y ∧ ∃ (i : Fin n) (jx jy : Fin k),
    copyVertex u v n i jx = x ∧
    copyVertex u v n i jy = y ∧
    H.Adj jx jy

instance (H : SimpleGraph (Fin k)) (u v : Fin k) (n : ℕ) [NeZero n] :
    DecidableRel (cycleSubstAdj H u v n) := by
  intro x y; unfold cycleSubstAdj; exact inferInstance

/-- The cycle-substitution graph. -/
def cycleSubst (H : SimpleGraph (Fin k)) (u v : Fin k) (n : ℕ) [NeZero n] :
    SimpleGraph (CycleSubstVertex n u v) where
  Adj := cycleSubstAdj H u v n
  symm := by
    intro x y ⟨hne, i, jx, jy, hx, hy, hadj⟩
    exact ⟨hne.symm, i, jy, jx, hy, hx, hadj.symm⟩
  loopless := ⟨fun {x} ⟨hne, _⟩ => hne rfl⟩

/-! ### Connectivity -/

/-- Within a single copy, H-reachability implies cycleSubst-reachability. -/
private lemma copy_reachable (H : SimpleGraph (Fin k)) (u v : Fin k)
    (n : ℕ) [NeZero n] (i : Fin n) (jx jy : Fin k)
    (h : H.Reachable jx jy) :
    (cycleSubst H u v n).Reachable (copyVertex u v n i jx) (copyVertex u v n i jy) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hadj _w ih =>
    by_cases heq : copyVertex u v n i a = copyVertex u v n i b
    · rw [heq]; exact ih
    · have : (cycleSubst H u v n).Adj (copyVertex u v n i a) (copyVertex u v n i b) :=
        ⟨heq, i, a, b, rfl, rfl, hadj⟩
      exact this.reachable.trans ih

/-- The cycle-substitution graph is connected when `H` is connected and `n ≥ 3`. -/
theorem cycleSubst_connected (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hH : H.Connected) (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    (cycleSubst H u v n).Connected := by
  have h0 : 0 < n := by omega
  -- copyVertex identities
  have hu_eq : ∀ i : Fin n, copyVertex u v n i u = .cycle i := by
    intro i; simp [copyVertex]
  have hv_eq : ∀ i : Fin n, copyVertex u v n i v =
      .cycle ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := by
    intro i; unfold copyVertex; rw [dif_neg (Ne.symm huv), dif_pos rfl]
  -- Cycle vertex m is reachable from cycle 0
  have cycle_reach : ∀ (m : ℕ) (hm : m < n),
      (cycleSubst H u v n).Reachable (.cycle ⟨0, h0⟩) (.cycle ⟨m, hm⟩) := by
    intro m hm
    induction m with
    | zero => exact Reachable.refl _
    | succ m ih =>
      refine (ih (by omega)).trans ?_
      have hr := copy_reachable H u v n ⟨m, by omega⟩ u v (hH.preconnected u v)
      rw [hu_eq, hv_eq] at hr
      rwa [show (⟨(m + 1) % n, _⟩ : Fin n) = ⟨m + 1, hm⟩ from
        Fin.ext (Nat.mod_eq_of_lt hm)] at hr
  -- Preconnected + Nonempty
  haveI : Nonempty (CycleSubstVertex n u v) := ⟨.cycle ⟨0, h0⟩⟩
  exact Connected.mk (fun x y => by
    suffices ∀ z, (cycleSubst H u v n).Reachable (.cycle ⟨0, h0⟩) z from
      (this x).symm.trans (this y)
    intro z
    match z with
    | .cycle ⟨m, hm⟩ => exact cycle_reach m hm
    | .internal ⟨m, hm⟩ j =>
      have hr := copy_reachable H u v n ⟨m, hm⟩ u j.val (hH.preconnected u j.val)
      rw [hu_eq] at hr
      have : copyVertex u v n ⟨m, hm⟩ j.val = .internal ⟨m, hm⟩ j := by
        unfold copyVertex; rw [dif_neg j.prop.1, dif_neg j.prop.2]
      rw [this] at hr
      exact (cycle_reach m hm).trans hr)

/-! ### Edge set decomposition

The edge set of `cycleSubst H u v n` decomposes as a disjoint union of `n` copies of
`H.edgeFinset`, one per copy of `H`. Copy `i` embeds `H`'s edges via
`Sym2.map (copyVertex u v n i)`.

Key facts:
1. `copyVertex u v n i` is injective (for `n ≥ 2`), so `Sym2.map` of it is too.
2. Copy edge sets are pairwise disjoint (for `n ≥ 3`).
3. Every edge of `cycleSubst` belongs to some copy.
-/

/-- Left inverse of `copyVertex u v n i` (for recovering the H-vertex from a cycleSubst vertex). -/
private def copyVertexInv (u v : Fin k) (n : ℕ) (i : Fin n) :
    CycleSubstVertex n u v → Fin k
  | .cycle j => if j = i then u else v
  | .internal _ ⟨w, _⟩ => w

/-- `copyVertex u v n i` is injective when `n ≥ 2`. -/
theorem copyVertex_injective (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (i : Fin n) : Function.Injective (copyVertex u v n i) := by
  have cycle_ne : (⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) ≠ i := by
    simp only [ne_eq, Fin.ext_iff]
    rcases Nat.lt_or_eq_of_le (show i.val + 1 ≤ n from i.isLt) with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [h, Nat.mod_self]; omega
  apply Function.HasLeftInverse.injective ⟨copyVertexInv u v n i, fun j => ?_⟩
  simp only [copyVertex]
  split_ifs with h1 h2 <;> simp_all [copyVertexInv, cycle_ne]

/-- The edges of copy `i` of `H` in the cycle-substitution graph. -/
def copyEdges (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    Finset (Sym2 (CycleSubstVertex n u v)) :=
  H.edgeFinset.map ⟨Sym2.map (copyVertex u v n i),
    Sym2.map.injective (copyVertex_injective u v huv n hn i)⟩

/-- The edge set of cycleSubst is the union of copy edge sets. -/
theorem cycleSubst_edgeFinset_eq (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    (cycleSubst H u v n).edgeFinset = Finset.biUnion Finset.univ
      (copyEdges H u v huv n (by omega)) := by
  ext e; refine Sym2.ind (fun x y => ?_) e
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_biUnion,
    Finset.mem_univ, true_and, copyEdges, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · -- Forward: edge of cycleSubst → in some copyEdges
    intro ⟨_, i, jx, jy, hx, hy, hadj⟩
    exact ⟨i, s(jx, jy), hadj, by rw [Sym2.map_pair_eq, hx, hy]⟩
  · -- Backward: in copyEdges → edge of cycleSubst
    intro ⟨i, e', he', heq⟩
    revert he' heq; refine Sym2.ind (fun a b => ?_) e'; intro he' heq
    rw [SimpleGraph.mem_edgeSet] at he'
    rw [Sym2.map_pair_eq] at heq
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun h => he'.ne (copyVertex_injective u v huv n (by omega) i h),
        i, a, b, rfl, rfl, he'⟩
    · exact ⟨fun h => he'.symm.ne (copyVertex_injective u v huv n (by omega) i h),
        i, b, a, rfl, rfl, he'.symm⟩

/-- Copy edge sets are pairwise disjoint. -/
theorem copyEdges_pairwise_disjoint (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin n))
      (copyEdges H u v huv n (by omega)) := by
  -- Helper: if copyVertex i a = copyVertex j b with i ≠ j, then a ∈ {u, v}
  have mem_terminal : ∀ (i j : Fin n), i ≠ j → ∀ (a b : Fin k),
      copyVertex u v n i a = copyVertex u v n j b → a = u ∨ a = v := by
    intro i j hij a b h
    by_contra hc; push_neg at hc
    have : copyVertex u v n i a = .internal i ⟨a, hc.1, hc.2⟩ := by
      unfold copyVertex; rw [dif_neg hc.1, dif_neg hc.2]
    rw [this] at h; unfold copyVertex at h
    split_ifs at h <;>
      first | exact CycleSubstVertex.noConfusion h
            | exact hij (CycleSubstVertex.internal.inj h).1
  -- Main proof: pairwise disjoint
  intro i _ j _ hij
  rw [Function.onFun, Finset.disjoint_left]
  intro e hei hej
  simp only [copyEdges, Finset.mem_map, Function.Embedding.coeFn_mk] at hei hej
  obtain ⟨e₁, he₁, rfl⟩ := hei
  obtain ⟨e₂, he₂, heq⟩ := hej
  -- Decompose edges into pairs
  revert he₁ he₂ heq
  refine Sym2.ind (fun a b => ?_) e₁
  refine Sym2.ind (fun c d => ?_) e₂
  intro he₁ he₂ heq
  rw [Sym2.map_pair_eq, Sym2.map_pair_eq] at heq
  -- From edge membership, a ≠ b and c ≠ d (SimpleGraph.irrefl)
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he₁ he₂
  -- Get all four vertices are in {u, v}
  -- Helper to extract Fin.val equations from copyVertex terminal equalities
  suffices aux : ∀ (a' b' c' d' : Fin k),
      H.Adj a' b' → H.Adj c' d' →
      (a' = u ∨ a' = v) → (b' = u ∨ b' = v) →
      (c' = u ∨ c' = v) → (d' = u ∨ d' = v) →
      copyVertex u v n i a' = copyVertex u v n j c' →
      copyVertex u v n i b' = copyVertex u v n j d' → False by
    have hij' := Ne.symm hij
    -- heq : s(copyVertex j c, copyVertex j d) = s(copyVertex i a, copyVertex i b)
    -- Sym2.eq_iff gives: (j c = i a ∧ j d = i b) ∨ (j c = i b ∧ j d = i a)
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- h1: copyVertex j c = copyVertex i a, h2: copyVertex j d = copyVertex i b
      exact aux a b c d he₁ he₂
        (mem_terminal i j hij a c h1.symm) (mem_terminal i j hij b d h2.symm)
        (mem_terminal j i hij' c a h1) (mem_terminal j i hij' d b h2)
        h1.symm h2.symm
    · -- h1: copyVertex j c = copyVertex i b, h2: copyVertex j d = copyVertex i a
      exact aux a b d c he₁ he₂.symm
        (mem_terminal i j hij a d h2.symm) (mem_terminal i j hij b c h1.symm)
        (mem_terminal j i hij' d a h2) (mem_terminal j i hij' c b h1)
        h2.symm h1.symm
  -- Now prove the auxiliary statement
  intro a' b' c' d' hab hcd ha hb hc hd h1 h2
  -- a' ≠ b' and c' ≠ d' from irreflexivity
  have hab' : a' ≠ b' := hab.ne
  have hcd' : c' ≠ d' := hcd.ne
  -- Compute copyVertex on terminals
  have cv_u : ∀ (p : Fin n), copyVertex u v n p u = .cycle p := by
    intro p; simp [copyVertex]
  have cv_v : ∀ (p : Fin n), copyVertex u v n p v =
      .cycle ⟨(p.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := by
    intro p; unfold copyVertex; rw [dif_neg (Ne.symm huv), dif_pos rfl]
  -- Case split on all terminal assignments
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  -- (a',b') = (u,u): contradicts a' ≠ b'
  · exact absurd rfl hab'
  -- (a',b') = (u,v)
  · rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    -- (c',d') = (u,u): contradicts c' ≠ d'
    · exact absurd rfl hcd'
    -- (u,v) vs (u,v): h1 gives i = j
    · rw [cv_u, cv_u] at h1
      exact hij (Fin.ext (Fin.ext_iff.mp (CycleSubstVertex.cycle.inj h1)))
    -- (u,v) vs (v,u): cross
    · -- h1: copyVertex i u = copyVertex j v, h2: copyVertex i v = copyVertex j u
      rw [cv_u, cv_v] at h1; rw [cv_v, cv_u] at h2
      -- h1: cycle i = cycle ⟨(j+1)%n, _⟩, h2: cycle ⟨(i+1)%n, _⟩ = cycle j
      have feq1 := CycleSubstVertex.cycle.inj h1
      have feq2 := CycleSubstVertex.cycle.inj h2
      -- feq1 : i = ⟨(j+1)%n, _⟩, feq2 : ⟨(i+1)%n, _⟩ = j
      have hival : i.val = (j.val + 1) % n := congr_arg Fin.val feq1
      have hjval : (i.val + 1) % n = j.val := congr_arg Fin.val feq2
      -- hival : i.val = (j.val + 1) % n and hjval : (i.val + 1) % n = j.val
      -- Substitute hjval into hival: i.val = ((i.val + 1) % n + 1) % n
      -- Simplify: ((i+1) % n + 1) % n = (i + 2) % n (by Nat.mod_add_mod)
      -- So i.val = (i.val + 2) % n, with i.val < n and n ≥ 3 → contradiction
      have key : (i.val + 1 + 1) % n = i.val := by
        have h1 : i.val = ((i.val + 1) % n + 1) % n := by
          rw [← hjval] at hival; exact hival
        rw [Nat.mod_add_mod] at h1; linarith
      have hi := i.isLt
      -- key : (i.val + 1 + 1) % n = i.val, with hi : i.val < n, hn : 3 ≤ n
      rw [show i.val + 1 + 1 = i.val + 2 from by ring] at key
      by_cases h : i.val + 2 < n
      · rw [Nat.mod_eq_of_lt h] at key; omega
      · rw [Nat.mod_eq_sub_mod (by omega)] at key
        rw [Nat.mod_eq_of_lt (by omega)] at key; omega
    -- (u,v) vs (v,v): contradicts c' ≠ d'
    · exact absurd rfl hcd'
  -- (a',b') = (v,u)
  · rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    · exact absurd rfl hcd'
    -- (v,u) vs (u,v): cross - symmetric to above
    · rw [cv_v, cv_u] at h1; rw [cv_u, cv_v] at h2
      have feq1 := CycleSubstVertex.cycle.inj h1
      have feq2 := CycleSubstVertex.cycle.inj h2
      have hival : (i.val + 1) % n = j.val := congr_arg Fin.val feq1
      have hjval : i.val = (j.val + 1) % n := congr_arg Fin.val feq2
      have hi := i.isLt
      have key : (i.val + 1 + 1) % n = i.val := by
        have h1 : i.val = ((i.val + 1) % n + 1) % n := by
          rw [← hival] at hjval; exact hjval
        rw [Nat.mod_add_mod] at h1; linarith
      rw [show i.val + 1 + 1 = i.val + 2 from by ring] at key
      by_cases h : i.val + 2 < n
      · rw [Nat.mod_eq_of_lt h] at key; omega
      · rw [Nat.mod_eq_sub_mod (by omega)] at key
        rw [Nat.mod_eq_of_lt (by omega)] at key; omega
    -- (v,u) vs (v,u): h2 gives i = j via u-terminal
    · rw [cv_u, cv_u] at h2
      exact hij (Fin.ext (Fin.ext_iff.mp (CycleSubstVertex.cycle.inj h2)))
    · exact absurd rfl hcd'
  -- (a',b') = (v,v): contradicts a' ≠ b'
  · exact absurd rfl hab'

/-! ### Reliability formula -/

/--
The reliability of the cycle-substitution graph equals `cycleBlockRel (Rel(H;q)) (splitRel(H;q)) n`.

**Proof outline:**
1. Edge set of `cycleSubst H u v n` decomposes as disjoint union of `n` copies of `H.edgeFinset`.
2. Powerset of the disjoint union bijects with `(H.edgeFinset.powerset)^n`.
3. Under this bijection, weight `(1-q)^|A| · q^{|E|-|A|}` factorizes as `∏ᵢ weight(Aᵢ)`.
4. `cycleSubst[A]` is connected iff:
   - Every copy connects `u` to `v` (probability `Rel(H;q)^n`), OR
   - Exactly one copy splits `u` from `v`, rest connect (probability `n · splitRel · Rel^{n-1}`).
5. Summing: `Rel(F;q) = Rel(H;q)^n + n · splitRel(H;q) · Rel(H;q)^{n-1} = cycleBlockRel`.
-/
theorem cycleSubst_edgeFinset_card (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    (cycleSubst H u v n).edgeFinset.card = n * H.edgeFinset.card := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n)))
      (copyEdges H u v huv n (by omega)) := by
    rw [Finset.coe_univ]; exact copyEdges_pairwise_disjoint H u v huv n hn
  rw [cycleSubst_edgeFinset_eq H u v huv n hn, Finset.card_biUnion hdisj]
  simp only [copyEdges, Finset.card_map, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

/-! ### Layer 1: Tuple bijection -/

/-- Extract copy `i`'s H-edge-subset from an F-edge-subset `A`. -/
def tupleOfEdgeSubset (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (A : Finset (Sym2 (CycleSubstVertex n u v))) (i : Fin n) :
    Finset (Sym2 (Fin k)) :=
  H.edgeFinset.filter (fun e => Sym2.map (copyVertex u v n i) e ∈ A)

/-- Assemble an n-tuple of H-edge-subsets into an F-edge-subset. -/
def edgeSubsetOfTuple (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (f : Fin n → Finset (Sym2 (Fin k))) :
    Finset (Sym2 (CycleSubstVertex n u v)) :=
  Finset.biUnion Finset.univ (fun i =>
    (f i).map ⟨Sym2.map (copyVertex u v n i),
      Sym2.map.injective (copyVertex_injective u v huv n hn i)⟩)

/-- Round-trip left: assemble ∘ extract = id. -/
theorem edgeSubsetOfTuple_tupleOfEdgeSubset (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (A : Finset (Sym2 (CycleSubstVertex n u v)))
    (hA : A ∈ (cycleSubst H u v n).edgeFinset.powerset) :
    edgeSubsetOfTuple H u v huv n (by omega) (tupleOfEdgeSubset H u v n (by omega) A) = A := by
  ext e
  simp only [edgeSubsetOfTuple, tupleOfEdgeSubset, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_filter]
  constructor
  · rintro ⟨i, e', ⟨he'_H, he'_A⟩, rfl⟩; exact he'_A
  · intro he
    rw [Finset.mem_powerset] at hA
    rw [cycleSubst_edgeFinset_eq H u v huv n hn] at hA
    have := hA he
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, copyEdges,
      Finset.mem_map, Function.Embedding.coeFn_mk] at this
    obtain ⟨i, e', he', rfl⟩ := this
    exact ⟨i, e', ⟨he', he⟩, rfl⟩

/-- Round-trip right: extract ∘ assemble = id (uses disjointness of copies). -/
theorem tupleOfEdgeSubset_edgeSubsetOfTuple (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (f : Fin n → Finset (Sym2 (Fin k)))
    (hf : ∀ i, f i ∈ H.edgeFinset.powerset) (i : Fin n) :
    tupleOfEdgeSubset H u v n (by omega) (edgeSubsetOfTuple H u v huv n (by omega) f) i = f i := by
  ext e
  simp only [tupleOfEdgeSubset, edgeSubsetOfTuple, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro ⟨_, j, e', he', heq⟩
    -- heq : Sym2.map (copyVertex j) e' = Sym2.map (copyVertex i) e
    -- Since copy edges are disjoint, j must equal i and e' must equal e
    have hinj_i := Sym2.map.injective (copyVertex_injective u v huv n (by omega) i)
    have hinj_j := Sym2.map.injective (copyVertex_injective u v huv n (by omega) j)
    -- The mapped edges are in copyEdges i and copyEdges j respectively
    -- From disjointness: j must equal i (otherwise the mapped edge is in two disjoint sets)
    by_cases hij : j = i
    · subst hij; exact hinj_i heq ▸ he'
    · exfalso
      have hmem_j : Sym2.map (copyVertex u v n j) e' ∈
          copyEdges H u v huv n (by omega) j :=
        Finset.mem_map.mpr ⟨e', Finset.mem_powerset.mp (hf j) he', rfl⟩
      have hmem_i : Sym2.map (copyVertex u v n i) e ∈
          copyEdges H u v huv n (by omega) i :=
        Finset.mem_map.mpr ⟨e, ‹e ∈ H.edgeFinset›, rfl⟩
      rw [heq] at hmem_j
      exact Finset.disjoint_left.mp
        ((copyEdges_pairwise_disjoint H u v huv n hn) (Set.mem_univ j) (Set.mem_univ i) hij)
        hmem_j hmem_i
  · intro he
    exact ⟨Finset.mem_powerset.mp (hf i) he, i, e, he, rfl⟩

/-! ### Layer 2: Weight factorization -/

/-- The cardinality of the assembled edge set is the sum of component cardinalities. -/
theorem edgeSubsetOfTuple_card (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (f : Fin n → Finset (Sym2 (Fin k)))
    (hf : ∀ i, f i ∈ H.edgeFinset.powerset) :
    (edgeSubsetOfTuple H u v huv n (by omega) f).card =
      ∑ i : Fin n, (f i).card := by
  simp only [edgeSubsetOfTuple]
  rw [Finset.card_biUnion]
  · simp [Finset.card_map]
  · -- Pairwise disjoint: subsets of disjoint copy edges are disjoint
    intro i _ j _ hij
    have hdisj := (copyEdges_pairwise_disjoint H u v huv n hn)
      (Set.mem_univ i) (Set.mem_univ j) hij
    exact hdisj.mono
      (Finset.map_subset_map.mpr (Finset.mem_powerset.mp (hf i)))
      (Finset.map_subset_map.mpr (Finset.mem_powerset.mp (hf j)))

/-! ### Layer 3: Connectivity characterization -/

/-- A copy of H "connects" if the subgraph on those edges is connected. -/
private def copyConnects (H : SimpleGraph (Fin k)) (u v : Fin k)
    (B : Finset (Sym2 (Fin k))) : Prop :=
  (SimpleGraph.fromEdgeSet (↑B : Set (Sym2 (Fin k)))).Connected

/-- A copy of H "splits" if u,v are separated into exactly two components. -/
private def copySplits (H : SimpleGraph (Fin k)) (u v : Fin k)
    (B : Finset (Sym2 (Fin k))) : Prop :=
  ¬(SimpleGraph.fromEdgeSet (↑B : Set (Sym2 (Fin k)))).Reachable u v ∧
    ∀ w, (SimpleGraph.fromEdgeSet (↑B : Set (Sym2 (Fin k)))).Reachable u w ∨
         (SimpleGraph.fromEdgeSet (↑B : Set (Sym2 (Fin k)))).Reachable v w

/-- Reachability in a smaller edge set lifts to a larger one. -/
private lemma fromEdgeSet_reachable_mono {V : Type*} {S T : Set (Sym2 V)} (hST : S ⊆ T)
    {x y : V} (h : (SimpleGraph.fromEdgeSet S).Reachable x y) :
    (SimpleGraph.fromEdgeSet T).Reachable x y := by
  exact h.mono (fun a b hadj => by
    rw [SimpleGraph.fromEdgeSet_adj] at hadj ⊢
    exact ⟨hST hadj.1, hadj.2⟩)

/-- Within a single copy, if two H-vertices are reachable in the subgraph fromEdgeSet (f i),
then their images under copyVertex are reachable in fromEdgeSet of the assembled edge set. -/
private lemma copy_reachable_in_assembly (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (f : Fin n → Finset (Sym2 (Fin k))) (i : Fin n) (jx jy : Fin k)
    (hr : (SimpleGraph.fromEdgeSet (↑(f i) : Set (Sym2 (Fin k)))).Reachable jx jy) :
    (SimpleGraph.fromEdgeSet
      (↑(edgeSubsetOfTuple H u v huv n hn f) : Set (Sym2 (CycleSubstVertex n u v)))).Reachable
      (copyVertex u v n i jx) (copyVertex u v n i jy) := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hadj _w ih =>
    by_cases heq : copyVertex u v n i a = copyVertex u v n i b
    · rw [heq]; exact ih
    · -- Extract that s(a,b) ∈ f i from the fromEdgeSet adjacency
      have hadj_mem : s(a, b) ∈ (f i) := by
        have := (SimpleGraph.fromEdgeSet_adj (s := (↑(f i) : Set (Sym2 (Fin k))))).mp hadj
        exact_mod_cast this.1
      have hmapped : s(copyVertex u v n i a, copyVertex u v n i b) ∈
          edgeSubsetOfTuple H u v huv n hn f := by
        simp only [edgeSubsetOfTuple, Finset.mem_biUnion, Finset.mem_univ, true_and,
          Finset.mem_map, Function.Embedding.coeFn_mk]
        exact ⟨i, s(a, b), hadj_mem, Sym2.map_pair_eq _ _ _⟩
      have hadj_G : (SimpleGraph.fromEdgeSet
          (↑(edgeSubsetOfTuple H u v huv n hn f) :
            Set (Sym2 (CycleSubstVertex n u v)))).Adj
          (copyVertex u v n i a) (copyVertex u v n i b) := by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨Finset.mem_coe.mpr hmapped, heq⟩
      exact hadj_G.reachable.trans ih

/-- If an internal vertex is adjacent to some vertex x in the assembled subgraph,
then x is a copyVertex image from the same copy. -/
private lemma internal_adj_of_assembly (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (f : Fin n → Finset (Sym2 (Fin k)))
    (i : Fin n) (j : {j : Fin k // j ≠ u ∧ j ≠ v})
    (x : CycleSubstVertex n u v)
    (hadj : (SimpleGraph.fromEdgeSet
      (↑(edgeSubsetOfTuple H u v huv n hn f) :
        Set (Sym2 (CycleSubstVertex n u v)))).Adj (.internal i j) x) :
    ∃ w : Fin k, x = copyVertex u v n i w ∧ s(j.val, w) ∈ f i := by
  rw [SimpleGraph.fromEdgeSet_adj] at hadj; obtain ⟨hmem, hne⟩ := hadj
  simp only [Finset.mem_coe, edgeSubsetOfTuple, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_map, Function.Embedding.coeFn_mk] at hmem
  obtain ⟨i', e', he', heq⟩ := hmem
  revert he' heq; refine Sym2.ind (fun a b => ?_) e'; intro he' heq
  simp only [Sym2.map_pair_eq] at heq
  -- Helper: if copyVertex i' w = internal i j, then i' = i and w = j.val
  have cv_internal : ∀ w : Fin k, copyVertex u v n i' w = .internal i j →
      i' = i ∧ w = j.val := by
    intro w hcv
    unfold copyVertex at hcv; split_ifs at hcv with h1 h2
    all_goals simp_all [CycleSubstVertex.internal.injEq]
    exact congr_arg Subtype.val hcv.2
  rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨rfl, ha⟩ := cv_internal a h1; subst ha; exact ⟨b, h2.symm, he'⟩
  · obtain ⟨rfl, hb⟩ := cv_internal b h2; subst hb; exact ⟨a, h1.symm, by rwa [Sym2.eq_swap] at he'⟩

/-- 3-way invariant transfer: along a walk from an internal vertex, avoiding one terminal
gives reachability to the OTHER terminal.
If the walk avoids `cycle i` (the u-terminal of copy i), then we get `Hi.Reachable j.val v`. -/
private lemma transfer_avoiding_u (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (f : Fin n → Finset (Sym2 (Fin k)))
    (i : Fin n) (j : {j : Fin k // j ≠ u ∧ j ≠ v}) :
    let G := SimpleGraph.fromEdgeSet
      (↑(edgeSubsetOfTuple H u v huv n hn f) : Set (Sym2 (CycleSubstVertex n u v)))
    let Hi := SimpleGraph.fromEdgeSet (↑(f i) : Set (Sym2 (Fin k)))
    ∀ z₁ z₂ (wk : G.Walk z₁ z₂),
      .cycle i ∉ wk.support →
      ((∃ j' : {j : Fin k // j ≠ u ∧ j ≠ v},
          z₁ = .internal i j' ∧ Hi.Reachable j.val j'.val) ∨
        Hi.Reachable j.val v) →
      ((∃ j' : {j : Fin k // j ≠ u ∧ j ≠ v},
          z₂ = .internal i j' ∧ Hi.Reachable j.val j'.val) ∨
        Hi.Reachable j.val v) := by
  intro G Hi z₁ z₂ wk
  induction wk with
  | nil => intro _ h; exact h
  | @cons a b c hadj wk' ih =>
    intro h_avoid h_Q
    have ha_ne : a ≠ .cycle i := by
      intro heq; exact h_avoid (heq ▸ SimpleGraph.Walk.start_mem_support _)
    have h_avoid' : .cycle i ∉ wk'.support := by
      intro hmem; exact h_avoid (SimpleGraph.Walk.support_subset_support_cons wk' hadj hmem)
    -- Transfer Q from a to b
    have Qb : (∃ j' : {j : Fin k // j ≠ u ∧ j ≠ v},
        b = .internal i j' ∧ Hi.Reachable j.val j'.val) ∨ Hi.Reachable j.val v := by
      rcases h_Q with ⟨j', hj'_eq, hj'_reach⟩ | h_v
      · -- a = internal(i, j'), need to classify b
        obtain ⟨w, hw_eq, hmem_fi⟩ := internal_adj_of_assembly H u v huv n hn f i j' b
          (hj'_eq ▸ hadj)
        by_cases hwu : w = u
        · -- b = copyVertex i u = cycle i. But cycle i ∉ wk'.support, and b is in wk'.support.
          exfalso; apply h_avoid'
          have : .cycle i ∈ wk'.support := by
            have hb_eq : b = .cycle i := by
              rw [hw_eq, hwu]
              unfold copyVertex
              rw [dif_pos rfl]
            rw [← hb_eq]
            exact SimpleGraph.Walk.start_mem_support _
          exact this
        by_cases hwv : w = v
        · -- b = copyVertex i v = cycle (i+1)%n. Get Hi.Reachable j.val v.
          right
          have : Hi.Reachable j'.val w := by
            refine SimpleGraph.Adj.reachable ?_
            rw [SimpleGraph.fromEdgeSet_adj]
            have hmem_swapped : s(j'.val, w) ∈ f i := hmem_fi
            refine ⟨Finset.mem_coe.mpr hmem_swapped, ?_⟩
            intro heq
            apply hadj.ne
            rw [hj'_eq, hw_eq]
            unfold copyVertex; rw [dif_neg (heq ▸ j'.prop.1), dif_neg (heq ▸ j'.prop.2)]
            congr 1; exact Subtype.ext heq
          exact hj'_reach.trans (hwv ▸ this)
        · -- b = internal(i, ⟨w, hwu, hwv⟩). Left disjunct.
          left
          refine ⟨⟨w, hwu, hwv⟩, ?_, ?_⟩
          · rw [hw_eq]; unfold copyVertex; rw [dif_neg hwu, dif_neg hwv]
          · have : Hi.Reachable j'.val w := by
              refine SimpleGraph.Adj.reachable ?_
              rw [SimpleGraph.fromEdgeSet_adj]
              have hmem_swapped : s(j'.val, w) ∈ f i := hmem_fi
              refine ⟨Finset.mem_coe.mpr hmem_swapped, fun heq => ?_⟩
              apply hadj.ne; rw [hj'_eq, hw_eq]
              unfold copyVertex; rw [dif_neg (heq ▸ j'.prop.1), dif_neg (heq ▸ j'.prop.2)]
              congr 1; exact Subtype.ext heq
            exact hj'_reach.trans this
      · right; exact h_v
    exact ih h_avoid' Qb

/-- Similarly: avoiding `cycle (i+1)%n` (the v-terminal) gives `Hi.Reachable j.val u`. -/
private lemma transfer_avoiding_v (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (f : Fin n → Finset (Sym2 (Fin k)))
    (i : Fin n) (j : {j : Fin k // j ≠ u ∧ j ≠ v}) :
    let G := SimpleGraph.fromEdgeSet
      (↑(edgeSubsetOfTuple H u v huv n hn f) : Set (Sym2 (CycleSubstVertex n u v)))
    let Hi := SimpleGraph.fromEdgeSet (↑(f i) : Set (Sym2 (Fin k)))
    ∀ z₁ z₂ (wk : G.Walk z₁ z₂),
      .cycle ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ ∉ wk.support →
      ((∃ j' : {j : Fin k // j ≠ u ∧ j ≠ v},
          z₁ = .internal i j' ∧ Hi.Reachable j.val j'.val) ∨
        Hi.Reachable j.val u) →
      ((∃ j' : {j : Fin k // j ≠ u ∧ j ≠ v},
          z₂ = .internal i j' ∧ Hi.Reachable j.val j'.val) ∨
        Hi.Reachable j.val u) := by
  intro G Hi z₁ z₂ wk
  induction wk with
  | nil => intro _ h; exact h
  | @cons a b c hadj wk' ih =>
    intro h_avoid h_Q
    set ci1 := CycleSubstVertex.cycle ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
    have h_avoid' : ci1 ∉ wk'.support := by
      intro hmem; exact h_avoid (SimpleGraph.Walk.support_subset_support_cons wk' hadj hmem)
    have Qb : (∃ j' : {j : Fin k // j ≠ u ∧ j ≠ v},
        b = .internal i j' ∧ Hi.Reachable j.val j'.val) ∨ Hi.Reachable j.val u := by
      rcases h_Q with ⟨j', hj'_eq, hj'_reach⟩ | h_u
      · obtain ⟨w, hw_eq, hmem_fi⟩ := internal_adj_of_assembly H u v huv n hn f i j' b
          (hj'_eq ▸ hadj)
        by_cases hwv : w = v
        · -- b = copyVertex i v = cycle (i+1)%n. But ci1 ∉ wk'.support.
          exfalso; apply h_avoid'
          have : ci1 ∈ wk'.support := by
            have hb_eq : b = ci1 := by
              rw [hw_eq, hwv]
              unfold copyVertex
              rw [dif_neg (Ne.symm huv), dif_pos rfl]
            rw [← hb_eq]
            exact SimpleGraph.Walk.start_mem_support _
          exact this
        by_cases hwu : w = u
        · right
          have : Hi.Reachable j'.val w := by
            refine SimpleGraph.Adj.reachable ?_
            rw [SimpleGraph.fromEdgeSet_adj]
            have hmem_swapped : s(j'.val, w) ∈ f i := hmem_fi
            refine ⟨Finset.mem_coe.mpr hmem_swapped, ?_⟩
            intro heq
            apply hadj.ne
            rw [hj'_eq, hw_eq]
            unfold copyVertex; rw [dif_neg (heq ▸ j'.prop.1), dif_neg (heq ▸ j'.prop.2)]
            congr 1; exact Subtype.ext heq
          exact hj'_reach.trans (hwu ▸ this)
        · left
          refine ⟨⟨w, hwu, hwv⟩, ?_, ?_⟩
          · rw [hw_eq]; unfold copyVertex; rw [dif_neg hwu, dif_neg hwv]
          · have : Hi.Reachable j'.val w := by
              refine SimpleGraph.Adj.reachable ?_
              rw [SimpleGraph.fromEdgeSet_adj]
              have hmem_swapped : s(j'.val, w) ∈ f i := hmem_fi
              refine ⟨Finset.mem_coe.mpr hmem_swapped, fun heq => ?_⟩
              apply hadj.ne; rw [hj'_eq, hw_eq]
              unfold copyVertex; rw [dif_neg (heq ▸ j'.prop.1), dif_neg (heq ▸ j'.prop.2)]
              congr 1; exact Subtype.ext heq
            exact hj'_reach.trans this
      · right; exact h_u
    exact ih h_avoid' Qb

/-- On a G-path from c_{i} to c_{(i+1)%n}, if copy i splits, the path never visits
an internal vertex of copy i. (Because entering copy i from c_i forces exit through
c_{(i+1)%n} on a path, giving Hi.Reachable u v — contradicting the split.) -/
private lemma path_avoids_split_internals (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (f : Fin n → Finset (Sym2 (Fin k)))
    (i : Fin n) (hsplit : copySplits H u v (f i))
    (p : (SimpleGraph.fromEdgeSet
      (↑(edgeSubsetOfTuple H u v huv n hn f) :
        Set (Sym2 (CycleSubstVertex n u v)))).Walk
      (.cycle i) (.cycle ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
    (hp : p.IsPath)
    (j : {j : Fin k // j ≠ u ∧ j ≠ v}) :
    .internal i j ∉ p.support := by
  let G := SimpleGraph.fromEdgeSet
    (↑(edgeSubsetOfTuple H u v huv n hn f) : Set (Sym2 (CycleSubstVertex n u v)))
  let Hi := SimpleGraph.fromEdgeSet (↑(f i) : Set (Sym2 (Fin k)))
  let ci : CycleSubstVertex n u v := .cycle i
  let ci1 : CycleSubstVertex n u v :=
    .cycle ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
  let vint : CycleSubstVertex n u v := .internal i j
  intro hmem
  -- Split the path at internal(i, j)
  let w₁ := p.takeUntil vint hmem  -- Walk from ci to vint
  let w₂ := p.dropUntil vint hmem  -- Walk from vint to ci1
  -- From take_spec + support_append + nodup: the two halves have disjoint supports
  -- (except at vint)
  have hnodup : p.support.Nodup := (SimpleGraph.Walk.isPath_def p).mp hp
  have hsup : p.support = w₁.support ++ w₂.support.tail := by
    have := p.take_spec hmem
    rw [← this, SimpleGraph.Walk.support_append]
  have hnodup' : (w₁.support ++ w₂.support.tail).Nodup := hsup ▸ hnodup
  have hdisj := (List.nodup_append'.mp hnodup').2.2  -- Disjoint w₁.support w₂.support.tail
  -- ci ∈ w₁.support (start of w₁)
  have hci_w₁ : ci ∈ w₁.support := SimpleGraph.Walk.start_mem_support _
  -- ci ∉ w₂.support: if ci ∈ w₂.support, since ci ≠ vint (cycle ≠ internal),
  -- ci ∈ w₂.support.tail, contradicting disjointness with hci_w₁
  have hci_ne_vint : ci ≠ vint := by simp [ci, vint]
  have hci_not_w₂ : ci ∉ w₂.support := by
    intro hmem₂
    have support_eq : w₂.support = vint :: w₂.support.tail := w₂.support_eq_cons
    rw [support_eq, List.mem_cons] at hmem₂
    obtain h1 | h2 := hmem₂
    · exact hci_ne_vint h1
    · exact hdisj hci_w₁ h2
  -- ci1 ∈ w₂.support (end of w₂)
  have hci1_w₂ : ci1 ∈ w₂.support := SimpleGraph.Walk.end_mem_support _
  -- ci1 ∉ w₁.support: similar argument
  have hci1_ne_vint : ci1 ≠ vint := by simp [ci1, vint]
  have hci1_not_w₁ : ci1 ∉ w₁.support := by
    intro hmem₁
    have support_eq : w₂.support = vint :: w₂.support.tail := w₂.support_eq_cons
    rw [support_eq, List.mem_cons] at hci1_w₂
    obtain h1 | h2 := hci1_w₂
    · exact hci1_ne_vint h1
    · exact hdisj hmem₁ h2
  -- Apply transfer_avoiding_u to w₂: get Hi.Reachable j.val v
  have hreach_v : Hi.Reachable j.val v := by
    have := transfer_avoiding_u H u v huv n hn f i j _ _ w₂ hci_not_w₂
      (Or.inl ⟨j, rfl, Reachable.refl _⟩)
    rcases this with ⟨j', hj'_eq, _⟩ | h
    · exact absurd hj'_eq (by simp [ci1, vint, CycleSubstVertex.internal])
    · exact h
  -- Apply transfer_avoiding_v to w₁.reverse: get Hi.Reachable j.val u
  have hreach_u : Hi.Reachable j.val u := by
    have h_avoid_r : ci1 ∉ w₁.reverse.support := by
      intro h
      rw [SimpleGraph.Walk.support_reverse w₁] at h
      rw [List.mem_reverse] at h
      exact hci1_not_w₁ h
    have := transfer_avoiding_v H u v huv n hn f i j _ _ w₁.reverse h_avoid_r
      (Or.inl ⟨j, rfl, Reachable.refl _⟩)
    rcases this with ⟨j', hj'_eq, _⟩ | h
    · exact absurd hj'_eq (by simp [ci, vint, CycleSubstVertex.internal])
    · exact h
  -- Combine: Hi.Reachable u v
  exact hsplit.1 (hreach_u.symm.trans hreach_v)

/-- Generalized: any path between two cycle vertices avoids internals of any splitting copy.
The proof is the same as `path_avoids_split_internals` — the transfer lemmas don't depend
on the path's endpoints being the copy's terminals. -/
private lemma path_avoids_split_internals_general (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (f : Fin n → Finset (Sym2 (Fin k)))
    (i : Fin n) (hsplit : copySplits H u v (f i))
    (m₁ m₂ : Fin n)
    (p : (SimpleGraph.fromEdgeSet
      (↑(edgeSubsetOfTuple H u v huv n hn f) :
        Set (Sym2 (CycleSubstVertex n u v)))).Walk
      (.cycle m₁) (.cycle m₂))
    (hp : p.IsPath)
    (j : {j : Fin k // j ≠ u ∧ j ≠ v}) :
    .internal i j ∉ p.support := by
  let Hi := SimpleGraph.fromEdgeSet (↑(f i) : Set (Sym2 (Fin k)))
  let ci : CycleSubstVertex n u v := .cycle i
  let ci1 : CycleSubstVertex n u v :=
    .cycle ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
  let vint : CycleSubstVertex n u v := .internal i j
  intro hmem
  let w₁ := p.takeUntil vint hmem
  let w₂ := p.dropUntil vint hmem
  have hnodup : p.support.Nodup := (SimpleGraph.Walk.isPath_def p).mp hp
  have hsup : p.support = w₁.support ++ w₂.support.tail := by
    have := p.take_spec hmem; rw [← this, SimpleGraph.Walk.support_append]
  have hnodup' : (w₁.support ++ w₂.support.tail).Nodup := hsup ▸ hnodup
  have hdisj := (List.nodup_append'.mp hnodup').2.2
  -- Key helper: if x ≠ vint, x can appear in at most one of w₁.support and w₂.support
  have not_both : ∀ x, x ≠ vint → x ∈ w₁.support → x ∉ w₂.support := by
    intro x hne hmem₁ hmem₂
    have : x ∈ w₂.support.tail := by
      rw [w₂.support_eq_cons, List.mem_cons] at hmem₂
      exact hmem₂.resolve_left hne
    exact hdisj hmem₁ this
  have hci_ne : ci ≠ vint := by simp [ci, vint]
  have hci1_ne : ci1 ≠ vint := by simp [ci1, vint]
  -- Get Reachable j.val v: find a half where cycle i is absent, apply transfer_avoiding_u
  have hreach_v : Hi.Reachable j.val v := by
    -- cycle i is in at most one of the halves
    by_cases hci_w₂ : ci ∈ w₂.support
    · -- ci ∈ w₂ → ci ∉ w₁. Apply transfer on w₁.reverse (avoiding ci).
      have hci_not_w₁ : ci ∉ w₁.support := by
        intro h; exact not_both ci hci_ne h hci_w₂
      have h_avoid : ci ∉ w₁.reverse.support := by
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]; exact hci_not_w₁
      have := transfer_avoiding_u H u v huv n hn f i j _ _ w₁.reverse h_avoid
        (Or.inl ⟨j, rfl, Reachable.refl _⟩)
      rcases this with ⟨j', hj'_eq, _⟩ | h
      · exact absurd hj'_eq (by simp [CycleSubstVertex.cycle])
      · exact h
    · -- ci ∉ w₂. Apply transfer on w₂ (avoiding ci).
      have := transfer_avoiding_u H u v huv n hn f i j _ _ w₂ hci_w₂
        (Or.inl ⟨j, rfl, Reachable.refl _⟩)
      rcases this with ⟨j', hj'_eq, _⟩ | h
      · exact absurd hj'_eq (by simp [CycleSubstVertex.cycle])
      · exact h
  -- Get Reachable j.val u: find a half where cycle (i+1)%n is absent, apply transfer_avoiding_v
  have hreach_u : Hi.Reachable j.val u := by
    by_cases hci1_w₁ : ci1 ∈ w₁.support
    · have hci1_not_w₂ : ci1 ∉ w₂.support := by
        intro h; exact not_both ci1 hci1_ne hci1_w₁ h
      have := transfer_avoiding_v H u v huv n hn f i j _ _ w₂ hci1_not_w₂
        (Or.inl ⟨j, rfl, Reachable.refl _⟩)
      rcases this with ⟨j', hj'_eq, _⟩ | h
      · exact absurd hj'_eq (by simp [CycleSubstVertex.cycle])
      · exact h
    · have h_avoid : ci1 ∉ w₁.reverse.support := by
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]; exact hci1_w₁
      have := transfer_avoiding_v H u v huv n hn f i j _ _ w₁.reverse h_avoid
        (Or.inl ⟨j, rfl, Reachable.refl _⟩)
      rcases this with ⟨j', hj'_eq, _⟩ | h
      · exact absurd hj'_eq (by simp [CycleSubstVertex.cycle])
      · exact h
  exact hsplit.1 (hreach_u.symm.trans hreach_v)

/-- **Key characterization**: The cycle-substitution subgraph is connected iff
all copies connect, or exactly one copy splits while the rest connect.
This is the hardest lemma in the proof. -/
private theorem connected_iff_copies (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hH : H.Connected) (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (f : Fin n → Finset (Sym2 (Fin k)))
    (hf : ∀ i, f i ∈ H.edgeFinset.powerset) :
    (SimpleGraph.fromEdgeSet
      (↑(edgeSubsetOfTuple H u v huv n (by omega) f) : Set (Sym2 (CycleSubstVertex n u v)))).Connected ↔
    (∀ i, copyConnects H u v (f i)) ∨
    (∃ j, copySplits H u v (f j) ∧ ∀ i, i ≠ j → copyConnects H u v (f i)) := by
  set G := SimpleGraph.fromEdgeSet
    (↑(edgeSubsetOfTuple H u v huv n (by omega) f) : Set (Sym2 (CycleSubstVertex n u v)))
  -- Helpers
  have hu_eq : ∀ i : Fin n, copyVertex u v n i u = .cycle i := fun i => by simp [copyVertex]
  have hv_eq : ∀ i : Fin n, copyVertex u v n i v =
      .cycle ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := fun i => by
    unfold copyVertex; rw [dif_neg (Ne.symm huv), dif_pos rfl]
  have connects_impl_reach : ∀ i, copyConnects H u v (f i) →
      G.Reachable (.cycle i) (.cycle ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩) := by
    intro i hi; rw [← hu_eq, ← hv_eq]
    exact copy_reachable_in_assembly H u v huv n (by omega) f i u v (hi.preconnected u v)
  -- Forward direction: show that connectivity forces each copy to connect or split,
  -- and at most one copy splits (≥2 splits would disconnect the cycle).
  -- Backward direction: construct reachability from the tuple condition.
  constructor
  · intro hconn
    -- Step 1: Each copy connects or splits.
    -- Key fact: internal(i,w) is only adjacent to copyVertex(i,_) vertices.
    -- So w must be reachable from u or v in fromEdgeSet(f i).
    have each_copy_ok : ∀ i, copyConnects H u v (f i) ∨ copySplits H u v (f i) := by
      intro i
      -- Suffices: ∀ w, fromEdgeSet(f i).Reachable u w ∨ fromEdgeSet(f i).Reachable v w
      -- Then either u reaches v (copyConnects) or not (copySplits)
      set Hi := SimpleGraph.fromEdgeSet (↑(f i) : Set (Sym2 (Fin k)))
      suffices cover : ∀ w : Fin k, Hi.Reachable u w ∨ Hi.Reachable v w by
        by_cases huv_reach : Hi.Reachable u v
        · left
          haveI : Nonempty (Fin k) := ⟨u⟩
          unfold copyConnects
          exact Connected.mk (fun x y => by
            have hux := (cover x).elim id (huv_reach.trans ·)
            have huy := (cover y).elim id (huv_reach.trans ·)
            exact hux.symm.trans huy)
        · right; exact ⟨huv_reach, cover⟩
      -- Prove cover by contradiction: if ∃ w₀ not reachable from u or v,
      -- then internal(i, w₀) is disconnected from cycle i in G.
      intro w
      by_contra h_neg; push_neg at h_neg
      obtain ⟨hnu, hnv⟩ := h_neg
      -- Define S = {w | Hi.Reachable u w ∨ Hi.Reachable v w} (vertices covered by u or v)
      -- w ∉ S. Show copyVertex i w is not G-reachable from cycle i → contradiction.
      -- Strategy: the set {copyVertex i w' | w' ∉ S} is G-closed (no edges leave it)
      -- so if nonempty, it's a disconnected component of G.
      -- The set is nonempty (contains copyVertex i w). And cycle i ∉ this set (u ∈ S).
      -- So G is disconnected, contradicting hconn.
      -- w ≠ u and w ≠ v (since u,v are trivially reachable from themselves)
      have hwu : w ≠ u := fun h => hnu (h ▸ Reachable.refl _)
      have hwv : w ≠ v := fun h => hnv (h ▸ Reachable.refl _)
      -- copyVertex i w = internal i ⟨w, hwu, hwv⟩
      have hcv : copyVertex u v n i w = .internal i ⟨w, hwu, hwv⟩ := by
        unfold copyVertex; rw [dif_neg hwu, dif_neg hwv]
      -- G.Reachable (cycle i) (copyVertex i w) from G.Connected
      obtain ⟨walk⟩ := hconn.preconnected (.cycle i) (copyVertex u v n i w)
      -- Walk induction: show that reaching copyVertex i w requires Hi-reachability
      -- from u or v to w. We prove: for any vertex z on the walk,
      -- if z = copyVertex i w' for some w', then Hi.Reachable u w' ∨ Hi.Reachable v w'.
      -- At the start: z = cycle i = copyVertex i u, so u reachable from u. ✓
      -- At each step: if z → z' via a G-edge, and z = copyVertex i a, z' = copyVertex i b,
      -- then s(a,b) ∈ f i (from the edge structure), so Hi.Adj a b.
      -- But we need z' to be a copyVertex i image, which holds for internal vertices.
      -- The walk might go through cycle vertices from other copies, but must return
      -- to copy i to reach the internal vertex.
      -- Suffices: show the walk's endpoint is reachable from u or v in Hi.
      -- Show: the set S = {w | Hi.Reachable u w ∨ Hi.Reachable v w} covers all of Fin k.
      -- If w ∉ S, then copyVertex i w = internal i ⟨w, hwu, hwv⟩.
      -- By internal_adj_of_assembly, all G-neighbors of this vertex are copyVertex i images.
      -- Those images correspond to Hi-adjacent vertices, which are also ∉ S (by closure).
      -- So the G-component of internal(i,w) is disjoint from cycle i, contradicting G.Connected.
      -- Formal: show ¬G.Reachable (cycle i) (copyVertex i w) → contradiction with hconn
      -- Show Hi.Reachable u w ∨ Hi.Reachable v w → contradiction with hnu ∧ hnv
      suffices Hi.Reachable u w ∨ Hi.Reachable v w from this.elim hnu hnv
      -- Property P(z): if z = copyVertex i w', then Hi.Reachable u w' ∨ Hi.Reachable v w'
      -- P is closed under G-adjacency (by internal_adj_of_assembly)
      -- P holds at cycle i (w' = u → left refl)
      -- By walk induction: P holds at all G-reachable vertices from cycle i
      obtain ⟨walk⟩ := hconn.preconnected (.cycle i) (copyVertex u v n i w)
      suffices step : ∀ (z₁ z₂ : CycleSubstVertex n u v), G.Adj z₁ z₂ →
          (∀ w', z₁ = copyVertex u v n i w' → Hi.Reachable u w' ∨ Hi.Reachable v w') →
          (∀ w', z₂ = copyVertex u v n i w' → Hi.Reachable u w' ∨ Hi.Reachable v w') by
        -- Apply walk induction using the step transfer
        -- Strategy: extract walk, apply Reachable transfer
        -- P at base: cycle i → w' = u → Reachable u u
        -- P step: transfers via `step` lemma
        -- Close by showing G.Reachable implies P via Reachable.rec
        -- Reachable = Nonempty Walk. We prove via the Walk.
        obtain ⟨walk⟩ := hconn.preconnected (.cycle i) (copyVertex u v n i w)
        -- Suffices: P holds for all endpoints of walks from cycle i
        -- Use Walk.concat induction (induction on walk from the end)
        -- Convert: use reversed walk
        have walk_rev := walk.reverse
        -- walk_rev : Walk (copyVertex i w) (cycle i)
        -- Induct on walk_rev (cons adds from the start = our end)
        -- Generalize the end vertex to allow Walk induction
        suffices ∀ z z₂ (wk : G.Walk z z₂), z₂ = .cycle i →
            ∀ w', z = copyVertex u v n i w' → Hi.Reachable u w' ∨ Hi.Reachable v w' from
          (this _ _ walk_rev rfl w rfl).elim (fun h => absurd h hnu) (fun h => absurd h hnv)
        intro z z₂ wk
        induction wk with
        | nil =>
          intro hz₂ w' h
          have hw' : w' = u := (copyVertex_injective u v huv n (by omega) i
            ((hu_eq i).trans (h.symm.trans hz₂).symm)).symm
          subst hw'; left; exact Reachable.refl _
        | @cons a b c hadj _ ih =>
          intro hz₂ w' h
          -- hadj : G.Adj a b, Walk b c, c = cycle i (from hz₂ after cons)
          -- step transfers P from b to a via hadj.symm
          exact step _ _ hadj.symm (fun w'' h' => ih hz₂ w'' h') w' h
      -- Prove the step: P transfers across G-adjacency
      intro z₁ z₂ hadj hz₁ w' hz₂
      by_cases hw'u : w' = u
      · left; exact hw'u ▸ Reachable.refl _
      by_cases hw'v : w' = v
      · right; exact hw'v ▸ Reachable.refl _
      -- w' ≠ u, v → z₂ = internal i ⟨w', ...⟩
      have hz₂_int : z₂ = .internal i ⟨w', hw'u, hw'v⟩ := by
        rw [hz₂]; unfold copyVertex; rw [dif_neg hw'u, dif_neg hw'v]
      obtain ⟨a, hz₁_eq, hmem⟩ := internal_adj_of_assembly H u v huv n (by omega) f i
        ⟨w', hw'u, hw'v⟩ z₁ (hz₂_int ▸ hadj.symm)
      -- hmem : s(w', a) ∈ f i → Hi.Adj a w' (from fromEdgeSet)
      -- fromEdgeSet(f i).Adj a w' from hmem : s(w', a) ∈ f i
      have hadj_Hi : Hi.Reachable a w' := by
        refine SimpleGraph.Adj.reachable ?_
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨?_, ?_⟩
        · exact Finset.mem_coe.mpr (by rwa [Sym2.eq_swap] at hmem)
        · intro heq; exact hadj.ne (hz₁_eq ▸ hz₂_int ▸ by
            show copyVertex u v n i a = .internal i ⟨w', hw'u, hw'v⟩
            unfold copyVertex; rw [dif_neg (heq ▸ hw'u), dif_neg (heq ▸ hw'v)]
            congr 1; exact Subtype.ext heq)
      rcases hz₁ a hz₁_eq with h | h
      · left; exact h.trans hadj_Hi
      · right; exact h.trans hadj_Hi
    -- Step 2: At most one copy splits.
    have at_most_one_split : ∀ i₁ i₂, copySplits H u v (f i₁) →
        copySplits H u v (f i₂) → i₁ = i₂ := by
      intro i₁ i₂ hs₁ hs₂
      by_contra hne
      -- Two splits disconnect the cycle graph. Define a predicate `good` closed under
      -- G-adjacency, True at cycle((i₁+1)%n), False at cycle(i₁). Walk transfer contradicts.
      let Hi₁ := SimpleGraph.fromEdgeSet (↑(f i₁) : Set (Sym2 (Fin k)))
      let Hi₂ := SimpleGraph.fromEdgeSet (↑(f i₂) : Set (Sym2 (Fin k)))
      -- Edge decomposition: every G-edge comes from some copy
      have edge_from_copy : ∀ a b : CycleSubstVertex n u v, G.Adj a b →
          ∃ (j : Fin n) (a' b' : Fin k), s(a', b') ∈ f j ∧
            a = copyVertex u v n j a' ∧ b = copyVertex u v n j b' := by
        intro a b hadj
        rw [SimpleGraph.fromEdgeSet_adj] at hadj
        simp only [Finset.mem_coe, edgeSubsetOfTuple, Finset.mem_biUnion, Finset.mem_univ,
          true_and, Finset.mem_map, Function.Embedding.coeFn_mk] at hadj
        obtain ⟨⟨j, e, he, heq⟩, _⟩ := hadj
        revert he heq; refine Sym2.ind (fun a' b' => ?_) e
        intro he heq; rw [Sym2.map_pair_eq] at heq
        rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨j, a', b', he, h1.symm, h2.symm⟩
        · exact ⟨j, b', a', by rwa [Sym2.eq_swap], h2.symm, h1.symm⟩
      -- Helper: copyVertex to cycle implies terminal
      have cv_cycle : ∀ (j : Fin n) (w : Fin k) (m : Fin n),
          copyVertex u v n j w = .cycle m → w = u ∨ w = v := by
        intro j w m hcv; by_contra hc; push_neg at hc
        simp [copyVertex, hc.1, hc.2] at hcv
      -- onSide: m is on the arc from (i₁+1)%n to i₂ (going forward)
      let onSide : Fin n → Prop := fun m =>
        if i₁.val < i₂.val then i₁.val < m.val ∧ m.val ≤ i₂.val
        else m.val > i₁.val ∨ m.val ≤ i₂.val
      have hne' : i₁.val ≠ i₂.val := Fin.val_ne_of_ne hne
      -- Helper: the .val of ⟨a % n, _⟩ is a % n
      -- (1) onSide ⟨(i₁+1)%n⟩
      have hon_succ : onSide ⟨(i₁.val + 1) % n, Nat.mod_lt _ (by omega)⟩ := by
        -- The Fin.val is (i₁.val + 1) % n
        set m := (⟨(i₁.val + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) with hm_def
        have hm_val : m.val = (i₁.val + 1) % n := rfl
        show if i₁.val < i₂.val then i₁.val < m.val ∧ m.val ≤ i₂.val
          else m.val > i₁.val ∨ m.val ≤ i₂.val
        split_ifs with h
        · rw [hm_val, Nat.mod_eq_of_lt (by omega : i₁.val + 1 < n)]; omega
        · push_neg at h
          by_cases h₁ : i₁.val + 1 < n
          · left; rw [hm_val, Nat.mod_eq_of_lt h₁]; omega
          · right; rw [hm_val, show i₁.val + 1 = n from by omega, Nat.mod_self]; omega
      -- (2) ¬onSide i₁
      have hoff_i₁ : ¬onSide i₁ := by
        show ¬(if i₁.val < i₂.val then _ else _); split_ifs with h <;> push_neg <;> omega
      -- (3) onSide i₂
      have hon_i₂ : onSide i₂ := by
        show if i₁.val < i₂.val then _ else _; split_ifs with h
        · exact ⟨by omega, le_refl _⟩
        · right; exact le_refl _
      -- ¬onSide ⟨(i₂+1)%n⟩
      have hoff_succ_i₂ : ¬onSide ⟨(i₂.val + 1) % n, Nat.mod_lt _ (by omega)⟩ := by
        set m₂ := (⟨(i₂.val + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n)
        show ¬(if i₁.val < i₂.val then i₁.val < m₂.val ∧ m₂.val ≤ i₂.val
              else m₂.val > i₁.val ∨ m₂.val ≤ i₂.val)
        have hm₂_val : m₂.val = (i₂.val + 1) % n := rfl
        split_ifs with h
        · push_neg
          by_cases h₂ : i₂.val + 1 < n
          · rw [hm₂_val, Nat.mod_eq_of_lt h₂]; omega
          · rw [hm₂_val, show i₂.val + 1 = n from by omega, Nat.mod_self]; omega
        · push_neg; push_neg at h
          by_cases h₂ : i₂.val + 1 < n
          · constructor
            · rw [hm₂_val, Nat.mod_eq_of_lt h₂]; omega
            · rw [hm₂_val, Nat.mod_eq_of_lt h₂]; omega
          · omega
      -- (4) For j ≠ i₁, j ≠ i₂: onSide j ↔ onSide ⟨(j+1)%n⟩
      have side_step : ∀ j : Fin n, j ≠ i₁ → j ≠ i₂ →
          (onSide j ↔ onSide ⟨(j.val + 1) % n, Nat.mod_lt _ (by omega)⟩) := by
        intro j hj₁ hj₂
        have hjv₁ : j.val ≠ i₁.val := Fin.val_ne_of_ne hj₁
        have hjv₂ : j.val ≠ i₂.val := Fin.val_ne_of_ne hj₂
        set m := (⟨(j.val + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) with hm_def
        have hm_val : m.val = (j.val + 1) % n := rfl
        show (if i₁.val < i₂.val then i₁.val < j.val ∧ j.val ≤ i₂.val
              else j.val > i₁.val ∨ j.val ≤ i₂.val) ↔
             (if i₁.val < i₂.val then i₁.val < m.val ∧ m.val ≤ i₂.val
              else m.val > i₁.val ∨ m.val ≤ i₂.val)
        by_cases hj_wrap : j.val + 1 < n
        · rw [hm_val, Nat.mod_eq_of_lt hj_wrap]
          split_ifs with h <;> constructor <;> intro hm <;> omega
        · have hj_eq : j.val + 1 = n := by omega
          rw [hm_val, hj_eq, Nat.mod_self]
          split_ifs with h <;> constructor <;> intro hm <;> omega
      -- Define the full predicate
      let good : CycleSubstVertex n u v → Prop := fun z =>
        match z with
        | .cycle m => onSide m
        | .internal j w =>
          if j = i₁ then Hi₁.Reachable v w.val
          else if j = i₂ then Hi₂.Reachable u w.val
          else onSide j
      -- good is closed under G-adjacency: G.Adj a b → good a → good b
      have good_closed : ∀ a b : CycleSubstVertex n u v, G.Adj a b → good a → good b := by
        intro a b hadj hga
        -- Extract copy and vertices from edge
        have hadj' := hadj
        rw [SimpleGraph.fromEdgeSet_adj] at hadj'
        obtain ⟨hmem_set, hne_ab⟩ := hadj'
        simp only [Finset.mem_coe, edgeSubsetOfTuple, Finset.mem_biUnion, Finset.mem_univ,
          true_and, Finset.mem_map, Function.Embedding.coeFn_mk] at hmem_set
        obtain ⟨j, e, he_f, he_map⟩ := hmem_set
        revert he_f he_map; refine Sym2.ind (fun a' b' => ?_) e; intro he_f he_map
        rw [Sym2.map_pair_eq] at he_map
        -- he_map : s(cv j a', cv j b') = s(a, b)
        -- We handle both orientations via a unified helper
        suffices helper : ∀ (x y : Fin k), s(x, y) ∈ f j →
            copyVertex u v n j x = a → copyVertex u v n j y = b → good b by
          rcases Sym2.eq_iff.mp he_map with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact helper a' b' he_f h1 h2
          · exact helper b' a' (by rwa [Sym2.eq_swap]) h2 h1
        clear he_map he_f e a' b'
        intro x y hmem hx_eq hy_eq
        -- Now: s(x,y) ∈ f j, a = cv j x, b = cv j y, good a, need good b
        -- Adjacency in Hi_j
        have mk_adj_j : x ≠ y →
            (SimpleGraph.fromEdgeSet (↑(f j) : Set (Sym2 (Fin k)))).Adj x y := by
          intro hxy; rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨Finset.mem_coe.mpr hmem, hxy⟩
        have hxy_ne : x ≠ y := fun h => hne_ab (hx_eq ▸ hy_eq ▸ congrArg _ h)
        have hadj_j := mk_adj_j hxy_ne
        -- good at copyVertex
        have good_cv_u : ∀ jj : Fin n, good (copyVertex u v n jj u) ↔ onSide jj := by
          intro jj; have : copyVertex u v n jj u = .cycle jj := hu_eq jj
          rw [this]
        have good_cv_v : ∀ jj : Fin n, good (copyVertex u v n jj v) ↔
            onSide ⟨(jj.val + 1) % n, Nat.mod_lt _ (by omega)⟩ := by
          intro jj
          have : copyVertex u v n jj v =
              .cycle ⟨(jj.val + 1) % n, Nat.mod_lt _ (by omega)⟩ := by
            unfold copyVertex; rw [dif_neg (Ne.symm huv), dif_pos rfl]
          rw [this]
        have good_cv_int : ∀ (jj : Fin n) (w : Fin k) (hwu : w ≠ u) (hwv : w ≠ v),
            good (copyVertex u v n jj w) ↔
            (if jj = i₁ then Hi₁.Reachable v w
             else if jj = i₂ then Hi₂.Reachable u w
             else onSide jj) := by
          intro jj w hwu hwv
          have : copyVertex u v n jj w = .internal jj ⟨w, hwu, hwv⟩ := by
            unfold copyVertex; rw [dif_neg hwu, dif_neg hwv]
          rw [this]
        -- Case split on j
        by_cases hj₁ : j = i₁
        · -- Copy i₁. Split at i₁ means ¬Hi₁.Reachable u v.
          -- x options: u, v, or internal. y options: u, v, or internal.
          by_cases hxu : x = u
          · -- a = cycle i₁, good a = onSide i₁ = False
            exfalso; rw [← hx_eq, hxu] at hga; rw [good_cv_u] at hga; exact hoff_i₁ (hj₁ ▸ hga)
          by_cases hxv : x = v
          · -- a = cycle (i₁+1)%n
            by_cases hyu : y = u
            · -- s(v,u) ∈ f i₁ → contradiction
              exfalso; rw [hxv, hyu, hj₁] at hmem
              have : Hi₁.Adj v u := by
                rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨Finset.mem_coe.mpr hmem, Ne.symm huv⟩
              exact hs₁.1 this.reachable.symm
            by_cases hyv : y = v
            · exact absurd (hx_eq.symm.trans (by rw [hxv, hyv]) |>.trans hy_eq) hne_ab
            · -- y is internal. good b = Hi₁.Reachable v y
              rw [← hy_eq, good_cv_int _ _ hyu hyv, if_pos hj₁]
              rw [hxv, hj₁] at hmem hadj_j
              exact hadj_j.reachable
          · -- x is internal. good a = Hi₁.Reachable v x (since j = i₁)
            have hga' : Hi₁.Reachable v x := by
              rw [← hx_eq, good_cv_int _ _ hxu hxv, if_pos hj₁] at hga; exact hga
            by_cases hyu : y = u
            · -- Hi₁.Adj x u and Reachable v x → Reachable v u → Reachable u v → contradiction
              exfalso; rw [hyu, hj₁] at hmem hadj_j
              exact hs₁.1 (hga'.trans hadj_j.reachable |>.symm)
            by_cases hyv : y = v
            · -- b = cycle (i₁+1)%n
              rw [← hy_eq, hyv, hj₁]; exact (good_cv_v i₁).mpr hon_succ
            · -- y is internal
              rw [← hy_eq, good_cv_int _ _ hyu hyv, if_pos hj₁]
              rw [hj₁] at hadj_j
              exact hga'.trans hadj_j.reachable
        by_cases hj₂ : j = i₂
        · -- Copy i₂.
          by_cases hxu : x = u
          · -- a = cycle i₂, good a = onSide i₂
            by_cases hyu : y = u
            · exact absurd (hx_eq.symm.trans (by rw [hxu, hyu]) |>.trans hy_eq) hne_ab
            by_cases hyv : y = v
            · -- s(u,v) ∈ f i₂ → contradiction
              exfalso; rw [hxu, hyv, hj₂] at hmem
              have : Hi₂.Adj u v := by
                rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨Finset.mem_coe.mpr hmem, huv⟩
              exact hs₂.1 this.reachable
            · -- y is internal. good b = Hi₂.Reachable u y
              rw [← hy_eq, good_cv_int _ _ hyu hyv, hj₂, if_neg (Ne.symm hne), if_pos rfl]
              rw [hxu, hj₂] at hmem hadj_j
              exact hadj_j.reachable
          by_cases hxv : x = v
          · -- a = cycle (i₂+1)%n, good a = onSide (i₂+1)%n = False
            exfalso; rw [← hx_eq, hxv, hj₂] at hga
            rw [good_cv_v] at hga; exact hoff_succ_i₂ hga
          · -- x is internal. good a = Hi₂.Reachable u x
            have hga' : Hi₂.Reachable u x := by
              rw [← hx_eq, good_cv_int _ _ hxu hxv] at hga; rw [hj₂, if_neg (Ne.symm hne), if_pos rfl] at hga
              exact hga
            by_cases hyv : y = v
            · -- Hi₂.Adj x v, Reachable u x → Reachable u v → contradiction
              exfalso; rw [hyv, hj₂] at hmem hadj_j
              exact hs₂.1 (hga'.trans hadj_j.reachable)
            by_cases hyu : y = u
            · rw [← hy_eq, hyu, hj₂]; exact (good_cv_u i₂).mpr hon_i₂
            · rw [← hy_eq, good_cv_int _ _ hyu hyv, hj₂, if_neg (Ne.symm hne), if_pos rfl]
              rw [hj₂] at hadj_j; exact hga'.trans hadj_j.reachable
        · -- Copy j ≠ i₁, j ≠ i₂. Good is constant = onSide j on this copy.
          have hside := side_step j hj₁ hj₂
          -- Extract onSide j from good(a)
          have get_side : onSide j := by
            by_cases hxu : x = u
            · rw [← hx_eq, hxu] at hga; rwa [good_cv_u] at hga
            by_cases hxv : x = v
            · rw [← hx_eq, hxv] at hga; rwa [good_cv_v, ← hside] at hga
            · rw [← hx_eq, good_cv_int _ _ hxu hxv, if_neg hj₁, if_neg hj₂] at hga; exact hga
          -- Push to good(b)
          by_cases hyu : y = u
          · rw [← hy_eq, hyu]; exact (good_cv_u j).mpr get_side
          by_cases hyv : y = v
          · rw [← hy_eq, hyv]; exact (good_cv_v j).mpr (hside.mp get_side)
          · rw [← hy_eq, good_cv_int _ _ hyu hyv, if_neg hj₁, if_neg hj₂]; exact get_side
      -- Apply walk induction to derive contradiction
      obtain ⟨walk⟩ := hconn.preconnected
        (.cycle ⟨(i₁.val + 1) % n, Nat.mod_lt _ (by omega)⟩) (.cycle i₁)
      -- Walk from cycle((i₁+1)%n) to cycle(i₁). Transfer good along it.
      suffices ∀ z₁ z₂ (wk : G.Walk z₁ z₂), good z₁ → good z₂ by
        exact hoff_i₁ (this _ _ walk hon_succ)
      intro z₁ z₂ wk
      induction wk with
      | nil => exact id
      | @cons a b c hadj _ ih => intro ha; exact ih (good_closed a b hadj ha)
    -- Combine: all connect, or exactly one splits
    by_cases h : ∀ i, copyConnects H u v (f i)
    · left; exact h
    · push_neg at h; obtain ⟨j, hj⟩ := h
      right; refine ⟨j, (each_copy_ok j).resolve_left hj, fun i hi => ?_⟩
      exact (each_copy_ok i).resolve_right (fun hs => hi (at_most_one_split i j hs
        ((each_copy_ok j).resolve_left hj)))
  · intro h
    haveI : Nonempty (CycleSubstVertex n u v) := ⟨.cycle ⟨0, by omega⟩⟩
    apply Connected.mk; intro x y
    -- Every vertex reachable from cycle 0
    suffices ∀ z, G.Reachable (.cycle ⟨0, by omega⟩) z from (this x).symm.trans (this y)
    -- Each copy connects or splits
    have each_copy : ∀ i, copyConnects H u v (f i) ∨ copySplits H u v (f i) := by
      rcases h with hall | ⟨j, hj, hrest⟩
      · intro i; left; exact hall i
      · intro i; by_cases hij : i = j
        · right; rwa [hij]
        · left; exact hrest i hij
    -- Cycle vertices: all reachable from cycle 0
    have cycle_reach : ∀ m : Fin n, G.Reachable (.cycle ⟨0, by omega⟩) (.cycle m) := by
      rcases h with hall | ⟨j, _, hrest⟩
      · -- All connect: chain 0→1→...→m
        intro ⟨m, hm⟩; induction m with
        | zero => exact Reachable.refl _
        | succ m ih =>
          exact (ih (by omega)).trans (by
            have := connects_impl_reach ⟨m, by omega⟩ (hall ⟨m, by omega⟩)
            rwa [show (⟨(m+1) % n, _⟩ : Fin n) = ⟨m+1, hm⟩ from
              Fin.ext (Nat.mod_eq_of_lt hm)] at this)
      · -- One split at j: chain forward, skipping j by going around
        -- fwd lemma: chain a→a+1→...→b when all copies in [a,b) ≠ j
        have fwd : ∀ a b : ℕ, ∀ (ha : a < n) (hb : b < n),
            a ≤ b → (∀ p, a ≤ p → p < b → p ≠ j.val) →
            G.Reachable (.cycle ⟨a, ha⟩) (.cycle ⟨b, hb⟩) := by
          intro a b ha hb hab hne
          induction b with
          | zero => simp [show a = 0 by omega]
          | succ b ih =>
            if hab' : a = b + 1 then subst hab'; exact Reachable.refl _
            else
              exact (ih (by omega) (by omega) (fun p h1 h2 => hne p h1 (by omega))).trans (by
                have hbj : (⟨b, by omega⟩ : Fin n) ≠ j :=
                  Fin.ne_of_val_ne (hne b (by omega) (by omega))
                have := connects_impl_reach ⟨b, by omega⟩ (hrest _ hbj)
                rwa [show (⟨(b+1) % n, _⟩ : Fin n) = ⟨b+1, hb⟩ from
                  Fin.ext (Nat.mod_eq_of_lt hb)] at this)
        intro ⟨m, hm⟩
        by_cases hjm : j.val < m
        · -- j < m: go backward 0 ← n-1 ← ... ← m (copies m..n-1 all ≠ j since j < m)
          have bwd := fwd m (n-1) hm (by omega) (by omega)
            (fun p h1 h2 => by omega)
          -- bwd: cycle m → cycle (n-1). Then copy (n-1) connects to cycle 0.
          have last := connects_impl_reach ⟨n-1, by omega⟩
            (hrest ⟨n-1, by omega⟩ (by simp [Fin.ext_iff]; omega))
          -- last: cycle (n-1) → cycle ((n-1+1)%n) = cycle 0
          have h0 : ((⟨n - 1, by omega⟩ : Fin n).val + 1) % n = 0 := by
            rw [show (⟨n - 1, by omega⟩ : Fin n).val = n - 1 from rfl,
                show n - 1 + 1 = n from by omega, Nat.mod_self]
          simp only [h0] at last
          exact (bwd.trans last).symm
        · -- j ≥ m: go forward 0→1→...→m (copies 0..m-1 all ≠ j since j ≥ m)
          exact fwd 0 m (by omega) hm (by omega)
            (fun p _ h2 => by omega)
    -- All vertices reachable from cycle 0
    intro z; match z with
    | .cycle m => exact cycle_reach m
    | .internal ⟨m, hm⟩ j' =>
      rcases (each_copy ⟨m, hm⟩) with hc | hs
      · -- Copy m connects: vertex j' reachable from cycle m via u
        have := copy_reachable_in_assembly H u v huv n (by omega) f ⟨m, hm⟩ u j'.val
          (hc.preconnected u j'.val)
        rw [hu_eq, show copyVertex u v n ⟨m, hm⟩ j'.val = .internal ⟨m, hm⟩ j' from by
          unfold copyVertex; rw [dif_neg j'.prop.1, dif_neg j'.prop.2]] at this
        exact (cycle_reach ⟨m, hm⟩).trans this
      · -- Copy m splits: j' reachable from u or v
        rcases hs.2 j'.val with hr | hr
        · have := copy_reachable_in_assembly H u v huv n (by omega) f ⟨m, hm⟩ u j'.val hr
          rw [hu_eq, show copyVertex u v n ⟨m, hm⟩ j'.val = .internal ⟨m, hm⟩ j' from by
            unfold copyVertex; rw [dif_neg j'.prop.1, dif_neg j'.prop.2]] at this
          exact (cycle_reach ⟨m, hm⟩).trans this
        · have := copy_reachable_in_assembly H u v huv n (by omega) f ⟨m, hm⟩ v j'.val hr
          rw [hv_eq, show copyVertex u v n ⟨m, hm⟩ j'.val = .internal ⟨m, hm⟩ j' from by
            unfold copyVertex; rw [dif_neg j'.prop.1, dif_neg j'.prop.2]] at this
          exact (cycle_reach ⟨(m + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩).trans this

/-! ### Layer 4: Assembly -/

/-- The weight of an H-edge-subset B at failure probability q. -/
private def copyWeight (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] (q : ℝ)
    (B : Finset (Sym2 (Fin k))) : ℝ :=
  (1 - q) ^ B.card * q ^ (H.edgeFinset.card - B.card)

/-- The assembled edge set lies in the powerset of cycleSubst's edge finset. -/
private lemma edgeSubsetOfTuple_mem_powerset (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (f : Fin n → Finset (Sym2 (Fin k)))
    (hf : ∀ i, f i ∈ H.edgeFinset.powerset) :
    edgeSubsetOfTuple H u v huv n (by omega) f ∈
      (cycleSubst H u v n).edgeFinset.powerset := by
  rw [Finset.mem_powerset, cycleSubst_edgeFinset_eq H u v huv n hn]
  intro e he
  simp only [edgeSubsetOfTuple, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_map, Function.Embedding.coeFn_mk] at he
  obtain ⟨i, e', he', rfl⟩ := he
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, copyEdges,
    Finset.mem_map, Function.Embedding.coeFn_mk]
  exact ⟨i, e', Finset.mem_powerset.mp (hf i) he', rfl⟩

/-- Weight of the assembled edge set equals the product of copy weights. -/
private lemma weight_factorizes (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (f : Fin n → Finset (Sym2 (Fin k)))
    (hf : ∀ i, f i ∈ H.edgeFinset.powerset) (q : ℝ) :
    (1 - q) ^ (edgeSubsetOfTuple H u v huv n (by omega) f).card *
      q ^ ((cycleSubst H u v n).edgeFinset.card -
        (edgeSubsetOfTuple H u v huv n (by omega) f).card) =
    ∏ i : Fin n, copyWeight H q (f i) := by
  rw [cycleSubst_edgeFinset_card H u v huv n hn,
      edgeSubsetOfTuple_card H u v huv n hn f hf]
  simp only [copyWeight]
  have hle : ∀ i, (f i).card ≤ H.edgeFinset.card :=
    fun i => Finset.card_le_card (Finset.mem_powerset.mp (hf i))
  -- n*|E| - ∑|f i| = ∑(|E| - |f i|)
  have hsub : n * H.edgeFinset.card - ∑ i : Fin n, (f i).card =
      ∑ i : Fin n, (H.edgeFinset.card - (f i).card) := by
    -- Cast to ℤ where subtraction is well-behaved
    have hsum_le : ∑ i : Fin n, (f i).card ≤ n * H.edgeFinset.card := by
      calc ∑ i : Fin n, (f i).card
          ≤ ∑ _ : Fin n, H.edgeFinset.card := Finset.sum_le_sum (fun i _ => hle i)
        _ = n * H.edgeFinset.card := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    zify [hle, hsum_le]
    simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hsub]
  simp_rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]

/-- copySplits implies not copyConnects. -/
private lemma copySplits_not_copyConnects (H : SimpleGraph (Fin k))
    (u v : Fin k) (B : Finset (Sym2 (Fin k))) :
    copySplits H u v B → ¬copyConnects H u v B :=
  fun hsp hco => hsp.1 (hco.preconnected u v)

/-- For indicator sums: ∃-split indicator as sum over j.
When P i → ¬Q i (mutually exclusive), the decomposition holds. -/
private lemma ite_exists_unique_sum {n : ℕ}
    (P Q : Fin n → Prop) [∀ i, Decidable (P i)] [∀ i, Decidable (Q i)]
    (w : Fin n → ℝ) (hPQ : ∀ i, P i → ¬Q i) :
    (if ∃ j, P j ∧ ∀ i, i ≠ j → Q i then ∏ i : Fin n, w i else 0) =
      ∑ j : Fin n, (if P j then w j else 0) *
        (∏ i ∈ Finset.univ.erase j, if Q i then w i else 0) := by
  by_cases h : ∃ j, P j ∧ ∀ i, i ≠ j → Q i
  · obtain ⟨j, hPj, hrest⟩ := h
    rw [if_pos ⟨j, hPj, hrest⟩]
    have : ∑ j' : Fin n, (if P j' then w j' else 0) *
        (∏ i ∈ Finset.univ.erase j', if Q i then w i else 0) =
      (if P j then w j else 0) *
        (∏ i ∈ Finset.univ.erase j, if Q i then w i else 0) := by
      apply Finset.sum_eq_single j
      · intro j' _ hj'
        by_cases hPj' : P j'
        · exact absurd (hrest j' hj') (hPQ j' hPj')
        · simp [hPj']
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [this, if_pos hPj, ← Finset.mul_prod_erase Finset.univ w (Finset.mem_univ j)]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi; rw [Finset.mem_erase] at hi; exact (if_pos (hrest i hi.1)).symm
  · rw [if_neg h]; symm
    apply Finset.sum_eq_zero
    intro j _
    by_cases hPj : P j
    · push_neg at h; obtain ⟨i, hi, hQi⟩ := h j hPj
      rw [show (∏ i ∈ Finset.univ.erase j, if Q i then w i else 0) = 0 from
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩) (if_neg hQi)]
      simp
    · simp [hPj]

/-- Factorization of a sum over piFinset where one coordinate is distinguished.
For `j : Fin n` fixed, the sum of `g(f j) * ∏_{i ≠ j} h(f i)` over all tuples `f`
equals `(∑_B g(B)) * (∑_B h(B))^(n-1)`. -/
private lemma sum_piFinset_split {n : ℕ} {α : Type*}
    (s : Finset α) (g h : α → ℝ) (j : Fin n) :
    ∑ f ∈ Fintype.piFinset (fun _ : Fin n => s),
      g (f j) * ∏ i ∈ Finset.univ.erase j, h (f i) =
    (∑ B ∈ s, g B) * (∑ B ∈ s, h B) ^ (n - 1) := by
  -- Rewrite summand as ∏_i (if i = j then g(f i) else h(f i))
  have hrw : ∀ f : Fin n → α,
      g (f j) * ∏ i ∈ Finset.univ.erase j, h (f i) =
      ∏ i : Fin n, if i = j then g (f i) else h (f i) := by
    intro f
    rw [← Finset.mul_prod_erase Finset.univ (fun i => if i = j then g (f i) else h (f i))
      (Finset.mem_univ j)]
    simp only [if_true]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi; rw [Finset.mem_erase] at hi
    rw [if_neg hi.1]
  simp_rw [hrw]
  -- Apply sum_prod_piFinset: ∑_f ∏_i φ(i, f i) = ∏_i ∑_{a∈s} φ(i, a)
  rw [Finset.sum_prod_piFinset (ι := Fin n) (κ := α) s
    (fun i a => if i = j then g a else h a)]
  -- ∏_i ∑_{a∈s} (if i = j then g(a) else h(a))
  -- = (∑_a g(a)) * ∏_{i≠j} (∑_a h(a))
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [ite_true]
  -- Simplify the remaining factors: for i ≠ j, (if i = j then g else h) = h
  have hsimp : ∀ i ∈ Finset.univ.erase j,
      (∑ a ∈ s, if i = j then g a else h a) = ∑ a ∈ s, h a := by
    intro i hi; rw [Finset.mem_erase] at hi
    apply Finset.sum_congr rfl; intro a _; rw [if_neg hi.1]
  rw [Finset.prod_congr rfl hsimp, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]

set_option maxHeartbeats 1600000 in
-- Bijection transfer, indicator decomposition, and algebraic factorization are computationally heavy.
theorem cycleSubst_reliabilityFun (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hH : H.Connected) (u v : Fin k) (huv : u ≠ v) (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (q : ℝ) :
    (cycleSubst H u v n).reliabilityFun q =
      cycleBlockRel (H.reliabilityFun q) (H.splitRelFun u v q) n := by
  -- Abbreviations
  set F := cycleSubst H u v n with hF_def
  set R := H.reliabilityFun q with hR_def
  set S := H.splitRelFun u v q with hS_def
  set E := H.edgeFinset with hE_def
  set wt := copyWeight H q with hwt_def
  -- Step 1: Transfer the reliability sum from F-edge-subsets to n-tuples of H-edge-subsets
  -- using the bijection edgeSubsetOfTuple / tupleOfEdgeSubset.
  have step1 : F.reliabilityFun q =
      ∑ f ∈ Fintype.piFinset (fun _ : Fin n => E.powerset),
        if (SimpleGraph.fromEdgeSet
          (↑(edgeSubsetOfTuple H u v huv n (by omega) f) :
            Set (Sym2 (CycleSubstVertex n u v)))).Connected
        then ∏ i : Fin n, wt (f i) else 0 := by
    simp only [SimpleGraph.reliabilityFun]
    -- The bijection goes: powerset → piFinset (via tupleOfEdgeSubset)
    --                      piFinset → powerset (via edgeSubsetOfTuple)
    apply Finset.sum_nbij'
      (fun A => tupleOfEdgeSubset H u v n (by omega) A)
      (fun f => edgeSubsetOfTuple H u v huv n (by omega) f)
    · -- Forward: powerset → piFinset
      intro A hA
      rw [Fintype.mem_piFinset]; intro i
      rw [Finset.mem_powerset]; intro e he
      simp only [tupleOfEdgeSubset, Finset.mem_filter] at he
      exact he.1
    · -- Backward: piFinset → powerset
      intro f hf
      rw [Fintype.mem_piFinset] at hf
      exact edgeSubsetOfTuple_mem_powerset H u v huv n hn f hf
    · -- Left inverse: tupleOf ∘ edgeSubsetOf = id on piFinset
      intro A hA
      exact edgeSubsetOfTuple_tupleOfEdgeSubset H u v huv n hn A hA
    · -- Right inverse: edgeSubsetOf ∘ tupleOf = id on powerset
      intro f hf
      rw [Fintype.mem_piFinset] at hf
      funext i
      exact tupleOfEdgeSubset_edgeSubsetOfTuple H u v huv n hn f hf i
    · -- Values agree: indicator and weight match
      intro A hA
      set f := tupleOfEdgeSubset H u v n (by omega) A with hf_def
      have hround := edgeSubsetOfTuple_tupleOfEdgeSubset H u v huv n hn A hA
      -- The tuple satisfies the powerset condition
      have hfpow : ∀ i, f i ∈ E.powerset := by
        intro i; rw [Finset.mem_powerset]; intro e he
        simp only [hf_def, tupleOfEdgeSubset, Finset.mem_filter] at he; exact he.1
      -- After round-trip: edgeSubsetOfTuple f = A
      -- So connectivity and weight match
      conv_rhs => rw [show edgeSubsetOfTuple H u v huv n (by omega) f = A from hround]
      congr 1
      -- Weight factorization: (1-q)^|A| * q^(|E_F|-|A|) = ∏ wt (f i)
      have := weight_factorizes H u v huv n hn f hfpow q
      rw [hround] at this
      exact this
  -- Step 2: Use connected_iff_copies to split the indicator into two disjoint cases.
  have step2 : ∀ f ∈ Fintype.piFinset (fun _ : Fin n => E.powerset),
      (if (SimpleGraph.fromEdgeSet
        (↑(edgeSubsetOfTuple H u v huv n (by omega) f) :
          Set (Sym2 (CycleSubstVertex n u v)))).Connected
      then ∏ i : Fin n, wt (f i) else 0) =
      (if ∀ i, copyConnects H u v (f i) then ∏ i : Fin n, wt (f i) else 0) +
      (if ∃ j, copySplits H u v (f j) ∧ ∀ i, i ≠ j → copyConnects H u v (f i)
       then ∏ i : Fin n, wt (f i) else 0) := by
    intro f hf
    rw [Fintype.mem_piFinset] at hf
    rw [connected_iff_copies H hH u v huv n hn f hf]
    -- The two cases (all connect) and (one splits, rest connect) are mutually exclusive
    by_cases hall : (∀ i, copyConnects H u v (f i)) ∨
        ∃ j, copySplits H u v (f j) ∧ ∀ i, i ≠ j → copyConnects H u v (f i)
    · rw [if_pos hall]
      rcases hall with h1 | h2
      · rw [if_pos h1]
        -- If all connect, then no copy splits (copySplits → ¬copyConnects)
        have h2' : ¬∃ j, copySplits H u v (f j) ∧ ∀ i, i ≠ j → copyConnects H u v (f i) := by
          rintro ⟨j, hj, _⟩; exact (copySplits_not_copyConnects H u v _ hj) (h1 j)
        rw [if_neg h2']; ring
      · rw [if_pos h2]
        -- If one splits, not all connect
        have : ¬∀ i, copyConnects H u v (f i) := by
          obtain ⟨j, hj, _⟩ := h2
          intro h; exact (copySplits_not_copyConnects H u v _ hj) (h j)
        rw [if_neg this]; ring
    · rw [if_neg hall]
      have ⟨h1, h2⟩ := not_or.mp hall
      rw [if_neg h1, if_neg h2]; ring
  -- Step 3: Split the sum and compute each part
  rw [step1]
  conv_lhs => rw [Finset.sum_congr rfl step2, Finset.sum_add_distrib]
  -- Step 3a: The "all connect" sum equals R^n
  -- When all copies connect, the indicator factors as a product over copies,
  -- and ∑_{tuples} ∏ factors = ∏ (∑ factor) = R^n.
  have all_connect_sum :
      ∑ f ∈ Fintype.piFinset (fun _ : Fin n => E.powerset),
        (if ∀ i, copyConnects H u v (f i) then ∏ i : Fin n, wt (f i) else 0) =
      R ^ n := by
    -- Use sum_pow' to directly get R^n
    -- R = ∑ B ∈ E.powerset, if copyConnects H u v B then wt B else 0
    -- R^n = ∑ f ∈ piFinset ..., ∏ i, (if copyConnects (f i) then wt (f i) else 0)
    -- But ∏ (if P i then w i else 0) = if (∀ i, P i) then ∏ w else 0
    -- So R^n = ∑ f, (if ∀ i, copyConnects (f i) then ∏ wt else 0) (*)
    -- This is exactly the LHS.
    -- Strategy: show LHS = R^n directly.
    -- First show R = ∑ B ∈ E.powerset, (if copyConnects B then wt B else 0)
    have hR_eq : R = ∑ B ∈ E.powerset,
        if copyConnects H u v B then wt B else 0 := by
      simp only [hR_def, SimpleGraph.reliabilityFun, copyWeight, copyConnects, hE_def, hwt_def]
    -- Then R^n = ∑_f ∏_i (if copyConnects (f i) then wt (f i) else 0)
    rw [hR_eq, Finset.sum_pow']
    -- Now need: ∑_f ∏_i (if conn then wt else 0) = ∑_f (if ∀ i, conn then ∏ wt else 0)
    apply Finset.sum_congr rfl
    intro f _
    -- ∏ (if P then w else 0) = if (∀ P) then ∏ w else 0
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, true_implies]
  -- Step 3b: The "one splits" sum equals n * S * R^(n-1)
  -- One copy splits, rest connect. By symmetry all j-terms are equal = S * R^(n-1).
  have one_splits_sum :
      ∑ f ∈ Fintype.piFinset (fun _ : Fin n => E.powerset),
        (if ∃ j, copySplits H u v (f j) ∧ ∀ i, i ≠ j → copyConnects H u v (f i)
         then ∏ i : Fin n, wt (f i) else 0) =
      ↑n * S * R ^ (n - 1) := by
    -- copySplits → ¬copyConnects
    have hPQ : ∀ (B : Finset (Sym2 (Fin k))),
        copySplits H u v B → ¬copyConnects H u v B :=
      fun B hsp hco => hsp.1 (hco.preconnected u v)
    -- Decompose using ite_exists_unique_sum for each f
    have hrw : ∀ f : Fin n → Finset (Sym2 (Fin k)),
        (if ∃ j, copySplits H u v (f j) ∧ ∀ i, i ≠ j → copyConnects H u v (f i)
         then ∏ i : Fin n, wt (f i) else (0 : ℝ)) =
        ∑ j : Fin n, (if copySplits H u v (f j) then wt (f j) else 0) *
          (∏ i ∈ Finset.univ.erase j,
            if copyConnects H u v (f i) then wt (f i) else 0) := by
      intro f
      exact ite_exists_unique_sum
        (fun i => copySplits H u v (f i))
        (fun i => copyConnects H u v (f i))
        (fun i => wt (f i))
        (fun i => hPQ (f i))
    simp_rw [hrw]
    -- Swap sums: ∑_f ∑_j = ∑_j ∑_f
    rw [Finset.sum_comm]
    -- Each j-term factors via sum_piFinset_split
    have hS_eq : S = ∑ B ∈ E.powerset,
        if copySplits H u v B then wt B else 0 := by
      simp only [hS_def, SimpleGraph.splitRelFun, copySplits, copyWeight, hE_def, hwt_def]
      congr 1; ext B; congr 1
    have hR_eq : R = ∑ B ∈ E.powerset,
        if copyConnects H u v B then wt B else 0 := by
      simp only [hR_def, SimpleGraph.reliabilityFun, copyWeight, copyConnects, hE_def, hwt_def]
    conv_lhs =>
      arg 2; ext j
      rw [show ∑ f ∈ Fintype.piFinset (fun _ : Fin n => E.powerset),
          (if copySplits H u v (f j) then wt (f j) else 0) *
          (∏ i ∈ Finset.univ.erase j,
            if copyConnects H u v (f i) then wt (f i) else 0) =
        S * R ^ (n - 1) from by
          rw [sum_piFinset_split E.powerset
            (fun B => if copySplits H u v B then wt B else 0)
            (fun B => if copyConnects H u v B then wt B else 0)
            j]
          rw [← hS_eq, ← hR_eq]]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  -- Final assembly: R^n + n * S * R^(n-1) = cycleBlockRel R S n
  unfold cycleBlockRel
  linarith [all_connect_sum, one_splits_sum]

end
