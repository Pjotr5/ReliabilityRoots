/-
Copyright (c) 2026 Pjotr Buys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys
-/
import ReliabilityRoots.Defs
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Lemma 2.1: Reliability of complete graphs converges to 1

For `|q| < 1`, `Rel(Kₙ; q) → 1` as `n → ∞`.
-/

open SimpleGraph Filter Set Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Helper lemmas for the recursion identity -/

/-- The total weight over all edge subsets of a graph equals 1 (binomial theorem):
    `∑_{A ⊆ E} (1-q)^|A| · q^{|E|-|A|} = ((1-q)+q)^|E| = 1`. -/
lemma total_weight_eq_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) :
    ∑ A ∈ G.edgeFinset.powerset,
      (1 - q) ^ A.card * q ^ (G.edgeFinset.card - A.card) = 1 := by
  rw [Finset.sum_powerset_apply_card
    (f := fun m => (1 - q) ^ m * q ^ (G.edgeFinset.card - m))]
  simp only [nsmul_eq_mul]
  conv_rhs => rw [show (1 : ℝ) = ((1 - q) + q) ^ G.edgeFinset.card from by ring]
  rw [add_pow]
  congr 1; ext m; ring

/-- The reliability equals 1 minus the contribution from disconnected edge subsets. -/
lemma reliabilityFun_eq_one_sub_disconnected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) :
    G.reliabilityFun q =
      1 - ∑ A ∈ G.edgeFinset.powerset,
        (if ¬(SimpleGraph.fromEdgeSet (↑A : Set (Sym2 V))).Connected then
          (1 - q) ^ A.card * q ^ (G.edgeFinset.card - A.card)
        else 0) := by
  simp only [SimpleGraph.reliabilityFun]
  have htotal := total_weight_eq_one G q
  suffices h :
    (∑ A ∈ G.edgeFinset.powerset,
      (if (SimpleGraph.fromEdgeSet (↑A : Set (Sym2 V))).Connected then
        (1 - q) ^ A.card * q ^ (G.edgeFinset.card - A.card) else 0)) +
    (∑ A ∈ G.edgeFinset.powerset,
      (if ¬(SimpleGraph.fromEdgeSet (↑A : Set (Sym2 V))).Connected then
        (1 - q) ^ A.card * q ^ (G.edgeFinset.card - A.card) else 0)) = 1 by linarith
  rw [← Finset.sum_add_distrib]
  trans (∑ A ∈ G.edgeFinset.powerset, (1 - q) ^ A.card * q ^ (G.edgeFinset.card - A.card))
  · apply Finset.sum_congr rfl; intro A _
    by_cases h : (SimpleGraph.fromEdgeSet (↑A : Set (Sym2 V))).Connected
    · rw [if_pos h, if_neg (not_not.mpr h), add_zero]
    · rw [if_neg h, if_pos h, zero_add]
  · exact htotal

/-! ### Step A: Component of vertex 0 -/

/-- The component of vertex `0` in `fromEdgeSet A`: the set of vertices reachable from `0`. -/
def componentOfZero {n : ℕ} (hn : 1 ≤ n)
    (A : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter fun v =>
    (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Reachable ⟨0, by omega⟩ v

/-- Vertex `0` is always in its own component. -/
lemma zero_mem_componentOfZero {n : ℕ} (hn : 1 ≤ n)
    (A : Finset (Sym2 (Fin n))) :
    (⟨0, by omega⟩ : Fin n) ∈ componentOfZero hn A := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact @Reachable.refl _ (fromEdgeSet (↑A : Set (Sym2 (Fin n)))) _

/-- For `K_n`, `fromEdgeSet A` is connected iff the component of `0` is all of `Fin n`. -/
lemma connected_iff_componentOfZero_eq_univ {n : ℕ} (hn : 1 ≤ n)
    (A : Finset (Sym2 (Fin n))) :
    (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Connected ↔
    componentOfZero hn A = Finset.univ := by
  constructor
  · intro hconn
    ext v; constructor
    · exact fun _ => Finset.mem_univ v
    · exact fun _ => Finset.mem_filter.mpr
        ⟨Finset.mem_univ v, hconn.preconnected ⟨0, by omega⟩ v⟩
  · intro heq
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    refine Connected.mk fun u v => ?_
    have hu := (Finset.mem_filter.mp
      (show u ∈ componentOfZero hn A from heq ▸ Finset.mem_univ u)).2
    have hv := (Finset.mem_filter.mp
      (show v ∈ componentOfZero hn A from heq ▸ Finset.mem_univ v)).2
    exact hu.symm.trans hv

/-! ### Step B: Fiber characterization -/

/-- `C(A) = S` iff (a) no cross-edge of `S` is in `A` and (b) `A` is connected on `S`.
    Here "connected on `S`" means every vertex of `S` is reachable from `0` using only
    edges of `A` with both endpoints in `S` (see blueprint Definition 3). -/
private lemma componentOfZero_eq_iff {n : ℕ} (hn : 1 ≤ n)
    (A : Finset (Sym2 (Fin n)))
    (S : Finset (Fin n)) (hS0 : (⟨0, by omega⟩ : Fin n) ∈ S) (hSn : S.card < n) :
    componentOfZero hn A = S ↔
    (∀ e ∈ A, ∀ u ∈ S, ∀ v ∉ S, e ≠ s(u, v)) ∧
    (∀ v ∈ S, (fromEdgeSet (↑(A.filter (fun e =>
      ∀ u₁ u₂, e = s(u₁, u₂) → u₁ ∈ S ∧ u₂ ∈ S)) :
      Set (Sym2 (Fin n)))).Reachable ⟨0, by omega⟩ v) := by
  set zero : Fin n := ⟨0, by omega⟩
  set A_S := A.filter (fun e => ∀ u₁ u₂, e = s(u₁, u₂) → u₁ ∈ S ∧ u₂ ∈ S)
  -- Helper: no cross-edges implies S is closed under adjacency in fromEdgeSet ↑A
  have adj_closed (ha : ∀ e ∈ A, ∀ u ∈ S, ∀ v ∉ S, e ≠ s(u, v))
      (u w : Fin n) (hadj : (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Adj u w)
      (hu : u ∈ S) : w ∈ S := by
    by_contra hw
    rw [fromEdgeSet_adj] at hadj
    exact ha _ (Finset.mem_coe.mp hadj.1) u hu w hw rfl
  -- Helper: adjacency between S-vertices lifts from fromEdgeSet ↑A to fromEdgeSet ↑A_S
  have adj_lift (u w : Fin n) (hu : u ∈ S) (hw : w ∈ S)
      (hadj : (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Adj u w) :
      (fromEdgeSet (↑A_S : Set (Sym2 (Fin n)))).Adj u w := by
    rw [fromEdgeSet_adj] at hadj ⊢
    exact ⟨Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hadj.1,
      fun u₁ u₂ he => by
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hu, hw⟩
        · exact ⟨hw, hu⟩⟩), hadj.2⟩
  -- Helper: fromEdgeSet ↑A_S ≤ fromEdgeSet ↑A
  have hle : fromEdgeSet (↑A_S : Set (Sym2 (Fin n))) ≤
      fromEdgeSet (↑A : Set (Sym2 (Fin n))) :=
    fromEdgeSet_mono (fun e he =>
      Finset.mem_coe.mpr (Finset.mem_of_mem_filter _ (Finset.mem_coe.mp he)))
  -- Helper: walk in G with start in S stays in S (and lifts to G_S)
  have walk_in_S (ha : ∀ e ∈ A, ∀ u ∈ S, ∀ v ∉ S, e ≠ s(u, v)) :
      ∀ (a b : Fin n), (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Walk a b →
      a ∈ S → b ∈ S ∧ (fromEdgeSet (↑A_S : Set (Sym2 (Fin n)))).Reachable a b := by
    intro a b walk ha_S
    induction walk with
    | nil => exact ⟨ha_S, @Reachable.refl _ (fromEdgeSet _) _⟩
    | @cons x y z hadj _ ih =>
      have hy_S := adj_closed ha x y hadj ha_S
      obtain ⟨hz_S, hreach⟩ := ih hy_S
      exact ⟨hz_S, (adj_lift x y ha_S hy_S hadj).reachable.trans hreach⟩
  constructor
  · -- Forward: C(A) = S → (a) ∧ (b)
    intro heq
    have ha : ∀ e ∈ A, ∀ u ∈ S, ∀ v ∉ S, e ≠ s(u, v) := by
      intro e he u hu v hv heqe; apply hv; rw [← heq]
      have hu_r := (Finset.mem_filter.mp (heq ▸ hu : u ∈ componentOfZero hn A)).2
      have : (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Adj u v := by
        rw [fromEdgeSet_adj]; exact ⟨Finset.mem_coe.mpr (heqe ▸ he), fun h => hv (h ▸ hu)⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu_r.trans this.reachable⟩
    refine ⟨ha, fun v hv => ?_⟩
    obtain ⟨walk⟩ := (Finset.mem_filter.mp (heq ▸ hv : v ∈ componentOfZero hn A)).2
    exact (walk_in_S ha zero v walk hS0).2
  · -- Backward: (a) ∧ (b) → C(A) = S
    intro ⟨ha, hb⟩
    apply Finset.Subset.antisymm
    · -- C(A) ⊆ S
      intro v hv
      obtain ⟨walk⟩ := (Finset.mem_filter.mp hv).2
      exact (walk_in_S ha zero v walk hS0).1
    · -- S ⊆ C(A)
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hb v hv).mono hle⟩

/-! ### Step C: Edge decomposition and fiber sum -/

/-- For complete graphs, reliability is invariant under equivalence of vertex types. -/
private lemma reliabilityFun_equiv {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (q : ℝ) :
    (⊤ : SimpleGraph α).reliabilityFun q =
    (⊤ : SimpleGraph β).reliabilityFun q := by
  simp only [SimpleGraph.reliabilityFun]
  let f := e.toEmbedding.sym2Map
  let g := e.symm.toEmbedding.sym2Map
  -- Helper: edge membership transfers
  have hmem_fwd (y : Sym2 α) (hy : y ∈ (⊤ : SimpleGraph α).edgeFinset) :
      f y ∈ (⊤ : SimpleGraph β).edgeFinset := by
    rw [mem_edgeFinset, edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet] at hy ⊢
    exact mt (Sym2.isDiag_map e.injective).mp hy
  have hmem_bwd (y : Sym2 β) (hy : y ∈ (⊤ : SimpleGraph β).edgeFinset) :
      g y ∈ (⊤ : SimpleGraph α).edgeFinset := by
    rw [mem_edgeFinset, edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet] at hy ⊢
    exact mt (Sym2.isDiag_map e.symm.injective).mp hy
  apply Finset.sum_nbij' (fun A => A.map f) (fun B => B.map g)
  · -- forward maps into powerset
    intro A hA; rw [Finset.mem_powerset] at hA ⊢
    exact fun x hx => by
      rw [Finset.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact hmem_fwd y (hA hy)
  · -- backward maps into powerset
    intro B hB; rw [Finset.mem_powerset] at hB ⊢
    exact fun x hx => by
      rw [Finset.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact hmem_bwd y (hB hy)
  · -- left inverse
    intro A _; ext x
    simp only [Finset.mem_map, Function.Embedding.sym2Map_apply, f, g, Sym2.map_map]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa [Sym2.map_map] using hz
    · intro hx; exact ⟨f x, ⟨x, hx, rfl⟩, by simp [f, g, Sym2.map_map]⟩
  · -- right inverse
    intro B _; ext x
    simp only [Finset.mem_map, Function.Embedding.sym2Map_apply, f, g, Sym2.map_map]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa [Sym2.map_map] using hz
    · intro hx; exact ⟨g x, ⟨x, hx, rfl⟩, by simp [f, g, Sym2.map_map]⟩
  · -- summands equal
    intro A hA
    have hiso : (fromEdgeSet (↑A : Set (Sym2 α))) ≃g
        (fromEdgeSet (↑(A.map f) : Set (Sym2 β))) := by
      refine ⟨e, ?_⟩; intro a b
      rw [fromEdgeSet_adj, fromEdgeSet_adj]
      constructor
      · -- Adj (e a) (e b) → Adj a b
        intro ⟨hmem, hne⟩
        refine ⟨?_, e.injective.ne_iff.mp hne⟩
        rw [Finset.coe_map, Set.mem_image] at hmem
        obtain ⟨x, hx, hfx⟩ := hmem
        have : x = s(a, b) := by
          apply Sym2.map.injective e.injective
          rw [Sym2.map_pair_eq, show Sym2.map (⇑e) x = f x from rfl, hfx]
        rwa [this] at hx
      · -- Adj a b → Adj (e a) (e b)
        intro ⟨hmem, hne⟩
        refine ⟨?_, e.injective.ne hne⟩
        rw [Finset.coe_map, Set.mem_image]
        exact ⟨s(a, b), hmem, by simp [f, Function.Embedding.sym2Map_apply, Sym2.map_pair_eq]⟩
    split_ifs with h1 h2 h2
    · simp only [Finset.card_map, card_edgeFinset_top_eq_card_choose_two,
        Fintype.card_congr e]
    · exact absurd (hiso.connected_iff.mp h1) h2
    · exact absurd (hiso.connected_iff.mpr h2) h1
    · rfl

set_option maxHeartbeats 400000 in
/-- Helper: the reliability sum over a predicate-filtered edge set equals the reliability
    of the complete graph on `(Finset.univ.filter P).card` vertices. -/
private lemma rel_sum_of_predicate {n : ℕ} (q : ℝ)
    (P : Fin n → Prop) [DecidablePred P]
    (root : Fin n) (hroot : P root)
    (E_P : Finset (Sym2 (Fin n)))
    (hE_P : E_P = (⊤ : SimpleGraph (Fin n)).edgeFinset.filter
      (fun e => ∀ u v, e = s(u, v) → P u ∧ P v)) :
    (∑ B ∈ E_P.powerset.filter (fun B : Finset (Sym2 (Fin n)) =>
        ∀ v, P v → (fromEdgeSet (↑B : Set (Sym2 (Fin n)))).Reachable root v),
      (1 - q) ^ B.card * q ^ (E_P.card - B.card)) =
    (⊤ : SimpleGraph (Fin (Finset.univ.filter P).card)).reliabilityFun q := by
  rw [← reliabilityFun_equiv
    ((Fintype.equivFin {v : Fin n // P v}).trans
      (finCongr (by simp [Fintype.card_subtype])))]
  set emb := (Function.Embedding.subtype P).sym2Map
  set E_sub := (⊤ : SimpleGraph {v : Fin n // P v}).edgeFinset
  have hE_P_eq : E_P = E_sub.map emb := by
    ext e; constructor
    · intro he; have ⟨he_E, he_P⟩ := Finset.mem_filter.mp (hE_P ▸ he)
      induction e using Sym2.inductionOn with
      | _ a b =>
        have ⟨ha, hb⟩ := he_P a b rfl
        have hab : a ≠ b := by
          intro h; subst h; simp [edgeFinset_top, Set.mem_toFinset, Sym2.mem_diagSet] at he_E
        exact Finset.mem_map.mpr ⟨s(⟨a, ha⟩, ⟨b, hb⟩),
          by rw [mem_edgeFinset, mem_edgeSet, top_adj, ne_eq, Subtype.mk.injEq]; exact hab,
          Sym2.eq_iff.mpr (Or.inl ⟨rfl, rfl⟩)⟩
    · intro he; rw [Finset.mem_map] at he; obtain ⟨x, hx, hxe⟩ := he
      induction x using Sym2.inductionOn with
      | _ a b =>
        simp only [emb, Function.Embedding.sym2Map_apply, Sym2.map_pair_eq] at hxe; subst hxe
        have hne : a ≠ b := by
          intro h; rw [mem_edgeFinset, mem_edgeSet, top_adj] at hx; exact hx h
        have hadj : (a : Fin n) ≠ b := fun h => hne (Subtype.ext h)
        rw [hE_P]; exact Finset.mem_filter.mpr ⟨by
          simp [edgeFinset_top, Set.mem_toFinset, Sym2.mem_diagSet, hadj],
          fun u v huv => by
            rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨a.2, b.2⟩
            · exact ⟨b.2, a.2⟩⟩
  unfold SimpleGraph.reliabilityFun; rw [← Finset.sum_filter, hE_P_eq]
  symm
  apply Finset.sum_nbij' (fun A => A.map emb)
    (fun B => B.preimage emb emb.injective.injOn)
  · -- forward: Connected on subtype → reachability on Fin n
    intro A hA; rw [Finset.mem_filter] at hA ⊢
    refine ⟨Finset.mem_powerset.mpr (Finset.map_subset_map.mpr (Finset.mem_powerset.mp hA.1)),
      fun v hv => ?_⟩
    obtain ⟨walk⟩ := hA.2.preconnected ⟨root, hroot⟩ ⟨v, hv⟩
    suffices h : ∀ (a b : {v : Fin n // P v}),
        (fromEdgeSet (↑A : Set (Sym2 {v : Fin n // P v}))).Walk a b →
        (fromEdgeSet (↑(A.map emb) : Set (Sym2 (Fin n)))).Reachable ↑a ↑b from h _ _ walk
    intro a b w; induction w with
    | nil => exact @Reachable.refl _ _ _
    | @cons u v _ hadj _ ih =>
      rw [fromEdgeSet_adj] at hadj
      have : (fromEdgeSet (↑(A.map emb) : Set (Sym2 (Fin n)))).Adj ↑u ↑v := by
        rw [fromEdgeSet_adj]; exact ⟨Finset.mem_coe.mpr
          (Finset.mem_map_of_mem emb (Finset.mem_coe.mp hadj.1)),
          Subtype.val_injective.ne hadj.2⟩
      exact this.reachable.trans ih
  · -- backward: reachability on Fin n → Connected on subtype
    intro B hB; rw [Finset.mem_filter] at hB ⊢
    refine ⟨Finset.mem_powerset.mpr (fun x hx => ?_), ?_⟩
    · rw [Finset.mem_preimage] at hx
      have hmem := (Finset.mem_powerset.mp hB.1) hx
      obtain ⟨y, hy, hye⟩ := Finset.mem_map.mp hmem
      exact emb.injective hye ▸ hy
    · haveI : Nonempty {v : Fin n // P v} := ⟨⟨root, hroot⟩⟩
      refine Connected.mk fun ⟨u, hu⟩ ⟨v, hv⟩ => ?_
      obtain ⟨wu⟩ := hB.2 u hu
      obtain ⟨wv⟩ := hB.2 v hv
      set G_pre := fromEdgeSet (↑(B.preimage emb emb.injective.injOn) :
        Set (Sym2 {v : Fin n // P v}))
      suffices h : ∀ (a b : Fin n) (ha : P a) (hb : P b),
          (fromEdgeSet (↑B : Set (Sym2 (Fin n)))).Walk a b →
          G_pre.Reachable ⟨a, ha⟩ ⟨b, hb⟩ from
        (h _ _ hroot hu wu).symm.trans (h _ _ hroot hv wv)
      intro a b ha hb w; induction w with
      | nil => exact @Reachable.refl _ _ _
      | @cons x y z hadj _ ih =>
        rw [fromEdgeSet_adj] at hadj
        have hy : P y := by
          have hxy := (Finset.mem_powerset.mp hB.1) (Finset.mem_coe.mp hadj.1)
          obtain ⟨e, _, he⟩ := Finset.mem_map.mp hxy
          induction e using Sym2.inductionOn with
          | _ c d =>
            simp only [emb, Function.Embedding.sym2Map_apply, Sym2.map_pair_eq] at he
            rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact d.2; exact c.2]
        have hadj_sub : G_pre.Adj ⟨x, ha⟩ ⟨y, hy⟩ := by
          rw [fromEdgeSet_adj]; exact ⟨Finset.mem_coe.mpr (Finset.mem_preimage.mpr
            (Finset.mem_coe.mp hadj.1)), fun h => hadj.2 (congr_arg Subtype.val h)⟩
        exact hadj_sub.reachable.trans (ih hy hb)
  · intro A _; ext x; simp
  · intro B hB; ext e; simp only [Finset.mem_map, Finset.mem_preimage]; constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro he
      have hmem := (Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1) he
      rw [Finset.mem_map] at hmem
      obtain ⟨y, hy, hye⟩ := hmem
      exact ⟨y, hye ▸ he, hye⟩
  · intro A _; simp only [Finset.card_map, E_sub]

/-- The fiber sum factorization: for `S` with `0 ∈ S` and `|S| < n`,
    `∑_{A : C(A)=S} w(A) = Rel(K_{|S|}; q) · q^{|S|·(n-|S|)}`. -/
private lemma fiber_sum_eq {n : ℕ} (hn : 1 ≤ n) (q : ℝ)
    (S : Finset (Fin n)) (hS0 : (⟨0, by omega⟩ : Fin n) ∈ S) (hSn : S.card < n) :
    (∑ A ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset.powerset.filter
        (fun A => componentOfZero hn A = S),
      (1 - q) ^ A.card *
        q ^ ((⊤ : SimpleGraph (Fin n)).edgeFinset.card - A.card)) =
    (⊤ : SimpleGraph (Fin S.card)).reliabilityFun q *
      q ^ (S.card * (n - S.card)) := by
  -- Edge classes: within S, cross, within Sᶜ
  set E := (⊤ : SimpleGraph (Fin n)).edgeFinset
  set E_S := E.filter (fun e => ∀ u v, e = s(u, v) → u ∈ S ∧ v ∈ S)
  set E_Sc := E.filter (fun e => ∀ u v, e = s(u, v) → u ∉ S ∧ v ∉ S)
  -- "Connected on S" predicate
  let connS := fun B : Finset (Sym2 (Fin n)) =>
    ∀ v ∈ S, (fromEdgeSet (↑B : Set (Sym2 (Fin n)))).Reachable ⟨0, by omega⟩ v
  -- Source and target finsets for the bijection
  let src := E.powerset.filter (fun A => componentOfZero hn A = S)
  let tgt := (E_S.powerset.filter connS) ×ˢ E_Sc.powerset
  -- Step 1: Transfer sum to product via bijection A ↔ (A ∩ E_S, A ∩ E_Sc)
  -- This is the core combinatorial step (blueprint Step C.3)
  -- Step 1: Transfer sum to product via bijection A ↔ (A ∩ E_S, A ∩ E_Sc)
  -- (Blueprint Step C.3: forward A ↦ (A ∩ E_S, A ∩ E_Sc), backward (B,C) ↦ B ∪ C)
  -- Step 1: Bijection A ↔ (A ∩ E_S, A ∩ E_Sc) via sum_nbij'
  -- (Blueprint Step C.3: uses componentOfZero_eq_iff for fiber condition,
  --  disjointness of E_S/E_Sc for inverses, card decomposition for summands)
  have hE_disj : Disjoint E_S E_Sc := by
    rw [Finset.disjoint_filter]; intro e _ h1 h2
    induction e using Sym2.inductionOn with
    | _ a b => exact absurd (h1 a b rfl).1 (h2 a b rfl).1
  have hA_sub : ∀ A ∈ src, A ⊆ E_S ∪ E_Sc := by
    intro A hA e he
    have ⟨hpw, heq⟩ := Finset.mem_filter.mp hA
    have hcond := (componentOfZero_eq_iff hn A S hS0 hSn).mp heq
    have he_E := Finset.mem_powerset.mp hpw he
    induction e using Sym2.inductionOn with
    | _ a b =>
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he_E,
          fun u v h => by rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                          <;> exact ⟨‹_›, ‹_›⟩⟩)
      · exact absurd rfl (hcond.1 _ he a ha b hb)
      · exact absurd Sym2.eq_swap (hcond.1 _ he b hb a ha)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he_E,
          fun u v h => by rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                          <;> exact ⟨‹_›, ‹_›⟩⟩)
  have hA_card : ∀ A ∈ src, A.card = (A ∩ E_S).card + (A ∩ E_Sc).card := by
    intro A hA
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left
      Finset.inter_subset_right (Finset.disjoint_of_subset_right
        Finset.inter_subset_right hE_disj)),
      ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr (hA_sub A hA)]
  -- Helper: A ∩ E_S has same edges as A.filter(pred) from componentOfZero_eq_iff
  have hA_S_eq : ∀ A ∈ src, ↑(A ∩ E_S) =
      (↑(A.filter (fun e => ∀ u₁ u₂, e = s(u₁, u₂) → u₁ ∈ S ∧ u₂ ∈ S)) :
        Set (Sym2 (Fin n))) := by
    intro A hA; ext e; simp only [Finset.mem_coe, Finset.mem_inter, Finset.mem_filter]
    exact ⟨fun ⟨he, hf⟩ => ⟨he, (Finset.mem_filter.mp hf).2⟩,
           fun ⟨he, hp⟩ => ⟨he, Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1 he, hp⟩⟩⟩
  have hbij : ∑ A ∈ src, (1 - q) ^ A.card * q ^ (E.card - A.card) =
      ∑ p ∈ tgt, (1 - q) ^ (p.1.card + p.2.card) *
        q ^ (E.card - (p.1.card + p.2.card)) := by
    apply Finset.sum_nbij' (fun A => (A ∩ E_S, A ∩ E_Sc)) (fun p => p.1 ∪ p.2)
    · -- forward lands in tgt
      intro A hA
      have ⟨_, heq⟩ := Finset.mem_filter.mp hA
      have hcond := (componentOfZero_eq_iff hn A S hS0 hSn).mp heq
      rw [Finset.mem_product]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        fun v hv => (hA_S_eq A hA) ▸ hcond.2 v hv⟩,
        Finset.mem_powerset.mpr Finset.inter_subset_right⟩
    · -- backward lands in src
      intro ⟨B, C⟩ hp
      rw [Finset.mem_product] at hp
      have hB_sub := Finset.mem_powerset.mp (Finset.mem_of_mem_filter _ hp.1)
      have hB_conn := (Finset.mem_filter.mp hp.1).2
      have hC_sub := Finset.mem_powerset.mp hp.2
      rw [Finset.mem_filter, Finset.mem_powerset]; refine ⟨fun e he => ?_, ?_⟩
      · rw [Finset.mem_union] at he; cases he with
        | inl h => exact Finset.filter_subset _ _ (hB_sub h)
        | inr h => exact Finset.filter_subset _ _ (hC_sub h)
      · rw [componentOfZero_eq_iff hn _ S hS0 hSn]; constructor
        · intro e he u hu v hv heqe; rw [Finset.mem_union] at he; cases he with
          | inl h => exact hv ((Finset.mem_filter.mp (hB_sub h)).2 u v heqe).2
          | inr h => exact absurd ((Finset.mem_filter.mp (hC_sub h)).2 u v heqe).1 (not_not.mpr hu)
        · intro v hv; have := hB_conn v hv
          exact this.mono (fun a b hab => by
            rw [fromEdgeSet_adj] at hab ⊢
            exact ⟨Finset.mem_coe.mpr (Finset.mem_filter.mpr
              ⟨Finset.mem_union_left _ (Finset.mem_coe.mp hab.1),
               (Finset.mem_filter.mp (hB_sub (Finset.mem_coe.mp hab.1))).2⟩), hab.2⟩)
    · -- left inverse: (A ∩ E_S) ∪ (A ∩ E_Sc) = A
      intro A hA
      rw [← Finset.inter_union_distrib_left]
      exact Finset.inter_eq_left.mpr (hA_sub A hA)
    · -- right inverse: ((B ∪ C) ∩ E_S, (B ∪ C) ∩ E_Sc) = (B, C)
      intro ⟨B, C⟩ hp
      rw [Finset.mem_product] at hp
      have hB := Finset.mem_powerset.mp (Finset.mem_of_mem_filter _ hp.1)
      have hC := Finset.mem_powerset.mp hp.2
      simp only [Prod.mk.injEq]; constructor
      · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hB]
        rw [show C ∩ E_S = ∅ from
          Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_of_subset_left hC hE_disj.symm)]
        exact Finset.union_empty _
      · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hC]
        rw [show B ∩ E_Sc = ∅ from
          Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_of_subset_left hB hE_disj)]
        exact Finset.empty_union _
    · -- summands equal: (1-q)^#A * q^(#E-#A) = (1-q)^(#B+#C) * q^(#E-(#B+#C))
      intro A hA; simp only [Prod.fst, Prod.snd]
      rw [hA_card A hA]
  -- Step 2: Factor the product sum into (∑_B w_S(B)) · q^cross · (∑_C w_Sc(C))
  -- Uses: |E| = |E_S| + |cross| + |E_Sc|, pow_add, sum_product'
  -- Edge count decomposition
  have hE_card : E.card = E_S.card + S.card * (n - S.card) + E_Sc.card := by
    have hsub : E_S ∪ E_Sc ⊆ E :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have h1 : (E \ (E_S ∪ E_Sc)).card + (E_S ∪ E_Sc).card = E.card := by
      rw [Finset.card_sdiff_add_card, Finset.union_eq_left.mpr hsub]
    have h2 := Finset.card_union_of_disjoint hE_disj
    -- Cross-edge count: |E \ (E_S ∪ E_Sc)| = |S| * (n - |S|)
    have h3 : (E \ (E_S ∪ E_Sc)).card = S.card * (n - S.card) := by
      rw [show S.card * (n - S.card) = (S ×ˢ Sᶜ).card from by
        rw [Finset.card_product, Finset.card_compl, Fintype.card_fin]]
      symm; apply Finset.card_bij (fun ⟨u, v⟩ _ => (s(u, v) : Sym2 (Fin n)))
      · -- maps into E \ (E_S ∪ E_Sc)
        intro ⟨u, v⟩ hp; rw [Finset.mem_product] at hp
        have hv := Finset.mem_compl.mp hp.2
        rw [Finset.mem_sdiff, Finset.mem_union, not_or]; refine ⟨?_, ?_, ?_⟩
        · simp [edgeFinset_top, E, Set.mem_toFinset, Sym2.mem_diagSet,
            show u ≠ v from fun h => hv (h ▸ hp.1)]
        · intro h; exact hv ((Finset.mem_filter.mp h).2 u v rfl).2
        · intro h; exact absurd hp.1 ((Finset.mem_filter.mp h).2 u v rfl).1
      · -- injective
        intro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ heq
        rw [Finset.mem_product] at h₁ h₂
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact absurd h₂.1 (Finset.mem_compl.mp h₁.2)
      · -- surjective
        intro e he; rw [Finset.mem_sdiff, Finset.mem_union, not_or] at he
        induction e using Sym2.inductionOn with
        | _ a b =>
          have hnotES : ¬(a ∈ S ∧ b ∈ S) := fun ⟨ha, hb⟩ =>
            he.2.1 (Finset.mem_filter.mpr ⟨he.1, fun u v h => by
              rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨‹_›, ‹_›⟩⟩)
          have hnotESc : ¬(a ∉ S ∧ b ∉ S) := fun ⟨ha, hb⟩ =>
            he.2.2 (Finset.mem_filter.mpr ⟨he.1, fun u v h => by
              rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨‹_›, ‹_›⟩⟩)
          by_cases ha : a ∈ S
          · exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, Finset.mem_compl.mpr
              (fun hb => hnotES ⟨ha, hb⟩)⟩, rfl⟩
          · exact ⟨(b, a), Finset.mem_product.mpr ⟨by_contra (fun hb => hnotESc ⟨ha, hb⟩),
              Finset.mem_compl.mpr ha⟩, Sym2.eq_swap⟩
    omega
  have hfactor : ∑ p ∈ tgt,
      (1 - q) ^ (p.1.card + p.2.card) * q ^ (E.card - (p.1.card + p.2.card)) =
      (∑ B ∈ E_S.powerset.filter connS,
        (1 - q) ^ B.card * q ^ (E_S.card - B.card)) *
      q ^ (S.card * (n - S.card)) *
      (∑ C ∈ E_Sc.powerset,
        (1 - q) ^ C.card * q ^ (E_Sc.card - C.card)) := by
    -- Rewrite each summand using edge count decomposition
    have hsub : ∀ p ∈ tgt,
        (1 - q) ^ (p.1.card + p.2.card) * q ^ (E.card - (p.1.card + p.2.card)) =
        ((1 - q) ^ p.1.card * q ^ (E_S.card - p.1.card)) *
          q ^ (S.card * (n - S.card)) *
          ((1 - q) ^ p.2.card * q ^ (E_Sc.card - p.2.card)) := by
      intro ⟨B, C⟩ hp
      rw [Finset.mem_product] at hp
      have hB := Finset.card_le_card (Finset.mem_powerset.mp
        (Finset.mem_of_mem_filter _ hp.1))
      have hC := Finset.card_le_card (Finset.mem_powerset.mp hp.2)
      simp only [Prod.fst, Prod.snd] at hB hC
      rw [show E.card - (B.card + C.card) =
          (E_S.card - B.card) + S.card * (n - S.card) + (E_Sc.card - C.card) from by
        rw [hE_card]; omega]
      rw [pow_add, pow_add, pow_add]
      ring
    rw [Finset.sum_congr rfl hsub]
    -- Factor: ∑_{(B,C)} f(B)*k*g(C) = (∑_B f(B)) * k * (∑_C g(C))
    rw [Finset.sum_product]; simp only [Prod.fst, Prod.snd]
    simp_rw [show ∀ (x y : Finset (Sym2 (Fin n))),
        (1-q)^x.card * q^(E_S.card - x.card) * q^(S.card * (n - S.card)) *
          ((1-q)^y.card * q^(E_Sc.card - y.card)) =
        ((1-q)^x.card * q^(E_S.card - x.card)) *
          (q^(S.card * (n - S.card)) * ((1-q)^y.card * q^(E_Sc.card - y.card))) from
      fun _ _ => by ring]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]; ring
  -- Step 3: ∑_C w_Sc(C) = 1 (total_weight_eq_one via reliabilityFun_equiv for Sᶜ)
  have htotal_Sc : ∑ C ∈ E_Sc.powerset,
      (1 - q) ^ C.card * q ^ (E_Sc.card - C.card) = 1 := by
    rw [Finset.sum_powerset_apply_card
      (f := fun m => (1 - q) ^ m * q ^ (E_Sc.card - m))]
    simp only [nsmul_eq_mul]
    conv_rhs => rw [show (1 : ℝ) = ((1 - q) + q) ^ E_Sc.card from by ring]
    rw [add_pow]; congr 1; ext m; ring
  -- Step 4: ∑_B connS w_S(B) = Rel(K_s; q) (reliabilityFun_equiv for S)
  have hrel_S : ∑ B ∈ E_S.powerset.filter connS,
      (1 - q) ^ B.card * q ^ (E_S.card - B.card) =
      (⊤ : SimpleGraph (Fin S.card)).reliabilityFun q := by
    rw [show S.card = (Finset.univ.filter (· ∈ S)).card from by simp]
    exact rel_sum_of_predicate q (· ∈ S) ⟨0, by omega⟩ hS0 E_S rfl
  -- Assembly
  rw [hbij, hfactor, htotal_Sc, hrel_S, mul_one]

/-- The number of `(s+1)`-element subsets of `Fin n` containing `0` is `C(n-1, s)`. -/
private lemma count_subsets_with_zero {n : ℕ} (hn : 1 ≤ n) (s : ℕ) (hs : s < n - 1) :
    ((Finset.univ (α := Finset (Fin n))).filter
      (fun S => (⟨0, by omega⟩ : Fin n) ∈ S ∧ S.card = s + 1)).card =
    (n - 1).choose s := by
  set zero : Fin n := ⟨0, by omega⟩
  rw [show (n - 1).choose s = (powersetCard s (Finset.univ.erase zero)).card from by
    rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]]
  exact Finset.card_bij (fun S _ => S.erase zero)
    (fun S hS => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      rw [Finset.mem_powersetCard]
      refine ⟨fun x hx => ?_, by rw [Finset.card_erase_of_mem hS.1]; omega⟩
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ _⟩)
    (fun S₁ hS₁ S₂ hS₂ h => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS₁ hS₂
      have := congr_arg (insert zero) h
      rwa [Finset.insert_erase hS₁.1, Finset.insert_erase hS₂.1] at this)
    (fun T hT => by
      rw [Finset.mem_powersetCard] at hT
      have hzT : zero ∉ T := fun h => by
        have := hT.1 h; rw [Finset.mem_erase] at this; exact this.1 rfl
      refine ⟨insert zero T, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Finset.mem_insert_self _ _, ?_⟩, Finset.erase_insert hzT⟩
      rw [Finset.card_insert_of_notMem hzT]; omega)

/-! ### Step E: Assembly -/

/-- The disconnected sum equals the recursion sum. Proved by:
    (1) partitioning by `C(A)` via `sum_fiberwise`,
    (2) applying `fiber_sum_eq` to each fiber,
    (3) regrouping by `|S|` and applying `count_subsets_with_zero`. -/
lemma disconnected_sum_eq_recursion_sum (n : ℕ) (hn : 1 ≤ n) (q : ℝ) :
    (∑ A ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset.powerset,
      (if ¬(SimpleGraph.fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Connected then
        (1 - q) ^ A.card * q ^ ((⊤ : SimpleGraph (Fin n)).edgeFinset.card - A.card)
      else 0)) =
    ∑ s ∈ Finset.range (n - 1), ((n - 1).choose s : ℝ) *
      (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
      q ^ ((s + 1) * (n - (s + 1))) := by
  set zero : Fin n := ⟨0, by omega⟩
  set E := (⊤ : SimpleGraph (Fin n)).edgeFinset
  set T := (Finset.univ (α := Finset (Fin n))).filter (fun S => zero ∈ S ∧ S.card < n)
  -- Step 1: Partition the disconnected sum by componentOfZero
  -- ∑ (if ¬Connected then w else 0) = ∑_S ∑_{A:C(A)=S} w(A)
  have step1 :
      (∑ A ∈ E.powerset, (if ¬(fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Connected then
        (1 - q) ^ A.card * q ^ (E.card - A.card) else 0)) =
      ∑ S ∈ T, ∑ A ∈ E.powerset.filter (fun A => componentOfZero hn A = S),
        (1 - q) ^ A.card * q ^ (E.card - A.card) := by
    -- Step 1a: rewrite ¬Connected to C(A) ≠ univ in the filter
    rw [← Finset.sum_filter]
    have hfilt_eq : E.powerset.filter (fun (A : Finset (Sym2 (Fin n))) =>
        ¬(fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Connected) =
        E.powerset.filter (fun A => componentOfZero hn A ≠ Finset.univ) := by
      congr 1; ext A
      exact (connected_iff_componentOfZero_eq_univ hn A).not
    rw [hfilt_eq]
    -- Step 1b: partition by componentOfZero
    rw [← Finset.sum_fiberwise_of_maps_to (g := componentOfZero hn) (t := T)
      (fun A hA => by
        have ⟨_, hne⟩ := Finset.mem_filter.mp hA
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, zero_mem_componentOfZero hn A, ?_⟩
        by_contra hle; push_neg at hle
        have hub := Finset.card_le_univ (componentOfZero hn A)
        rw [Fintype.card_fin] at hub
        exact hne (Finset.eq_univ_of_card _ (by rw [Fintype.card_fin]; omega)))]
    -- Step 1c: simplify double filter
    apply Finset.sum_congr rfl; intro S hS
    apply Finset.sum_congr _ (fun _ _ => rfl)
    -- Show: (E.powerset.filter(C≠univ)).filter(C=S) = E.powerset.filter(C=S)
    ext A; simp only [Finset.mem_filter, and_assoc]
    constructor
    · exact fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩
    · intro ⟨h1, h3⟩; refine ⟨h1, ?_, h3⟩
      rw [h3]; intro heq
      have ⟨_, _, hlt⟩ := Finset.mem_filter.mp hS
      rw [heq, Finset.card_univ, Fintype.card_fin] at hlt; omega
  -- Step 2: Apply fiber_sum_eq to each fiber
  have step2 :
      (∑ S ∈ T, ∑ A ∈ E.powerset.filter (fun A => componentOfZero hn A = S),
        (1 - q) ^ A.card * q ^ (E.card - A.card)) =
      ∑ S ∈ T, (⊤ : SimpleGraph (Fin S.card)).reliabilityFun q *
        q ^ (S.card * (n - S.card)) := by
    apply Finset.sum_congr rfl; intro S hS
    have ⟨_, hS0, hSn⟩ := Finset.mem_filter.mp hS
    exact fiber_sum_eq hn q S hS0 hSn
  -- Step 3: Regroup by |S| and apply count_subsets_with_zero
  have step3 :
      (∑ S ∈ T, (⊤ : SimpleGraph (Fin S.card)).reliabilityFun q *
        q ^ (S.card * (n - S.card))) =
      ∑ s ∈ Finset.range (n - 1), ((n - 1).choose s : ℝ) *
        (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
        q ^ ((s + 1) * (n - (s + 1))) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun S => S.card - 1) (t := Finset.range (n - 1))
      (fun S hS => by
        have ⟨_, h0, hlt⟩ := Finset.mem_filter.mp hS
        rw [Finset.mem_range]; show S.card - 1 < n - 1
        have : 1 ≤ S.card := Finset.card_pos.mpr ⟨_, h0⟩
        omega)]
    apply Finset.sum_congr rfl
    intro s hs; rw [Finset.mem_range] at hs
    -- Identify the fiber with {S | zero ∈ S ∧ |S| = s+1}
    have hfiber_eq : T.filter (fun S => S.card - 1 = s) =
        (Finset.univ (α := Finset (Fin n))).filter
          (fun S => zero ∈ S ∧ S.card = s + 1) := by
      ext S; simp only [Finset.mem_filter, Finset.mem_univ, true_and, T]
      constructor
      · intro ⟨⟨h0, hlt⟩, hcard⟩
        exact ⟨h0, by have := Finset.card_pos.mpr ⟨_, h0⟩; omega⟩
      · intro ⟨h0, hcard⟩
        exact ⟨⟨h0, by omega⟩, by have := Finset.card_pos.mpr ⟨_, h0⟩; omega⟩
    rw [hfiber_eq]
    -- Rewrite each summand: replace S.card with s+1 using the filter condition
    set F := (Finset.univ (α := Finset (Fin n))).filter (fun S => zero ∈ S ∧ S.card = s + 1)
    have hsum_rw : (∑ S ∈ F,
        (⊤ : SimpleGraph (Fin S.card)).reliabilityFun q * q ^ (S.card * (n - S.card))) =
        ∑ S ∈ F, (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
          q ^ ((s + 1) * (n - (s + 1))) :=
      Finset.sum_congr rfl fun S hS => by
        rw [show S.card = s + 1 from (Finset.mem_filter.mp hS).2.2]
    rw [hsum_rw, Finset.sum_const, count_subsets_with_zero hn s hs, nsmul_eq_mul]
    ring
  exact step1.trans (step2.trans step3)

/-! ### Recursion identity -/

/-- Recursion for the reliability of complete graphs:
    `Rel(K_n; q) = 1 - ∑_{s=0}^{n-2} C(n-1,s) · Rel(K_{s+1}; q) · q^{(s+1)(n-s-1)}`. -/
theorem reliabilityFun_completeGraph_recursion (n : ℕ) (hn : 1 ≤ n) (q : ℝ) :
    (⊤ : SimpleGraph (Fin n)).reliabilityFun q =
      1 - ∑ s ∈ Finset.range (n - 1), ((n - 1).choose s : ℝ) *
        (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
        q ^ ((s + 1) * (n - (s + 1))) := by
  rw [reliabilityFun_eq_one_sub_disconnected, disconnected_sum_eq_recursion_sum n hn q]

/-! ### Bounding sequence -/

/-- `aₙ(r) = ∑_{s=0}^{n-2} C(n-1, s) · r^{(s+1)(n-s-1)}`. -/
def seqA (r : ℝ) (n : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (n - 1), ((n - 1).choose s : ℝ) * r ^ ((s + 1) * (n - (s + 1)))

lemma seqA_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : 0 ≤ seqA r n := by
  unfold seqA; apply Finset.sum_nonneg; intros
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr _)

/-- `seqA r n → 0` as `n → ∞` for `0 ≤ r < 1`.

Uses the pairing bound `seqA ≤ (1 + r^{⌊n/2⌋})^n - 1` from the paper:
pair terms `s` and `n-s`, apply Pascal's identity, bound exponents, then
squeeze with `exp(n · r^{⌊n/2⌋}) - 1 → 0`. -/
lemma tendsto_seqA_zero {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (seqA r) atTop (nhds 0) := by
  have hbound : ∀ n, seqA r n ≤ (1 + r ^ (n / 2)) ^ n - 1 := by
    intro n; unfold seqA; set x := r ^ (n / 2)
    -- Following the paper's pairing argument via delta functions.
    -- We work with the reindexed sum: let f(s) = C(n-1,s-1) * r^{s(n-s)} for s in {1,...,n-1}.
    -- Define δ_le(s) = if s ≤ n/2 then 1 else 0, δ_ge(s) = if s ≥ n/2 then 1 else 0.
    -- Then δ_le(s) + δ_ge(s) ≥ 1 for all s.
    let f : ℕ → ℝ := fun s => ((n - 1).choose (s - 1) : ℝ) * r ^ (s * (n - s))
    let δ_le : ℕ → ℝ := fun s => if s ≤ n / 2 then 1 else 0
    let δ_ge : ℕ → ℝ := fun s => if n / 2 ≤ s then 1 else 0
    -- Step 0: reindex seqA to paper's form (s → s+1)
    have hreindex : ∑ s ∈ Finset.range (n - 1), ((n - 1).choose s : ℝ) *
        r ^ ((s + 1) * (n - (s + 1))) =
        ∑ s ∈ Finset.Icc 1 (n - 1), f s := by
      apply Finset.sum_nbij' (· + 1) (· - 1)
      · intro s hs; simp only [Finset.mem_range] at hs; simp [Finset.mem_Icc]; omega
      · intro s hs; simp only [Finset.mem_Icc] at hs; simp [Finset.mem_range]; omega
      · intro s hs; omega
      · intro s hs; simp only [Finset.mem_Icc] at hs; omega
      · intro s _; simp [f]
    -- Step 1: f(s) ≤ f(s) * (δ_le(s) + δ_ge(s))  since δ_le + δ_ge ≥ 1 and f ≥ 0
    have hstep1 : ∑ s ∈ Finset.Icc 1 (n - 1), f s ≤
        ∑ s ∈ Finset.Icc 1 (n - 1), f s * (δ_le s + δ_ge s) := by
      apply Finset.sum_le_sum; intro s _
      calc f s = f s * 1 := (mul_one _).symm
        _ ≤ f s * (δ_le s + δ_ge s) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            simp only [δ_le, δ_ge]; split_ifs <;> norm_num <;> omega
    -- Step 2: distribute
    have hstep2 : ∑ s ∈ Finset.Icc 1 (n - 1), f s * (δ_le s + δ_ge s) =
        ∑ s ∈ Finset.Icc 1 (n - 1), f s * δ_le s +
        ∑ s ∈ Finset.Icc 1 (n - 1), f s * δ_ge s := by
      rw [← Finset.sum_add_distrib]; congr 1; ext s; ring
    -- Step 3: reindex s → n-s in second sum (Icc 1 (n-1) is preserved under s ↦ n-s)
    have hstep3 : ∑ s ∈ Finset.Icc 1 (n - 1), f s * δ_ge s =
        ∑ s ∈ Finset.Icc 1 (n - 1), f (n - s) * δ_ge (n - s) := by
      apply Finset.sum_nbij' (fun s => n - s) (fun s => n - s)
      · intro s hs; simp only [Finset.mem_Icc] at hs ⊢; omega
      · intro s hs; simp only [Finset.mem_Icc] at hs ⊢; omega
      · intro s hs; simp only [Finset.mem_Icc] at hs
        show n - (n - s) = s; exact Nat.sub_sub_self (by omega)
      · intro s hs; simp only [Finset.mem_Icc] at hs
        show n - (n - s) = s; exact Nat.sub_sub_self (by omega)
      · intro s hs; simp only [Finset.mem_Icc] at hs
        show f s * δ_ge s = f (n - (n - s)) * δ_ge (n - (n - s))
        rw [Nat.sub_sub_self (by omega : s ≤ n)]
    -- Step 4: simplify f(n-s): coefficient becomes C(n-1,s), exponent is s(n-s)
    have hstep4 : ∀ s ∈ Finset.Icc 1 (n - 1),
        f (n - s) * δ_ge (n - s) =
        ((n - 1).choose s : ℝ) * r ^ (s * (n - s)) * δ_ge (n - s) := by
      intro s hs; simp only [Finset.mem_Icc] at hs; simp only [f]
      congr 1; congr 1
      · congr 1; rw [show n - s - 1 = (n - 1) - s from by omega]; exact Nat.choose_symm (by omega)
      · congr 1; rw [Nat.sub_sub_self (by omega : s ≤ n)]; ring
    -- Step 5: δ_le(s) ≤ δ_ge(n-s) (key: n - n/2 ≥ n/2, so δ_ge covers more)
    -- Use this to bound: f·δ_le ≤ f·δ_ge(n-s), then combine
    have hstep5_ineq :
        (∑ s ∈ Finset.Icc 1 (n - 1), f s * δ_le s) +
        (∑ s ∈ Finset.Icc 1 (n - 1), ((n - 1).choose s : ℝ) * r ^ (s * (n - s)) * δ_ge (n - s)) ≤
        ∑ s ∈ Finset.Icc 1 (n - 1),
          (((n - 1).choose (s - 1) : ℝ) + ((n - 1).choose s : ℝ)) *
            r ^ (s * (n - s)) * δ_ge (n - s) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro s hs
      simp only [Finset.mem_Icc] at hs; simp only [f]
      have hdle : δ_le s ≤ δ_ge (n - s) := by
        simp only [δ_le, δ_ge]; split_ifs <;> norm_num <;> omega
      -- Need: a*c*e + b*c*d ≤ (a+b)*c*d where e=δ_le ≤ d=δ_ge(n-s), a,b,c ≥ 0
      -- i.e., a*c*e ≤ a*c*d, i.e., a*c*(d-e) ≥ 0
      have hc := pow_nonneg hr (s * (n - s))
      have ha := Nat.cast_nonneg (α := ℝ) ((n - 1).choose (s - 1))
      have hb := Nat.cast_nonneg (α := ℝ) ((n - 1).choose s)
      have hd : 0 ≤ δ_ge (n - s) := by simp only [δ_ge]; split_ifs <;> norm_num
      nlinarith [mul_nonneg (mul_nonneg ha hc) (show 0 ≤ δ_ge (n - s) - δ_le s from by linarith)]
    -- Step 6: Pascal: C(n-1, s-1) + C(n-1, s) = C(n, s)
    have hstep6 : ∀ s ∈ Finset.Icc 1 (n - 1),
        ((n - 1).choose (s - 1) : ℝ) + ((n - 1).choose s : ℝ) = (n.choose s : ℝ) := by
      intro s hs; simp only [Finset.mem_Icc] at hs
      have h : (n - 1).choose (s - 1) + (n - 1).choose s = n.choose s := by
        have := Nat.choose_succ_succ (n - 1) (s - 1)
        simp only [Nat.succ_eq_add_one,
          show n - 1 + 1 = n from by omega, show s - 1 + 1 = s from by omega] at this
        linarith
      exact_mod_cast h
    -- Step 7: exponent bound: δ_ge(n-s) ≠ 0 ⟹ n/2 ≤ n-s ⟹ s(n-s) ≥ s·(n/2)
    have hstep7 : ∀ s ∈ Finset.Icc 1 (n - 1),
        (n.choose s : ℝ) * r ^ (s * (n - s)) * δ_ge (n - s) ≤
        (n.choose s : ℝ) * x ^ s * δ_ge (n - s) := by
      intro s hs; simp only [δ_ge]
      split_ifs with h
      · simp only [mul_one]; apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        calc r ^ (s * (n - s)) ≤ r ^ (n / 2 * s) := by
              apply pow_le_pow_of_le_one hr hr1.le
              rw [mul_comm]; exact Nat.mul_le_mul_left s h
          _ = x ^ s := by rw [show x = r ^ (n / 2) from rfl, ← pow_mul]
      · simp
    -- Step 8: drop δ_ge(n-s) ≤ 1
    have hstep8 : ∀ s ∈ Finset.Icc 1 (n - 1),
        (n.choose s : ℝ) * x ^ s * δ_ge (n - s) ≤ (n.choose s : ℝ) * x ^ s := by
      intro s _; simp only [δ_ge]; split_ifs <;> simp; positivity
    -- Step 10: extend range from Icc 1 (n-1) to range (n+1) minus s=0 term
    have hstep10 : ∑ s ∈ Finset.Icc 1 (n - 1), (n.choose s : ℝ) * x ^ s ≤
        ∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) * x ^ s - 1 := by
      have hsub : Finset.Icc 1 (n - 1) ⊆ Finset.Icc 1 n :=
        Finset.Icc_subset_Icc_right (by omega)
      have hnn : ∀ s ∈ Finset.Icc 1 n, 0 ≤ (n.choose s : ℝ) * x ^ s :=
        fun s _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (pow_nonneg hr _) _)
      have h1 : ∑ s ∈ Finset.Icc 1 (n - 1), (n.choose s : ℝ) * x ^ s ≤
          ∑ s ∈ Finset.Icc 1 n, (n.choose s : ℝ) * x ^ s :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s hs _ => hnn s hs)
      have h2 : ∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) * x ^ s =
          1 + ∑ s ∈ Finset.Icc 1 n, (n.choose s : ℝ) * x ^ s := by
        rw [show Finset.range (n + 1) = {0} ∪ Finset.Icc 1 n from by
          ext s; simp [Finset.mem_Icc]; omega]
        rw [Finset.sum_union (by
          rw [Finset.disjoint_left]; intro a; simp [Finset.mem_Icc]; omega)]; simp
      linarith
    -- Step 11: binomial theorem
    have hstep11 : ∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) * x ^ s = (1 + x) ^ n := by
      rw [show (1 : ℝ) + x = x + 1 from by ring, add_pow]; simp [one_pow, mul_one, mul_comm]
    -- Assembly
    calc ∑ s ∈ Finset.range (n - 1), ((n - 1).choose s : ℝ) * r ^ ((s + 1) * (n - (s + 1)))
        = ∑ s ∈ Finset.Icc 1 (n - 1), f s := hreindex
      _ ≤ ∑ s ∈ Finset.Icc 1 (n - 1), f s * (δ_le s + δ_ge s) := hstep1
      _ = (∑ s ∈ Finset.Icc 1 (n - 1), f s * δ_le s) +
          (∑ s ∈ Finset.Icc 1 (n - 1), f s * δ_ge s) := hstep2
      _ = (∑ s ∈ Finset.Icc 1 (n - 1), f s * δ_le s) +
          (∑ s ∈ Finset.Icc 1 (n - 1), f (n - s) * δ_ge (n - s)) := by rw [hstep3]
      _ = (∑ s ∈ Finset.Icc 1 (n - 1), f s * δ_le s) +
          (∑ s ∈ Finset.Icc 1 (n - 1), ((n - 1).choose s : ℝ) *
            r ^ (s * (n - s)) * δ_ge (n - s)) := by
          congr 1; exact Finset.sum_congr rfl hstep4
      _ ≤ ∑ s ∈ Finset.Icc 1 (n - 1), (((n - 1).choose (s - 1) : ℝ) +
            ((n - 1).choose s : ℝ)) * r ^ (s * (n - s)) * δ_ge (n - s) := hstep5_ineq
      _ = ∑ s ∈ Finset.Icc 1 (n - 1), (n.choose s : ℝ) *
            r ^ (s * (n - s)) * δ_ge (n - s) := by
          exact Finset.sum_congr rfl (fun s hs => by rw [hstep6 s hs])
      _ ≤ ∑ s ∈ Finset.Icc 1 (n - 1), (n.choose s : ℝ) * x ^ s * δ_ge (n - s) :=
          Finset.sum_le_sum hstep7
      _ ≤ ∑ s ∈ Finset.Icc 1 (n - 1), (n.choose s : ℝ) * x ^ s :=
          Finset.sum_le_sum hstep8
      _ ≤ ∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) * x ^ s - 1 := hstep10
      _ = (1 + x) ^ n - 1 := by rw [hstep11]
  -- Step 2: squeeze with (1 + r^(n/2))^n - 1 → 0
  apply squeeze_zero (fun n => seqA_nonneg hr n) hbound
  -- Step 3: (1 + r^(n/2))^n - 1 → 0
  -- Use: (1+x)^n ≤ exp(nx) and n * r^(n/2) → 0
  have hkey : Tendsto (fun n : ℕ => (↑n : ℝ) * r ^ (n / 2)) atTop (nhds 0) := by
    have h1 : Tendsto (fun k : ℕ => (2 * (↑k : ℝ) + 1) * r ^ k) atTop (nhds 0) := by
      have ha := (tendsto_self_mul_const_pow_of_lt_one hr hr1).const_mul 2
      have hb := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
      simp only [show (2 : ℝ) * 0 = 0 from by ring, show (0 : ℝ) * 2 + 0 = 0 from by ring] at ha
      have := ha.add hb; simp only [show (0 : ℝ) + 0 = 0 from by ring] at this
      exact this.congr (fun k => by ring)
    have h2 : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
      rw [Filter.tendsto_atTop]; intro b
      exact Filter.eventually_atTop.mpr ⟨2 * b, fun n hn => by omega⟩
    apply squeeze_zero (fun n => by positivity)
      (fun n => by
        calc (↑n : ℝ) * r ^ (n / 2)
            ≤ (2 * ↑(n / 2) + 1) * r ^ (n / 2) := by
              gcongr; exact_mod_cast show n ≤ 2 * (n / 2) + 1 by omega)
    exact h1.comp h2
  apply squeeze_zero
    (fun n => sub_nonneg.mpr (one_le_pow₀ (by linarith [pow_nonneg hr (n / 2)])))
    (fun n => by
      calc (1 + r ^ (n / 2)) ^ n - 1
          ≤ (Real.exp (r ^ (n / 2))) ^ n - 1 := by
            gcongr; linarith [Real.add_one_le_exp (r ^ (n / 2))]
        _ = Real.exp (↑n * r ^ (n / 2)) - 1 := by
              congr 1; exact (Real.exp_nat_mul _ _).symm)
  -- exp(n * r^(n/2)) - 1 → 0 since n * r^(n/2) → 0 and exp is continuous
  have : Tendsto (fun n : ℕ => Real.exp (↑n * r ^ (n / 2)) - 1) atTop (nhds 0) := by
    have hexp := (Real.continuous_exp.tendsto 0).comp (by simpa using hkey)
    simp only [Function.comp, Real.exp_zero] at hexp
    simpa using hexp.sub_const 1
  exact this

/-! ### Recursion bound -/

/-- From the recursion: `|Rel(K_n; q) - 1| ≤ M · seqA |q| n` when all
`|Rel(K_s; q)| ≤ M` for `s < n`. -/
private lemma recursion_bound (n : ℕ) (hn : 1 ≤ n) (q : ℝ)
    (M : ℝ) (hM : ∀ s : ℕ, s < n → |((⊤ : SimpleGraph (Fin s)).reliabilityFun q)| ≤ M)
    (hM_nn : 0 ≤ M) :
    |((⊤ : SimpleGraph (Fin n)).reliabilityFun q) - 1| ≤ M * seqA |q| n := by
  rw [reliabilityFun_completeGraph_recursion n hn q]
  simp only [sub_sub_cancel_left, abs_neg]
  calc |∑ s ∈ Finset.range (n - 1), ((n - 1).choose s : ℝ) *
          (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
          q ^ ((s + 1) * (n - (s + 1)))|
      ≤ ∑ s ∈ Finset.range (n - 1), |((n - 1).choose s : ℝ) *
          (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
          q ^ ((s + 1) * (n - (s + 1)))| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s ∈ Finset.range (n - 1), ((n - 1).choose s : ℝ) *
          |(⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q| *
          |q| ^ ((s + 1) * (n - (s + 1))) := by
        congr 1; ext s
        rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ∑ s ∈ Finset.range (n - 1), ((n - 1).choose s : ℝ) * M *
          |q| ^ ((s + 1) * (n - (s + 1))) := by
        apply Finset.sum_le_sum; intro s hs
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (hM (s + 1) (by
            rw [Finset.mem_range] at hs; omega)) (Nat.cast_nonneg _)
        · exact pow_nonneg (abs_nonneg q) _
    _ = M * seqA |q| n := by
        unfold seqA; rw [Finset.mul_sum]; congr 1; ext s; ring

/-! ### Uniform boundedness -/

/-- For `|q| < 1`, `|Rel(Kₙ; q)|` is uniformly bounded over all `n`. -/
lemma reliabilityFun_completeGraph_bounded (q : ℝ) (hq : |q| < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, |((⊤ : SimpleGraph (Fin n)).reliabilityFun q)| ≤ M := by
  -- Get N such that seqA |q| n ≤ 1/2 for n ≥ N
  have hseqA := tendsto_seqA_zero (abs_nonneg q) hq
  rw [Metric.tendsto_atTop] at hseqA
  obtain ⟨N, hN⟩ := hseqA (1/2) (by positivity)
  -- M₀ = max over small n
  let vals : Finset ℝ := (Finset.range (N + 1)).image
    (fun n => |((⊤ : SimpleGraph (Fin n)).reliabilityFun q)|)
  have hvals : vals.Nonempty := ⟨|((⊤ : SimpleGraph (Fin 0)).reliabilityFun q)|,
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N), rfl⟩⟩
  let M₀ := vals.sup' hvals id
  let M := max 2 (M₀ + 1)
  refine ⟨M, by positivity, ?_⟩
  have hM_ge_2 : (2 : ℝ) ≤ M := le_max_left 2 (M₀ + 1)
  -- For n ≤ N: bounded by M₀ ≤ M
  have hM₀_bound : ∀ n : ℕ, n ≤ N →
      |((⊤ : SimpleGraph (Fin n)).reliabilityFun q)| ≤ M := by
    intro n hn
    have hmem : |((⊤ : SimpleGraph (Fin n)).reliabilityFun q)| ∈ vals :=
      Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), rfl⟩
    have : id |((⊤ : SimpleGraph (Fin n)).reliabilityFun q)| ≤ M₀ :=
      Finset.le_sup' id hmem
    simp [id] at this
    linarith [le_max_right 2 (M₀ + 1)]
  -- For n ≥ N: seqA |q| n ≤ 1/2
  have hseqA_bound : ∀ n : ℕ, N ≤ n → seqA |q| n ≤ 1/2 := by
    intro n hn
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    linarith [abs_of_nonneg (seqA_nonneg (abs_nonneg q) n)]
  -- Strong induction
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  by_cases hn : n ≤ N
  · exact hM₀_bound n hn
  · push_neg at hn
    have hn1 : 1 ≤ n := by omega
    have hbound := recursion_bound n hn1 q M (fun s hs => ih s hs) (by positivity)
    calc |((⊤ : SimpleGraph (Fin n)).reliabilityFun q)|
        = |(((⊤ : SimpleGraph (Fin n)).reliabilityFun q) - 1) + 1| := by ring_nf
      _ ≤ |((⊤ : SimpleGraph (Fin n)).reliabilityFun q) - 1| + |1| := abs_add_le _ _
      _ = |((⊤ : SimpleGraph (Fin n)).reliabilityFun q) - 1| + 1 := by
          simp [abs_of_pos (show (0:ℝ) < 1 by positivity)]
      _ ≤ M * seqA |q| n + 1 := by linarith
      _ ≤ M * (1/2) + 1 := by
          linarith [mul_le_mul_of_nonneg_left (hseqA_bound n (by omega)) (by positivity : (0:ℝ) ≤ M)]
      _ ≤ M := by linarith

/-! ### Convergence -/

/-- **Lemma 2.1**: For `|q| < 1`, `Rel(Kₙ; q) → 1` as `n → ∞`. -/
theorem lim_rel_completeGraph (q : ℝ) (hq : |q| < 1) :
    Tendsto (fun n => (⊤ : SimpleGraph (Fin n)).reliabilityFun q) atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM_pos, hM⟩ := reliabilityFun_completeGraph_bounded q hq
  have hseqA := tendsto_seqA_zero (abs_nonneg q) hq
  rw [Metric.tendsto_atTop] at hseqA
  obtain ⟨N₀, hN₀⟩ := hseqA (ε / M) (div_pos hε hM_pos)
  use max N₀ 1
  intro n hn
  rw [Real.dist_eq]
  by_cases hn0 : n = 0
  · omega
  · have hn1 : 1 ≤ n := by omega
    have hbound := recursion_bound n hn1 q M (fun s _ => hM s) (by positivity)
    calc |((⊤ : SimpleGraph (Fin n)).reliabilityFun q) - 1|
        ≤ M * seqA |q| n := hbound
      _ < M * (ε / M) := by
          apply mul_lt_mul_of_pos_left _ hM_pos
          have h := hN₀ n (le_of_max_le_left hn)
          rw [Real.dist_eq, sub_zero] at h
          linarith [abs_of_nonneg (seqA_nonneg (abs_nonneg q) n)]
      _ = ε := by field_simp

/-! ### Split-reliability of complete graphs

The second part of Lemma 2.1 from the paper: `splitRel(Kₙ; q) / q^{n-1} → 2`
as `n → ∞` for `|q| < 1`.

The proof uses the recursion (Equation 2.2 in the paper):
  `splitRel(Kₙ; q) = ∑_{s=1}^{n-1} C(n-2, s-1) · Rel(Kₛ; q) · Rel(K_{n-s}; q) · q^{s(n-s)}`

Extracting the `s = 1` and `s = n - 1` terms gives `2 · q^{n-1} · Rel(K_{n-1}; q)`,
and the remaining sum is bounded by `M² · b_n · q^{n-1}` where `b_n → 0`.

The proof uses the same conditioning-on-component-of-zero approach as
`reliabilityFun_completeGraph_recursion`, but additionally requires the complement
component (containing terminal 1) to be connected.
-/

/-! #### Step A: Counting subsets with 0 present and 1 absent -/

/-- The number of `(s+1)`-element subsets of `Fin n` containing `0` but not `1`
is `C(n-2, s)`. -/
private lemma count_subsets_split {n : ℕ} (hn : 2 ≤ n) (s : ℕ) (_hs : s < n - 1) :
    ((Finset.univ (α := Finset (Fin n))).filter
      (fun S => (⟨0, by omega⟩ : Fin n) ∈ S ∧
        (⟨1, by omega⟩ : Fin n) ∉ S ∧ S.card = s + 1)).card =
    (n - 2).choose s := by
  set zero : Fin n := ⟨0, by omega⟩
  set one : Fin n := ⟨1, by omega⟩
  have hne : zero ≠ one := by simp [zero, one, Fin.ext_iff]
  set base := (Finset.univ : Finset (Fin n)).erase zero |>.erase one
  have hbase_card : base.card = n - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]; omega
  rw [show (n - 2).choose s = (powersetCard s base).card from by
    rw [Finset.card_powersetCard, hbase_card]]
  apply Finset.card_bij (fun S _ => S.erase zero)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rw [Finset.mem_powersetCard]; refine ⟨fun x hx => ?_, ?_⟩
    · have ⟨hx0, hxS⟩ := Finset.mem_erase.mp hx
      exact Finset.mem_erase.mpr ⟨fun h => hS.2.1 (h ▸ hxS),
        Finset.mem_erase.mpr ⟨hx0, Finset.mem_univ _⟩⟩
    · rw [Finset.card_erase_of_mem hS.1]; omega
  · intro S₁ hS₁ S₂ hS₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS₁ hS₂
    have := congr_arg (insert zero) h
    rwa [Finset.insert_erase hS₁.1, Finset.insert_erase hS₂.1] at this
  · intro T hT
    rw [Finset.mem_powersetCard] at hT
    have h0 : zero ∉ T := fun h =>
      (Finset.mem_erase.mp (Finset.mem_erase.mp (hT.1 h)).2).1 rfl
    have h1_base : one ∉ T := fun h =>
      (Finset.mem_erase.mp (hT.1 h)).1 rfl
    refine ⟨insert zero T, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.mem_insert_self _ _, ?_, ?_⟩, Finset.erase_insert h0⟩
    · rw [Finset.mem_insert]; push_neg; exact ⟨hne.symm, h1_base⟩
    · rw [Finset.card_insert_of_notMem h0]; omega

/-! #### Step B: Split fiber sum factorization -/

set_option maxHeartbeats 800000 in
-- The fiber sum involves many `set` definitions, bijections, and edge-counting lemmas
-- that require extra heartbeats for the type checker to elaborate.
/-- The split fiber sum factorization: for `S` with `0 ∈ S`, `1 ∉ S`, and `|S| < n`,
`∑_{A : C(A)=S, Sᶜ-connected} w(A) = Rel(K_{|S|}; q) · Rel(K_{n-|S|}; q) · q^{|S|·(n-|S|)}`.

This is the split-reliability analog of `fiber_sum_eq`. -/
private lemma split_fiber_sum_eq {n : ℕ} (hn : 2 ≤ n) (q : ℝ)
    (S : Finset (Fin n))
    (hS0 : (⟨0, by omega⟩ : Fin n) ∈ S)
    (hS1 : (⟨1, by omega⟩ : Fin n) ∉ S)
    (hSn : S.card < n) :
    (∑ A ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset.powerset.filter
        (fun A => componentOfZero (by omega : 1 ≤ n) A = S ∧
          (∀ v, v ∉ S → (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Reachable
            ⟨1, by omega⟩ v)),
      (1 - q) ^ A.card *
        q ^ ((⊤ : SimpleGraph (Fin n)).edgeFinset.card - A.card)) =
    (⊤ : SimpleGraph (Fin S.card)).reliabilityFun q *
    (⊤ : SimpleGraph (Fin (n - S.card))).reliabilityFun q *
      q ^ (S.card * (n - S.card)) := by
  set zero : Fin n := ⟨0, by omega⟩
  set one : Fin n := ⟨1, by omega⟩
  set E := (⊤ : SimpleGraph (Fin n)).edgeFinset
  set E_S := E.filter (fun e => ∀ u v, e = s(u, v) → u ∈ S ∧ v ∈ S)
  set E_Sc := E.filter (fun e => ∀ u v, e = s(u, v) → u ∉ S ∧ v ∉ S)
  let connS := fun B : Finset (Sym2 (Fin n)) =>
    ∀ v ∈ S, (fromEdgeSet (↑B : Set (Sym2 (Fin n)))).Reachable zero v
  let connSc := fun C : Finset (Sym2 (Fin n)) =>
    ∀ v, v ∉ S → (fromEdgeSet (↑C : Set (Sym2 (Fin n)))).Reachable one v
  let src := E.powerset.filter (fun A => componentOfZero (by omega : 1 ≤ n) A = S ∧
    ∀ v, v ∉ S → (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Reachable one v)
  let tgt := (E_S.powerset.filter connS) ×ˢ (E_Sc.powerset.filter connSc)
  -- Edge class disjointness
  have hE_disj : Disjoint E_S E_Sc := by
    rw [Finset.disjoint_filter]; intro e _ h1 h2
    induction e using Sym2.inductionOn with
    | _ a b => exact absurd (h1 a b rfl).1 (h2 a b rfl).1
  -- A ⊆ E_S ∪ E_Sc when C(A) = S
  have hA_sub : ∀ A ∈ src, A ⊆ E_S ∪ E_Sc := by
    intro A hA e he
    have ⟨hpw, heq, _⟩ := Finset.mem_filter.mp hA
    have hcond := (componentOfZero_eq_iff (by omega : 1 ≤ n) A S hS0 hSn).mp heq
    have he_E := Finset.mem_powerset.mp hpw he
    induction e using Sym2.inductionOn with
    | _ a b =>
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he_E,
          fun u v h => by rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                          <;> exact ⟨‹_›, ‹_›⟩⟩)
      · exact absurd rfl (hcond.1 _ he a ha b hb)
      · exact absurd Sym2.eq_swap (hcond.1 _ he b hb a ha)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he_E,
          fun u v h => by rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                          <;> exact ⟨‹_›, ‹_›⟩⟩)
  -- Card decomposition
  have hA_card : ∀ A ∈ src, A.card = (A ∩ E_S).card + (A ∩ E_Sc).card := by
    intro A hA
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left
      Finset.inter_subset_right (Finset.disjoint_of_subset_right
        Finset.inter_subset_right hE_disj)),
      ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr (hA_sub A hA)]
  -- A ∩ E_S has same edges as A.filter(pred)
  have hA_S_eq : ∀ A ∈ src, ↑(A ∩ E_S) =
      (↑(A.filter (fun e => ∀ u₁ u₂, e = s(u₁, u₂) → u₁ ∈ S ∧ u₂ ∈ S)) :
        Set (Sym2 (Fin n))) := by
    intro A hA; ext e; simp only [Finset.mem_coe, Finset.mem_inter, Finset.mem_filter]
    exact ⟨fun ⟨he, hf⟩ => ⟨he, (Finset.mem_filter.mp hf).2⟩,
           fun ⟨he, hp⟩ => ⟨he, Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1 he, hp⟩⟩⟩
  -- Walk-in-Sc helper: walks starting in Sᶜ stay in Sᶜ when no cross-edges
  have walk_in_Sc (A : Finset (Sym2 (Fin n)))
      (ha : ∀ e ∈ A, ∀ u ∈ S, ∀ v ∉ S, e ≠ s(u, v)) :
      ∀ (a b : Fin n), (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Walk a b →
      a ∉ S → b ∉ S ∧ (fromEdgeSet (↑(A ∩ E_Sc) : Set (Sym2 (Fin n)))).Reachable a b := by
    intro a b walk ha_Sc
    induction walk with
    | nil => exact ⟨ha_Sc, @Reachable.refl _ (fromEdgeSet _) _⟩
    | @cons x y z hadj _ ih =>
      have hy_Sc : y ∉ S := by
        by_contra hy
        rw [fromEdgeSet_adj] at hadj
        exact ha _ (Finset.mem_coe.mp hadj.1) y hy x ha_Sc (Sym2.eq_swap)
      obtain ⟨hz_Sc, hreach⟩ := ih hy_Sc
      refine ⟨hz_Sc, ?_⟩
      rw [fromEdgeSet_adj] at hadj
      have : (fromEdgeSet (↑(A ∩ E_Sc) : Set (Sym2 (Fin n)))).Adj x y := by
        rw [fromEdgeSet_adj]; exact ⟨Finset.mem_coe.mpr (Finset.mem_inter.mpr
          ⟨Finset.mem_coe.mp hadj.1, Finset.mem_filter.mpr
            ⟨by simp [edgeFinset_top, E, Set.mem_toFinset, Sym2.mem_diagSet, hadj.2],
             fun u v h => by
               rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
               · exact ⟨ha_Sc, hy_Sc⟩
               · exact ⟨hy_Sc, ha_Sc⟩⟩⟩), hadj.2⟩
      exact this.reachable.trans hreach
  -- Bijection
  have hbij : ∑ A ∈ src, (1 - q) ^ A.card * q ^ (E.card - A.card) =
      ∑ p ∈ tgt, (1 - q) ^ (p.1.card + p.2.card) *
        q ^ (E.card - (p.1.card + p.2.card)) := by
    apply Finset.sum_nbij' (fun A => (A ∩ E_S, A ∩ E_Sc)) (fun p => p.1 ∪ p.2)
    · -- forward lands in tgt
      intro A hA
      have ⟨hpw, heq, hSc_reach⟩ := Finset.mem_filter.mp hA
      have hcond := (componentOfZero_eq_iff (by omega : 1 ≤ n) A S hS0 hSn).mp heq
      rw [Finset.mem_product]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        fun v hv => (hA_S_eq A hA) ▸ hcond.2 v hv⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
          fun v hv => ?_⟩⟩
      obtain ⟨walk⟩ := hSc_reach v hv
      exact (walk_in_Sc A hcond.1 one v walk hS1).2
    · -- backward lands in src
      intro ⟨B, C⟩ hp
      rw [Finset.mem_product] at hp
      have hB_sub := Finset.mem_powerset.mp (Finset.mem_of_mem_filter _ hp.1)
      have hB_conn := (Finset.mem_filter.mp hp.1).2
      have hC_sub := Finset.mem_powerset.mp (Finset.mem_of_mem_filter _ hp.2)
      have hC_conn := (Finset.mem_filter.mp hp.2).2
      rw [Finset.mem_filter, Finset.mem_powerset]; refine ⟨fun e he => ?_, ?_, ?_⟩
      · rw [Finset.mem_union] at he; cases he with
        | inl h => exact Finset.filter_subset _ _ (hB_sub h)
        | inr h => exact Finset.filter_subset _ _ (hC_sub h)
      · rw [componentOfZero_eq_iff (by omega : 1 ≤ n) _ S hS0 hSn]; constructor
        · intro e he u hu v hv heqe; rw [Finset.mem_union] at he; cases he with
          | inl h => exact hv ((Finset.mem_filter.mp (hB_sub h)).2 u v heqe).2
          | inr h => exact absurd ((Finset.mem_filter.mp (hC_sub h)).2 u v heqe).1 (not_not.mpr hu)
        · intro v hv; have := hB_conn v hv
          exact this.mono (fun a b hab => by
            rw [fromEdgeSet_adj] at hab ⊢
            exact ⟨Finset.mem_coe.mpr (Finset.mem_filter.mpr
              ⟨Finset.mem_union_left _ (Finset.mem_coe.mp hab.1),
               (Finset.mem_filter.mp (hB_sub (Finset.mem_coe.mp hab.1))).2⟩), hab.2⟩)
      · intro v hv
        have := hC_conn v hv
        exact this.mono (fun a b hab => by
          rw [fromEdgeSet_adj] at hab ⊢
          exact ⟨Finset.mem_coe.mpr (Finset.mem_union_right _
            (Finset.mem_coe.mp hab.1)), hab.2⟩)
    · -- left inverse
      intro A hA
      rw [← Finset.inter_union_distrib_left]
      exact Finset.inter_eq_left.mpr (hA_sub A hA)
    · -- right inverse
      intro ⟨B, C⟩ hp
      rw [Finset.mem_product] at hp
      have hB := Finset.mem_powerset.mp (Finset.mem_of_mem_filter _ hp.1)
      have hC := Finset.mem_powerset.mp (Finset.mem_of_mem_filter _ hp.2)
      simp only [Prod.mk.injEq]; constructor
      · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hB]
        rw [show C ∩ E_S = ∅ from
          Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_of_subset_left hC hE_disj.symm)]
        exact Finset.union_empty _
      · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hC]
        rw [show B ∩ E_Sc = ∅ from
          Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_of_subset_left hB hE_disj)]
        exact Finset.empty_union _
    · -- summands equal
      intro A hA; rw [hA_card A hA]
  -- Edge count decomposition
  have hE_card : E.card = E_S.card + S.card * (n - S.card) + E_Sc.card := by
    have hsub : E_S ∪ E_Sc ⊆ E :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have h1 : (E \ (E_S ∪ E_Sc)).card + (E_S ∪ E_Sc).card = E.card := by
      rw [Finset.card_sdiff_add_card, Finset.union_eq_left.mpr hsub]
    have h2 := Finset.card_union_of_disjoint hE_disj
    have h3 : (E \ (E_S ∪ E_Sc)).card = S.card * (n - S.card) := by
      rw [show S.card * (n - S.card) = (S ×ˢ Sᶜ).card from by
        rw [Finset.card_product, Finset.card_compl, Fintype.card_fin]]
      symm; apply Finset.card_bij (fun ⟨u, v⟩ _ => (s(u, v) : Sym2 (Fin n)))
      · intro ⟨u, v⟩ hp; rw [Finset.mem_product] at hp
        have hv := Finset.mem_compl.mp hp.2
        rw [Finset.mem_sdiff, Finset.mem_union, not_or]; refine ⟨?_, ?_, ?_⟩
        · simp [edgeFinset_top, E, Set.mem_toFinset, Sym2.mem_diagSet,
            show u ≠ v from fun h => hv (h ▸ hp.1)]
        · intro h; exact hv ((Finset.mem_filter.mp h).2 u v rfl).2
        · intro h; exact absurd hp.1 ((Finset.mem_filter.mp h).2 u v rfl).1
      · intro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ heq
        rw [Finset.mem_product] at h₁ h₂
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact absurd h₂.1 (Finset.mem_compl.mp h₁.2)
      · intro e he; rw [Finset.mem_sdiff, Finset.mem_union, not_or] at he
        induction e using Sym2.inductionOn with
        | _ a b =>
          have hnotES : ¬(a ∈ S ∧ b ∈ S) := fun ⟨ha, hb⟩ =>
            he.2.1 (Finset.mem_filter.mpr ⟨he.1, fun u v h => by
              rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨‹_›, ‹_›⟩⟩)
          have hnotESc : ¬(a ∉ S ∧ b ∉ S) := fun ⟨ha, hb⟩ =>
            he.2.2 (Finset.mem_filter.mpr ⟨he.1, fun u v h => by
              rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨‹_›, ‹_›⟩⟩)
          by_cases ha : a ∈ S
          · exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, Finset.mem_compl.mpr
              (fun hb => hnotES ⟨ha, hb⟩)⟩, rfl⟩
          · exact ⟨(b, a), Finset.mem_product.mpr ⟨by_contra (fun hb => hnotESc ⟨ha, hb⟩),
              Finset.mem_compl.mpr ha⟩, Sym2.eq_swap⟩
    omega
  -- Factor the product sum
  have hfactor : ∑ p ∈ tgt,
      (1 - q) ^ (p.1.card + p.2.card) * q ^ (E.card - (p.1.card + p.2.card)) =
      (∑ B ∈ E_S.powerset.filter connS,
        (1 - q) ^ B.card * q ^ (E_S.card - B.card)) *
      q ^ (S.card * (n - S.card)) *
      (∑ C ∈ E_Sc.powerset.filter connSc,
        (1 - q) ^ C.card * q ^ (E_Sc.card - C.card)) := by
    have hsub_S : ∀ p ∈ tgt, p.1.card ≤ E_S.card := by
      intro p hp; rw [Finset.mem_product] at hp
      exact Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_of_mem_filter _ hp.1))
    have hsub_Sc : ∀ p ∈ tgt, p.2.card ≤ E_Sc.card := by
      intro p hp; rw [Finset.mem_product] at hp
      exact Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_of_mem_filter _ hp.2))
    have hsub : ∀ p ∈ tgt, (1 - q) ^ (p.1.card + p.2.card) *
        q ^ (E.card - (p.1.card + p.2.card)) =
        ((1 - q) ^ p.1.card * q ^ (E_S.card - p.1.card)) *
          q ^ (S.card * (n - S.card)) *
          ((1 - q) ^ p.2.card * q ^ (E_Sc.card - p.2.card)) := by
      intro p hp
      have h1 := hsub_S p hp; have h2 := hsub_Sc p hp
      rw [show E.card - (p.1.card + p.2.card) =
          (E_S.card - p.1.card) + S.card * (n - S.card) + (E_Sc.card - p.2.card) from by
        rw [hE_card]; omega]
      rw [pow_add, pow_add, pow_add]; ring
    rw [Finset.sum_congr rfl hsub, Finset.sum_product]
    simp_rw [show ∀ x y : Finset (Sym2 (Fin n)),
        (1-q)^x.card * q^(E_S.card - x.card) * q^(S.card * (n - S.card)) *
          ((1-q)^y.card * q^(E_Sc.card - y.card)) =
        (1-q)^x.card * q^(E_S.card - x.card) *
          (q^(S.card * (n - S.card)) * ((1-q)^y.card * q^(E_Sc.card - y.card)))
      from fun _ _ => by ring, ← Finset.mul_sum, ← Finset.sum_mul]; ring
  -- Rel(K_{|S|}) from S-part
  have hrel_S : ∑ B ∈ E_S.powerset.filter connS,
      (1 - q) ^ B.card * q ^ (E_S.card - B.card) =
      (⊤ : SimpleGraph (Fin S.card)).reliabilityFun q := by
    rw [show S.card = (Finset.univ.filter (· ∈ S)).card from by simp]
    exact rel_sum_of_predicate q (· ∈ S) ⟨0, by omega⟩ hS0 E_S rfl
  -- Rel(K_{n-|S|}) from Sᶜ-part
  have hrel_Sc : ∑ C ∈ E_Sc.powerset.filter connSc,
      (1 - q) ^ C.card * q ^ (E_Sc.card - C.card) =
      (⊤ : SimpleGraph (Fin (n - S.card))).reliabilityFun q := by
    rw [show n - S.card = (Finset.univ.filter (· ∉ S)).card from by
      rw [Finset.filter_not, Finset.card_sdiff]; simp]
    exact rel_sum_of_predicate q (· ∉ S) ⟨1, by omega⟩ hS1 E_Sc rfl
  -- Assembly
  rw [hbij, hfactor, hrel_S, hrel_Sc]; ring

/-! #### Step C: Split recursion assembly -/

set_option maxHeartbeats 800000 in
-- Assembly proof partitions by componentOfZero and regroups — many intermediate sets and sums.
/-- **splitRel recursion** (Equation 2.2): Conditioning on the component of terminal 0,
`splitRel(K_n; q) = ∑_{s=1}^{n-1} C(n-2,s-1) · Rel(K_s; q) · Rel(K_{n-s}; q) · q^{s(n-s)}`.

There are C(n-2, s-1) choices for the component S of terminal 0 with |S|=s
(terminal 1 is excluded), K_s and K_{n-s} must each be connected,
and all s(n-s) cross-edges must fail. -/
theorem splitRelFun_completeGraph_recursion (n : ℕ) (hn : 2 ≤ n) (q : ℝ) :
    (⊤ : SimpleGraph (Fin n)).splitRelFun ⟨0, by omega⟩ ⟨1, by omega⟩ q =
      ∑ s ∈ Finset.range (n - 1), ((n - 2).choose s : ℝ) *
        (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
        (⊤ : SimpleGraph (Fin (n - (s + 1)))).reliabilityFun q *
        q ^ ((s + 1) * (n - (s + 1))) := by
  set zero : Fin n := ⟨0, by omega⟩
  set one : Fin n := ⟨1, by omega⟩
  set E := (⊤ : SimpleGraph (Fin n)).edgeFinset
  set T := (Finset.univ (α := Finset (Fin n))).filter
    (fun S => zero ∈ S ∧ one ∉ S ∧ S.card < n)
  -- Step 1: Partition the split sum by componentOfZero
  have step1 :
      (∑ A ∈ E.powerset, (if ¬(fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Reachable zero one ∧
        ∀ w, (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Reachable zero w ∨
             (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Reachable one w then
        (1 - q) ^ A.card * q ^ (E.card - A.card) else 0)) =
      ∑ S ∈ T, ∑ A ∈ E.powerset.filter
          (fun A => componentOfZero (by omega : 1 ≤ n) A = S ∧
            ∀ v, v ∉ S → (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Reachable one v),
        (1 - q) ^ A.card * q ^ (E.card - A.card) := by
    rw [← Finset.sum_filter]
    -- The split condition determines componentOfZero A ∈ T
    have hfilt_eq : E.powerset.filter (fun (A : Finset (Sym2 (Fin n))) =>
        ¬(fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Reachable zero one ∧
        ∀ w, (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Reachable zero w ∨
             (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Reachable one w) =
        E.powerset.filter (fun (A : Finset (Sym2 (Fin n))) =>
          one ∉ componentOfZero (by omega : 1 ≤ n) A ∧
          componentOfZero (by omega) A ≠ Finset.univ ∧
          ∀ v, v ∉ componentOfZero (by omega) A →
            (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Reachable one v) := by
      apply Finset.filter_congr; intro A _
      constructor
      · intro ⟨hnr, hall⟩
        refine ⟨fun h => hnr (Finset.mem_filter.mp h).2, ?_, fun v hv => ?_⟩
        · intro heq
          exact hnr ((Finset.eq_univ_iff_forall.mp heq one |> Finset.mem_filter.mp).2)
        · exact (hall v).resolve_left (fun h => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      · intro ⟨h1, _, h3⟩
        refine ⟨fun h => h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩), fun w => ?_⟩
        by_cases hw : (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Reachable zero w
        · left; exact hw
        · right; exact h3 w (fun h => hw (Finset.mem_filter.mp h).2)
    rw [hfilt_eq]
    rw [← Finset.sum_fiberwise_of_maps_to (g := componentOfZero (by omega : 1 ≤ n)) (t := T)
      (fun A hA => by
        have ⟨_, h1, hne, _⟩ := Finset.mem_filter.mp hA
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, zero_mem_componentOfZero _ _, h1, ?_⟩
        by_contra hle; push_neg at hle
        have hub := Finset.card_le_univ (componentOfZero (by omega : 1 ≤ n) A)
        rw [Fintype.card_fin] at hub
        exact hne (Finset.eq_univ_of_card _ (by rw [Fintype.card_fin]; omega)))]
    apply Finset.sum_congr rfl; intro S hS
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext A; simp only [Finset.mem_filter, and_assoc]
    constructor
    · -- From: A ∈ E.powerset ∧ one ∉ C(A) ∧ C(A) ≠ univ ∧ (∀ v ∉ C(A), Reach 1 v) ∧ C(A) = S
      -- To: A ∈ E.powerset ∧ C(A) = S ∧ (∀ v ∉ S, Reach 1 v)
      exact fun ⟨h1, _, _, h4, h5⟩ =>
        ⟨h1, h5, fun v hv => h4 v (h5 ▸ hv)⟩
    · -- From: A ∈ E.powerset ∧ C(A) = S ∧ (∀ v ∉ S, Reach 1 v)
      -- To: the 5-tuple
      intro ⟨h1, h3, h4⟩
      have ⟨_, _, hS1', hSn⟩ := Finset.mem_filter.mp hS
      refine ⟨h1, by rw [h3]; exact hS1', ?_, fun v hv => h4 v (h3 ▸ hv), h3⟩
      rw [h3]; intro heq
      rw [heq, Finset.card_univ, Fintype.card_fin] at hSn; omega
  -- Step 2: Apply split_fiber_sum_eq to each fiber
  have step2 :
      (∑ S ∈ T, ∑ A ∈ E.powerset.filter
          (fun A => componentOfZero (by omega : 1 ≤ n) A = S ∧
            ∀ v, v ∉ S → (fromEdgeSet (↑A : Set (Sym2 (Fin n)))).Reachable one v),
        (1 - q) ^ A.card * q ^ (E.card - A.card)) =
      ∑ S ∈ T, (⊤ : SimpleGraph (Fin S.card)).reliabilityFun q *
        (⊤ : SimpleGraph (Fin (n - S.card))).reliabilityFun q *
        q ^ (S.card * (n - S.card)) := by
    apply Finset.sum_congr rfl; intro S hS
    have ⟨_, hS0, hS1', hSn⟩ := Finset.mem_filter.mp hS
    exact split_fiber_sum_eq hn q S hS0 hS1' hSn
  -- Step 3: Regroup by |S|
  have step3 :
      (∑ S ∈ T, (⊤ : SimpleGraph (Fin S.card)).reliabilityFun q *
        (⊤ : SimpleGraph (Fin (n - S.card))).reliabilityFun q *
        q ^ (S.card * (n - S.card))) =
      ∑ s ∈ Finset.range (n - 1), ((n - 2).choose s : ℝ) *
        (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
        (⊤ : SimpleGraph (Fin (n - (s + 1)))).reliabilityFun q *
        q ^ ((s + 1) * (n - (s + 1))) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun S => S.card - 1) (t := Finset.range (n - 1))
      (fun S hS => by
        have ⟨_, h0, _, hlt⟩ := Finset.mem_filter.mp hS
        rw [Finset.mem_range]; change S.card - 1 < n - 1
        have : 1 ≤ S.card := Finset.card_pos.mpr ⟨_, h0⟩
        omega)]
    apply Finset.sum_congr rfl
    intro s hs; rw [Finset.mem_range] at hs
    have hfiber_eq : T.filter (fun S => S.card - 1 = s) =
        (Finset.univ (α := Finset (Fin n))).filter
          (fun S => zero ∈ S ∧ one ∉ S ∧ S.card = s + 1) := by
      ext S; simp only [Finset.mem_filter, Finset.mem_univ, true_and, T]
      constructor
      · intro ⟨⟨h0, h1, hlt⟩, hcard⟩
        exact ⟨h0, h1, by have := Finset.card_pos.mpr ⟨_, h0⟩; omega⟩
      · intro ⟨h0, h1, hcard⟩
        exact ⟨⟨h0, h1, by omega⟩, by have := Finset.card_pos.mpr ⟨_, h0⟩; omega⟩
    rw [hfiber_eq]
    set F := (Finset.univ (α := Finset (Fin n))).filter
      (fun S => zero ∈ S ∧ one ∉ S ∧ S.card = s + 1)
    have hsum_rw : (∑ S ∈ F,
        (⊤ : SimpleGraph (Fin S.card)).reliabilityFun q *
        (⊤ : SimpleGraph (Fin (n - S.card))).reliabilityFun q *
        q ^ (S.card * (n - S.card))) =
        ∑ S ∈ F, (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
          (⊤ : SimpleGraph (Fin (n - (s + 1)))).reliabilityFun q *
          q ^ ((s + 1) * (n - (s + 1))) :=
      Finset.sum_congr rfl fun S hS => by
        rw [show S.card = s + 1 from (Finset.mem_filter.mp hS).2.2.2]
    rw [hsum_rw, Finset.sum_const, count_subsets_split hn s hs, nsmul_eq_mul]
    ring
  -- Assembly: unfold splitRelFun, reconcile decidability instances, apply steps
  change (⊤ : SimpleGraph (Fin n)).splitRelFun zero one q = _
  unfold SimpleGraph.splitRelFun
  refine Eq.trans ?_ (step1.trans (step2.trans step3))
  apply Finset.sum_congr rfl; intro A _; split_ifs <;> rfl

/-! ### The bounding sequence b_n -/

/-- The bounding sequence `b_n` for the split-reliability tail sum:
`seqB(r, n) = ∑_{s=2}^{n-2} C(n-2, s-1) · r^{s(n-s) - (n-1)}`.

We use this for `n ≥ 4`; for smaller n the sum is empty. -/
def seqB (r : ℝ) (n : ℕ) : ℝ :=
  ∑ s ∈ Finset.Ico 2 (n - 1), ((n - 2).choose (s - 1) : ℝ) * r ^ (s * (n - s) - (n - 1))

lemma seqB_nonneg (hr : 0 ≤ r) (n : ℕ) : 0 ≤ seqB r n := by
  apply Finset.sum_nonneg; intro s _
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr _)

/-- `seqB(r, n) → 0` as `n → ∞`, for `0 ≤ r < 1`.

The paper's proof: rewrite `b_{n+2} = ∑_{s=1}^{n-1} C(n,s) · r^{s(n-s)}`, then use
the pairing `s ↔ n-s`, bound `r^{s(n-s)} ≤ (r^{n/2})^s`, and apply the binomial
theorem to get `≤ 2[(1 + r^{n/2})^n - 1] → 0`. -/
private lemma tendsto_pow_exp_sub_one {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => (1 + r ^ (n / 2)) ^ n - 1) atTop (nhds 0) := by
  have hkey : Tendsto (fun n : ℕ => (↑n : ℝ) * r ^ (n / 2)) atTop (nhds 0) := by
    have h1 : Tendsto (fun k : ℕ => (2 * (↑k : ℝ) + 1) * r ^ k) atTop (nhds 0) := by
      have ha := (tendsto_self_mul_const_pow_of_lt_one hr hr1).const_mul 2
      have hb := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
      simp only [show (2 : ℝ) * 0 = 0 from by ring, show (0 : ℝ) * 2 + 0 = 0 from by ring] at ha
      have := ha.add hb; simp only [show (0 : ℝ) + 0 = 0 from by ring] at this
      exact this.congr (fun k => by ring)
    have h2 : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
      rw [Filter.tendsto_atTop]; intro b
      exact Filter.eventually_atTop.mpr ⟨2 * b, fun n hn => by omega⟩
    apply squeeze_zero (fun n => by positivity)
      (fun n => by
        calc (↑n : ℝ) * r ^ (n / 2)
            ≤ (2 * ↑(n / 2) + 1) * r ^ (n / 2) := by
              gcongr; exact_mod_cast show n ≤ 2 * (n / 2) + 1 by omega)
    exact h1.comp h2
  apply squeeze_zero
    (fun n => sub_nonneg.mpr (one_le_pow₀ (by linarith [pow_nonneg hr (n / 2)])))
    (fun n => by
      calc (1 + r ^ (n / 2)) ^ n - 1
          ≤ (Real.exp (r ^ (n / 2))) ^ n - 1 := by
            gcongr; linarith [Real.add_one_le_exp (r ^ (n / 2))]
        _ = Real.exp (↑n * r ^ (n / 2)) - 1 := by
              congr 1; exact (Real.exp_nat_mul _ _).symm)
  have : Tendsto (fun n : ℕ => Real.exp (↑n * r ^ (n / 2)) - 1) atTop (nhds 0) := by
    have hexp := (Real.continuous_exp.tendsto 0).comp (by simpa using hkey)
    simp only [Function.comp, Real.exp_zero] at hexp
    simpa using hexp.sub_const 1
  exact this

set_option maxHeartbeats 400000 in
theorem tendsto_seqB_zero (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (seqB r) atTop (nhds 0) := by
  -- Shift: it suffices to show seqB r (n + 4) → 0
  suffices h : Tendsto (fun n => seqB r (n + 4)) atTop (nhds 0) by
    exact (Filter.tendsto_add_atTop_iff_nat (f := seqB r) 4).mp h
  -- Set m = n + 2 so seqB(r, m+2) = ∑_{j ∈ Icc 1 (m-1)} C(m,j)·r^{j(m-j)}
  -- Bound this by 2 · ((1 + r^{m/2})^m - 1) using the pairing argument.
  have hbound : ∀ n, seqB r (n + 4) ≤
      2 * ((1 + r ^ ((n + 2) / 2)) ^ (n + 2) - 1) := by
    intro n; set m := n + 2
    unfold seqB
    simp only [show n + 4 - 1 = n + 3 from by omega,
               show n + 4 - 2 = m from by omega]
    -- Reindex: s ∈ Ico 2 (n+3) ↦ j = s-1 ∈ Icc 1 (m-1)
    -- Key: exponent s*(n+4-s)-(n+3) = (s-1)*(m-(s-1)) for s ∈ [2, m]
    have hreindex : ∑ s ∈ Finset.Ico 2 (n + 3),
        (m.choose (s - 1) : ℝ) * r ^ (s * (n + 4 - s) - (n + 3)) =
        ∑ j ∈ Finset.Icc 1 (m - 1),
        (m.choose j : ℝ) * r ^ (j * (m - j)) := by
      apply Finset.sum_nbij' (· - 1) (· + 1)
      · intro s hs; simp only [Finset.mem_Ico] at hs
        simp only [Finset.mem_Icc]; omega
      · intro j hj; simp only [Finset.mem_Icc] at hj
        simp only [Finset.mem_Ico]; omega
      · intro s hs; simp only [Finset.mem_Ico] at hs; omega
      · intro j hj; simp only [Finset.mem_Icc] at hj; omega
      · intro s hs
        simp only [Finset.mem_Ico] at hs
        have hs2 : 2 ≤ s := hs.1
        have hsm : s ≤ n + 2 := by omega
        show (m.choose (s - 1) : ℝ) * r ^ (s * (n + 4 - s) - (n + 3)) =
             (m.choose (s - 1) : ℝ) * r ^ ((s - 1) * (m - (s - 1)))
        congr 1
        congr 1
        -- Need: s*(n+4-s)-(n+3) = (s-1)*(m-(s-1)) in ℕ
        -- Both sides equal s*n + 4*s - s² - n - 3 (in ℤ, and ≥ 0)
        -- LHS: s*(n+4-s) = s*n + 4*s - s*s since s ≤ n+2 < n+4
        -- s*(n+4-s)-(n+3) ≥ 2*2-(n+3) when s=2, n+4-s=n+2: 2*(n+2)-(n+3)=n+1≥0
        -- RHS: (s-1)*(m-(s-1)) = (s-1)*(n+3-s)
        -- Show equality by lifting to ℤ
        have h_le1 : s ≤ n + 4 := by omega
        have h_le2 : s - 1 ≤ m := by omega
        have h_le3 : n + 3 ≤ s * (n + 4 - s) := by
          -- s*(n+4-s) ≥ 2*(n+4-s) and ≥ s*2, so 2*s*(n+4-s) ≥ 2n+8, hence ≥ n+4
          have h1 : s * 2 ≤ s * (n + 4 - s) :=
            Nat.mul_le_mul_left s (by omega)
          have h2 : 2 * (n + 4 - s) ≤ s * (n + 4 - s) :=
            Nat.mul_le_mul_right _ hs2
          omega
        zify [h_le1, h_le2, h_le3, show 1 ≤ s from by omega]
        simp only [show (m : ℤ) = ↑n + 2 from by omega]; ring
    rw [hreindex]
    -- Now bound ∑_{j ∈ Icc 1 (m-1)} C(m,j)·r^{j(m-j)} ≤ 2·((1+x)^m - 1) where x = r^{m/2}
    set x := r ^ (m / 2)
    -- Use delta functions δ_le(j) = [j ≤ m/2]
    set g : ℕ → ℝ := fun j => (m.choose j : ℝ) * r ^ (j * (m - j)) with hg_def
    let δ_le : ℕ → ℝ := fun j => if j ≤ m / 2 then 1 else 0
    change ∑ j ∈ Finset.Icc 1 (m - 1), g j ≤ 2 * ((1 + x) ^ m - 1)
    -- Step 1: g(j) ≤ g(j)·(δ_le(j) + δ_le(m-j))
    -- since for j ∈ [1, m-1], at least one of j ≤ m/2 or m-j ≤ m/2 holds
    have hg_nn : ∀ j, 0 ≤ g j := fun j =>
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr _)
    have hstep1 : ∑ j ∈ Finset.Icc 1 (m - 1), g j ≤
        ∑ j ∈ Finset.Icc 1 (m - 1), g j * (δ_le j + δ_le (m - j)) := by
      apply Finset.sum_le_sum; intro j hj
      simp only [Finset.mem_Icc] at hj
      calc g j = g j * 1 := (mul_one _).symm
        _ ≤ g j * (δ_le j + δ_le (m - j)) := by
          apply mul_le_mul_of_nonneg_left _ (hg_nn j)
          simp only [δ_le]
          split_ifs <;> norm_num <;> omega
    -- Step 2: distribute
    have hstep2 : ∑ j ∈ Finset.Icc 1 (m - 1), g j * (δ_le j + δ_le (m - j)) =
        (∑ j ∈ Finset.Icc 1 (m - 1), g j * δ_le j) +
        (∑ j ∈ Finset.Icc 1 (m - 1), g j * δ_le (m - j)) := by
      rw [← Finset.sum_add_distrib]; congr 1; ext j; ring
    -- Step 3: reindex j → m-j in second sum
    have hstep3 : ∑ j ∈ Finset.Icc 1 (m - 1), g j * δ_le (m - j) =
        ∑ j ∈ Finset.Icc 1 (m - 1), g (m - j) * δ_le j := by
      apply Finset.sum_nbij' (fun j => m - j) (fun j => m - j)
      · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
      · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
      · intro j hj; simp only [Finset.mem_Icc] at hj
        show m - (m - j) = j; omega
      · intro j hj; simp only [Finset.mem_Icc] at hj
        show m - (m - j) = j; omega
      · intro j hj; simp only [Finset.mem_Icc] at hj
        show g j * δ_le (m - j) = g (m - (m - j)) * δ_le (m - j)
        rw [Nat.sub_sub_self (by omega : j ≤ m)]
    -- Step 4: g(m-j) = g(j) because C(m,m-j)=C(m,j) and (m-j)·j = j·(m-j)
    have hstep4 : ∀ j ∈ Finset.Icc 1 (m - 1), g (m - j) * δ_le j = g j * δ_le j := by
      intro j hj; simp only [Finset.mem_Icc] at hj
      have hgmj : g (m - j) = g j := by
        simp only [hg_def]
        have hsub : m - (m - j) = j := Nat.sub_sub_self (by omega)
        rw [Nat.choose_symm (by omega), show (m - j) * (m - (m - j)) = j * (m - j)
          from by rw [hsub]; ring]
      rw [hgmj]
    -- So the two halves are equal: sum g·δ_le(m-j) = sum g·δ_le
    have hstep5 : ∑ j ∈ Finset.Icc 1 (m - 1), g j * δ_le (m - j) =
        ∑ j ∈ Finset.Icc 1 (m - 1), g j * δ_le j := by
      rw [hstep3]; exact Finset.sum_congr rfl hstep4
    -- Step 6: exponent bound when δ_le(j) ≠ 0: j ≤ m/2, so j(m-j) ≥ j·(m/2),
    -- hence r^{j(m-j)} ≤ (r^{m/2})^j = x^j
    have hstep6 : ∀ j ∈ Finset.Icc 1 (m - 1),
        g j * δ_le j ≤ (m.choose j : ℝ) * x ^ j := by
      intro j hj; simp only [δ_le, hg_def]
      split_ifs with h
      · simp only [mul_one]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        calc r ^ (j * (m - j)) ≤ r ^ (m / 2 * j) := by
              apply pow_le_pow_of_le_one hr hr1.le
              have : m / 2 ≤ m - j := by omega
              calc m / 2 * j ≤ (m - j) * j := Nat.mul_le_mul_right j this
                _ = j * (m - j) := by ring
          _ = x ^ j := by rw [show x = r ^ (m / 2) from rfl, ← pow_mul]
      · simp; positivity
    -- Step 7: extend range to get ≤ (1+x)^m - 1
    have hstep7 : ∑ j ∈ Finset.Icc 1 (m - 1), (m.choose j : ℝ) * x ^ j ≤
        (1 + x) ^ m - 1 := by
      have hsub : Finset.Icc 1 (m - 1) ⊆ Finset.Icc 1 m :=
        Finset.Icc_subset_Icc_right (by omega)
      have hnn : ∀ j ∈ Finset.Icc 1 m, 0 ≤ (m.choose j : ℝ) * x ^ j :=
        fun j _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (pow_nonneg hr _) _)
      have h1 : ∑ j ∈ Finset.Icc 1 (m - 1), (m.choose j : ℝ) * x ^ j ≤
          ∑ j ∈ Finset.Icc 1 m, (m.choose j : ℝ) * x ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hnn j hj)
      have h2 : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * x ^ j = (1 + x) ^ m := by
        rw [show (1 : ℝ) + x = x + 1 from by ring, add_pow]; simp [one_pow, mul_one, mul_comm]
      have h3 : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * x ^ j =
          1 + ∑ j ∈ Finset.Icc 1 m, (m.choose j : ℝ) * x ^ j := by
        rw [show Finset.range (m + 1) = {0} ∪ Finset.Icc 1 m from by
          ext j; simp [Finset.mem_Icc]; omega]
        rw [Finset.sum_union (by
          rw [Finset.disjoint_left]; intro a; simp [Finset.mem_Icc]; omega)]; simp
      linarith
    -- Assembly
    calc ∑ j ∈ Finset.Icc 1 (m - 1), g j
        ≤ ∑ j ∈ Finset.Icc 1 (m - 1), g j * (δ_le j + δ_le (m - j)) := hstep1
      _ = (∑ j ∈ Finset.Icc 1 (m - 1), g j * δ_le j) +
          (∑ j ∈ Finset.Icc 1 (m - 1), g j * δ_le (m - j)) := hstep2
      _ = (∑ j ∈ Finset.Icc 1 (m - 1), g j * δ_le j) +
          (∑ j ∈ Finset.Icc 1 (m - 1), g j * δ_le j) := by rw [hstep5]
      _ = 2 * ∑ j ∈ Finset.Icc 1 (m - 1), g j * δ_le j := by ring
      _ ≤ 2 * ∑ j ∈ Finset.Icc 1 (m - 1), (m.choose j : ℝ) * x ^ j := by
          apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep6) (by positivity)
      _ ≤ 2 * ((1 + x) ^ m - 1) := by
          apply mul_le_mul_of_nonneg_left hstep7 (by positivity)
  -- Show 2 · ((1 + r^{(n+2)/2})^{n+2} - 1) → 0
  have htail : Tendsto (fun n => 2 * ((1 + r ^ ((n + 2) / 2)) ^ (n + 2) - 1))
      atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ => (1 + r ^ ((n + 2) / 2)) ^ (n + 2) - 1) atTop (nhds 0) := by
      have := tendsto_pow_exp_sub_one hr hr1
      exact this.comp (tendsto_add_atTop_nat 2)
    rw [show (0 : ℝ) = 2 * 0 from by ring]
    exact Filter.Tendsto.const_mul 2 h0
  -- Apply squeeze_zero
  exact squeeze_zero (fun n => seqB_nonneg hr (n + 4)) hbound htail

/-! ### Split-reliability limit -/

/-- **Lemma 2.1 (second part)**: For `|q| < 1` and `q ≠ 0`,
`splitRel_{0,1}(Kₙ; q) / q^{n-1} → 2` as `n → ∞`.

We index by `n + 2` so that the graph always has ≥ 2 vertices and terminals 0, 1 exist.

**Proof outline**: From the recursion, extracting the `s = 1` and `s = n - 1` terms:
`splitRel(K_{n+2}) / q^{n+1} = 2 · Rel(K_{n+1}) + (tail bounded by M² · seqB)`.
Since `Rel(K_{n+1}) → 1` and `seqB → 0`, the limit is 2. -/
-- Rel(K_1; q) = 1
private lemma rel_one (q : ℝ) :
    (⊤ : SimpleGraph (Fin 1)).reliabilityFun q = 1 := by
  -- Use the recursion: Rel(K_1) = 1 - ∑(empty) = 1
  rw [reliabilityFun_completeGraph_recursion 1 (by omega) q]
  simp

set_option maxHeartbeats 800000 in
theorem lim_srel_completeGraph_normalized (q : ℝ) (hq : |q| < 1) (hq0 : q ≠ 0) :
    Tendsto
      (fun n => (⊤ : SimpleGraph (Fin (n + 2))).splitRelFun
        ⟨0, by omega⟩ ⟨1, by omega⟩ q / q ^ (n + 1))
      atTop (nhds 2) := by
  -- Strategy: Write splitRel/q^{n+1} = 2·Rel(K_{n+1}) + tail, show both parts converge.
  -- Since Rel → 1, 2·Rel → 2. Show tail → 0.
  -- The tail bound uses M² · seqB → 0.
  -- Helper: q^{n+1} ≠ 0
  have hq_ne : ∀ n : ℕ, q ^ (n + 1) ≠ 0 := fun n => pow_ne_zero _ hq0
  -- Helper: Rel(K_1; q) = 1
  have hrel1 : (⊤ : SimpleGraph (Fin 1)).reliabilityFun q = 1 := rel_one q
  -- Get uniform bound
  obtain ⟨M, hM_pos, hM⟩ := reliabilityFun_completeGraph_bounded q hq
  -- Key decomposition: for each n,
  -- splitRel(K_{n+2})/q^{n+1} = 2·Rel(K_{n+1}) + tail(n)
  -- where |tail(n)| ≤ M² · seqB(|q|, n+2)
  -- Define the "tail" function:
  -- tail(n) = splitRel(K_{n+2})/q^{n+1} - 2·Rel(K_{n+1})
  -- We will show tail → 0 using the recursion and the seqB bound.
  -- Step 1: Show tail → 0
  -- Using Metric.tendsto_atTop for both tail → 0 and Rel → 1
  -- Then the original function = tail + 2·Rel → 0 + 2 = 2
  -- Approach: show the limit is 2 using Metric.tendsto_atTop directly.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get N₁: |Rel(K_n) - 1| < ε/4 for n ≥ N₁
  have hrel_tendsto := lim_rel_completeGraph q hq
  rw [Metric.tendsto_atTop] at hrel_tendsto
  obtain ⟨N₁, hN₁⟩ := hrel_tendsto (ε / 4) (by linarith)
  -- Get N₂: M² · seqB(|q|, n) < ε/2 for n ≥ N₂
  have hseqB_tendsto := tendsto_seqB_zero (abs_nonneg q) hq
  rw [Metric.tendsto_atTop] at hseqB_tendsto
  obtain ⟨N₂, hN₂⟩ := hseqB_tendsto (ε / (2 * M ^ 2 + 2)) (by positivity)
  use max N₁ (max N₂ 1)
  intro n hn
  have hn1 : 1 ≤ n := by omega
  rw [Real.dist_eq]
  -- Rewrite splitRel using recursion
  -- Use recursion
  rw [splitRelFun_completeGraph_recursion (n + 2) (by omega) q]
  -- Abbreviate: n+2-1=n+1, n+2-2=n
  -- First simplify: n+2-1=n+1 and n+2-2=n in the goal
  show |(∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) *
      (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
      (⊤ : SimpleGraph (Fin (n + 2 - (s + 1)))).reliabilityFun q *
      q ^ ((s + 1) * (n + 2 - (s + 1)))) / q ^ (n + 1) - 2| < ε
  -- Now the goal uses n+1-s in Fin types.
  -- Bound |Rel(K_{n+1}) - 1|
  have hRn1 : |(⊤ : SimpleGraph (Fin (n + 1))).reliabilityFun q - 1| < ε / 4 := by
    have := hN₁ (n + 1) (by omega); rwa [Real.dist_eq] at this
  -- Bound seqB(|q|, n+2)
  have hseqB_bound : seqB |q| (n + 2) < ε / (2 * M ^ 2 + 2) := by
    have h := hN₂ (n + 2) (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (seqB_nonneg (abs_nonneg q) _)] at h; exact h
  -- Key tail bound
  have htail : |(∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) *
      (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
      (⊤ : SimpleGraph (Fin (n + 2 - (s + 1)))).reliabilityFun q *
      q ^ ((s + 1) * (n + 2 - (s + 1)))) / q ^ (n + 1) -
    2 * (⊤ : SimpleGraph (Fin (n + 1))).reliabilityFun q| ≤
    M ^ 2 * seqB |q| (n + 2) := by
    -- Let g be the summand function
    let g : ℕ → ℝ := fun s => (n.choose s : ℝ) *
      (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
      (⊤ : SimpleGraph (Fin (n + 2 - (s + 1)))).reliabilityFun q *
      q ^ ((s + 1) * (n + 2 - (s + 1)))
    -- Step 1: Split range(n+1) = {0} ∪ Ico 1 n ∪ {n}
    have hrange_split : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 n ∪ {n} := by
      ext s; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_Ico]; omega
    have hdisj1 : Disjoint ({0} ∪ Finset.Ico 1 n : Finset ℕ) ({n} : Finset ℕ) := by
      rw [Finset.disjoint_left]; intro s hs
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico] at hs ⊢; omega
    have hdisj2 : Disjoint ({0} : Finset ℕ) (Finset.Ico 1 n) := by
      rw [Finset.disjoint_left]; intro s hs
      simp only [Finset.mem_singleton, Finset.mem_Ico] at hs ⊢; omega
    -- Step 2: g(0) and g(n) both equal Rel(K_{n+1}) * q^{n+1}
    have hg0 : g 0 = (⊤ : SimpleGraph (Fin (n + 1))).reliabilityFun q * q ^ (n + 1) := by
      show (n.choose 0 : ℝ) * (⊤ : SimpleGraph (Fin 1)).reliabilityFun q *
        (⊤ : SimpleGraph (Fin (n + 2 - 1))).reliabilityFun q *
        q ^ (1 * (n + 2 - 1)) = _
      have h1 : n + 2 - 1 = n + 1 := by omega
      have h2 : 1 * (n + 1) = n + 1 := by omega
      rw [h1, h2, Nat.choose_zero_right, Nat.cast_one, one_mul, hrel1, one_mul]
    have hgn : g n = (⊤ : SimpleGraph (Fin (n + 1))).reliabilityFun q * q ^ (n + 1) := by
      show (n.choose n : ℝ) * (⊤ : SimpleGraph (Fin (n + 1))).reliabilityFun q *
        (⊤ : SimpleGraph (Fin (n + 2 - (n + 1)))).reliabilityFun q *
        q ^ ((n + 1) * (n + 2 - (n + 1))) = _
      have h1 : n + 2 - (n + 1) = 1 := by omega
      have h2 : (n + 1) * 1 = n + 1 := by omega
      rw [h1, h2, Nat.choose_self, Nat.cast_one, one_mul, hrel1, mul_one]
    -- Step 3: Rewrite sum using the split
    rw [hrange_split, Finset.sum_union hdisj1, Finset.sum_union hdisj2,
      Finset.sum_singleton, Finset.sum_singleton]
    -- After sum_singleton, the singletons evaluate to g 0 and g n
    change |(g 0 + ∑ s ∈ Finset.Ico 1 n, g s + g n) / q ^ (n + 1) -
      2 * (⊤ : SimpleGraph (Fin (n + 1))).reliabilityFun q| ≤ _
    rw [hg0, hgn]
    -- Now the goal has endpoint terms = Rel(K_{n+1}) * q^{n+1}
    set R := (⊤ : SimpleGraph (Fin (n + 1))).reliabilityFun q
    set middle := ∑ s ∈ Finset.Ico 1 n, g s
    -- Simplify to |middle / q^{n+1}|
    have hsimp : (R * q ^ (n + 1) + middle + R * q ^ (n + 1)) / q ^ (n + 1) - 2 * R =
        middle / q ^ (n + 1) := by
      field_simp; ring
    rw [hsimp]
    -- Step 4: Distribute division and bound via triangle inequality
    have hsum_div : middle / q ^ (n + 1) = ∑ s ∈ Finset.Ico 1 n, (g s / q ^ (n + 1)) := by
      show (∑ s ∈ Finset.Ico 1 n, g s) / q ^ (n + 1) = _
      simp only [div_eq_mul_inv]; rw [Finset.sum_mul]
    rw [hsum_div]
    -- Step 5: Each |g(s)/q^{n+1}| ≤ M² · C(n,s) · |q|^{s(n-s)}
    calc |∑ s ∈ Finset.Ico 1 n, (g s / q ^ (n + 1))|
        ≤ ∑ s ∈ Finset.Ico 1 n, |g s / q ^ (n + 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ Finset.Ico 1 n, M ^ 2 * ((n.choose s : ℝ) * |q| ^ (s * (n - s))) := by
          apply Finset.sum_le_sum; intro s hs
          simp only [Finset.mem_Ico] at hs
          -- |g(s) / q^{n+1}| = |g(s)| / |q|^{n+1}
          rw [abs_div, abs_pow]
          -- Expand |g(s)|
          show |↑(n.choose s) * (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
            (⊤ : SimpleGraph (Fin (n + 2 - (s + 1)))).reliabilityFun q *
            q ^ ((s + 1) * (n + 2 - (s + 1)))| / |q| ^ (n + 1) ≤ _
          rw [abs_mul, abs_mul, abs_mul, abs_pow,
            abs_of_nonneg (Nat.cast_nonneg (n.choose s))]
          have hM1 : |((⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q)| ≤ M := hM (s + 1)
          have hM2 : |((⊤ : SimpleGraph (Fin (n + 2 - (s + 1)))).reliabilityFun q)| ≤ M :=
            hM (n + 2 - (s + 1))
          -- Exponent identity: (s+1)*(n+2-(s+1)) = (n+1) + s*(n-s)
          have hexp : (s + 1) * (n + 2 - (s + 1)) = (n + 1) + s * (n - s) := by
            have : s + 1 ≤ n + 2 := by omega
            have : s ≤ n := by omega
            zify [*]; ring
          rw [hexp, pow_add]
          -- Cancel |q|^{n+1}
          rw [show ↑(n.choose s) * |(⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q| *
              |(⊤ : SimpleGraph (Fin (n + 2 - (s + 1)))).reliabilityFun q| *
              (|q| ^ (n + 1) * |q| ^ (s * (n - s))) / |q| ^ (n + 1)
              = ↑(n.choose s) * |(⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q| *
              |(⊤ : SimpleGraph (Fin (n + 2 - (s + 1)))).reliabilityFun q| *
              |q| ^ (s * (n - s)) from by
            rw [show ↑(n.choose s) * |(⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q| *
                |(⊤ : SimpleGraph (Fin (n + 2 - (s + 1)))).reliabilityFun q| *
                (|q| ^ (n + 1) * |q| ^ (s * (n - s)))
                = (↑(n.choose s) * |(⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q| *
                |(⊤ : SimpleGraph (Fin (n + 2 - (s + 1)))).reliabilityFun q| *
                |q| ^ (s * (n - s))) * |q| ^ (n + 1) from by ring]
            rw [mul_div_cancel_right₀ _ (ne_of_gt (pow_pos (abs_pos.mpr hq0) _))]]
          calc ↑(n.choose s) * |(⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q| *
                |(⊤ : SimpleGraph (Fin (n + 2 - (s + 1)))).reliabilityFun q| *
                |q| ^ (s * (n - s))
              ≤ ↑(n.choose s) * M * M * |q| ^ (s * (n - s)) := by gcongr
            _ = M ^ 2 * (↑(n.choose s) * |q| ^ (s * (n - s))) := by ring
      _ = M ^ 2 * ∑ s ∈ Finset.Ico 1 n, ((n.choose s : ℝ) * |q| ^ (s * (n - s))) := by
          rw [← Finset.mul_sum]
      _ = M ^ 2 * seqB |q| (n + 2) := by
          congr 1
          simp only [seqB, show n + 2 - 1 = n + 1 from by omega,
            show n + 2 - 2 = n from by omega]
          apply Finset.sum_nbij' (· + 1) (· - 1)
          · intro s hs; simp only [Finset.mem_Ico] at hs ⊢; omega
          · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
          · intro s hs; omega
          · intro j hj; simp only [Finset.mem_Ico] at hj; omega
          · intro s hs
            simp only [Finset.mem_Ico] at hs
            have hs1 : s + 1 ≤ n + 2 := by omega
            have hs2 : s ≤ n := by omega
            have hexp_eq : (s + 1) * (n + 2 - (s + 1)) - (n + 1) = s * (n - s) := by
              have hge : n + 1 ≤ (s + 1) * (n + 2 - (s + 1)) := by
                have : (s + 1) * (n + 2 - (s + 1)) = (n + 1) + s * (n - s) := by
                  zify [hs1, hs2]; ring
                omega
              zify [hs1, hs2, hge, show 1 ≤ s + 1 from by omega]; ring
            simp only [show s + 1 - 1 = s from by omega, hexp_eq]
  -- M² · seqB < ε/2
  have h2 : M ^ 2 * seqB |q| (n + 2) < ε / 2 := by
    calc M ^ 2 * seqB |q| (n + 2)
        < M ^ 2 * (ε / (2 * M ^ 2 + 2)) :=
          mul_lt_mul_of_pos_left hseqB_bound (by positivity)
      _ ≤ ε / 2 := by
          have : (0:ℝ) < 2 * M ^ 2 + 2 := by positivity
          calc M ^ 2 * (ε / (2 * M ^ 2 + 2))
              ≤ (2 * M ^ 2 + 2) / 2 * (ε / (2 * M ^ 2 + 2)) := by
                gcongr; nlinarith [sq_nonneg M]
            _ = ε / 2 := by field_simp
  -- Triangle inequality
  set T := (∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) *
    (⊤ : SimpleGraph (Fin (s + 1))).reliabilityFun q *
    (⊤ : SimpleGraph (Fin (n + 2 - (s + 1)))).reliabilityFun q *
    q ^ ((s + 1) * (n + 2 - (s + 1)))) / q ^ (n + 1)
  set Rn := (⊤ : SimpleGraph (Fin (n + 1))).reliabilityFun q
  calc |T - 2|
      = |(T - 2 * Rn) + 2 * (Rn - 1)| := by ring_nf
    _ ≤ |T - 2 * Rn| + |2 * (Rn - 1)| := abs_add_le _ _
    _ = |T - 2 * Rn| + 2 * |Rn - 1| := by
        congr 1; rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2)]
    _ ≤ M ^ 2 * seqB |q| (n + 2) + 2 * |Rn - 1| := by linarith [htail]
    _ < ε / 2 + ε / 2 := by linarith [hRn1]
    _ = ε := by ring

end
