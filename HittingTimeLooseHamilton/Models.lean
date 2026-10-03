module

public import HittingTimeLooseHamilton.KahnLaw
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Fin

public section

/-! Finite probability models from Section 1 of the supplied manuscript.
The terminal state is uniform; an independent uniform permutation orders its
missing edges using fixed finite coordinates. Every missing-edge order has equal mass.
In particular, intermediate extension states are not defined by reconditioning.
-/
noncomputable section
open scoped BigOperators
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev SimpleHypergraph (V : Type*) := Finset (Finset V)

@[expose] def completeEdges (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :
    SimpleHypergraph V := Finset.univ.filter (fun e => e.card = r)

@[simp] theorem mem_completeEdges (r : ℕ) (e : Finset V) :
    e ∈ completeEdges V r ↔ e.card = r := by simp [completeEdges]

@[expose] def vertexDegree (G : SimpleHypergraph V) (v : V) : ℕ :=
  (G.filter fun e => v ∈ e).card

@[expose] def pairDegree (G : SimpleHypergraph V) (u v : V) : ℕ :=
  (G.filter fun e => u ∈ e ∧ v ∈ e).card

@[expose] def originalPorts (markers : Finset (Finset V)) : Finset V := markers.biUnion id

/-- The port set is an explicit fixed parameter, independent of changing markers. -/
@[expose] def allowedEdges (r : ℕ) (ports : Finset V) : SimpleHypergraph V :=
  (completeEdges V r).filter fun e => (e ∩ ports).card ≤ 1

@[simp] theorem mem_allowedEdges (r : ℕ) (ports e : Finset V) :
    e ∈ allowedEdges r ports ↔ e.card = r ∧ (e ∩ ports).card ≤ 1 := by
  simp [allowedEdges]

abbrev Edge (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :=
  ↥(completeEdges V r)

abbrev EdgeOrder (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :=
  Equiv.Perm (Edge V r)

/-- Rank zero is the first edge in the order. -/
@[expose] def edgeRank {r : ℕ} (σ : EdgeOrder V r) (e : Edge V r) : ℕ :=
  (Fintype.equivFin (Edge V r) (σ e)).val

/-- Uniform complete-edge order, the sample space of the ordinary process. -/
@[expose] def processLaw (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :
    FiniteEntropy.Law (EdgeOrder V r) := FiniteEntropy.uniform

@[expose] def processState {r : ℕ} (σ : EdgeOrder V r) (t : ℕ) : SimpleHypergraph V :=
  ((Finset.univ : Finset (Edge V r)).filter (fun e => edgeRank σ e < t)).image
    Subtype.val

@[simp] theorem processState_zero {r : ℕ} (σ : EdgeOrder V r) :
    processState σ 0 = ∅ := by simp [processState]

theorem processState_mono {r : ℕ} (σ : EdgeOrder V r) : Monotone (processState σ) := by
  intro s t h
  apply Finset.image_subset_image
  intro e he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact lt_of_lt_of_le he h

theorem processState_subset {r : ℕ} (σ : EdgeOrder V r) (t : ℕ) :
    processState σ t ⊆ completeEdges V r := by
  intro e he
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
  exact a.property

@[simp] theorem processState_terminal {r : ℕ} (σ : EdgeOrder V r) :
    processState σ (completeEdges V r).card = completeEdges V r := by
  apply Finset.Subset.antisymm (processState_subset σ _)
  intro e he
  apply Finset.mem_image.mpr
  refine ⟨⟨e, he⟩, ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simpa [edgeRank] using (Fintype.equivFin (Edge V r) (σ ⟨e, he⟩)).isLt

/-- Fixed-size degree-conditioned terminal family Omega(M,ell). -/
@[expose] def TerminalState (V : Type*) [Fintype V] [DecidableEq V]
    (r M : ℕ) (ell : V → ℕ) :=
  {F : SimpleHypergraph V // F ⊆ completeEdges V r ∧ F.card = M ∧
    ∀ v, ell v ≤ vertexDegree F v}

@[expose] instance {r M : ℕ} {ell : V → ℕ} : Fintype (TerminalState V r M ell) := by
  classical
  unfold TerminalState
  infer_instance

/-- This law is defined precisely when the terminal family is nonempty. -/
@[expose] def terminalLaw (r M : ℕ) (ell : V → ℕ) [Nonempty (TerminalState V r M ell)] :
    FiniteEntropy.Law (TerminalState V r M ell) := FiniteEntropy.uniform

theorem edgeRank_injective {r : ℕ} (σ : EdgeOrder V r) :
    Function.Injective (edgeRank σ) := by
  intro a b hab
  exact σ.injective ((Fintype.equivFin (Edge V r)).injective (Fin.ext hab))

theorem processState_card {r : ℕ} (σ : EdgeOrder V r) (t : ℕ) :
    (processState σ t).card = min t (completeEdges V r).card := by
  rw [processState, Finset.card_image_iff.mpr (fun a _ b _ h => Subtype.ext h)]
  have hc : Fintype.card (Edge V r) = (completeEdges V r).card := Fintype.card_coe _
  calc
    _ = (Finset.range (min t (completeEdges V r).card)).card := by
      apply Finset.card_bij (fun a _ => edgeRank σ a)
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        simp only [Finset.mem_range, lt_min_iff]
        exact ⟨ha, by simpa [edgeRank, hc] using
          (Fintype.equivFin (Edge V r) (σ a)).isLt⟩
      · intro a _ b _ h
        exact edgeRank_injective σ h
      · intro b hb
        have hb' : b < Fintype.card (Edge V r) := by
          simpa [hc] using (lt_min_iff.mp (Finset.mem_range.mp hb)).2
        refine ⟨σ.symm ((Fintype.equivFin (Edge V r)).symm ⟨b, hb'⟩), ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa only [edgeRank, Equiv.apply_symm_apply, Fin.val_mk] using
            (lt_min_iff.mp (Finset.mem_range.mp hb)).1
        · simp [edgeRank]
    _ = _ := Finset.card_range _

theorem terminal_size_le {r M : ℕ} {ell : V → ℕ}
    (F : TerminalState V r M ell) : M ≤ (completeEdges V r).card := by
  rw [← F.property.2.1]
  exact Finset.card_le_card F.property.1

/-- Missing edges, including edges prohibited only for the counted cycle family. -/
abbrev MissingEdge {r M : ℕ} {ell : V → ℕ} (F : TerminalState V r M ell) :=
  ↥(completeEdges V r \ F.val)

theorem missing_card {r M : ℕ} {ell : V → ℕ}
    (F : TerminalState V r M ell) :
    Fintype.card (MissingEdge F) = (completeEdges V r).card - M := by
  rw [Fintype.card_coe, Finset.card_sdiff_of_subset F.property.1, F.property.2.1]

/-- Deterministic coordinates for missing edges; the following uniform permutation
makes the distribution independent of this coordinate choice. -/
@[expose] def missingEquiv {r M : ℕ} {ell : V → ℕ} (F : TerminalState V r M ell) :
    MissingEdge F ≃ Fin ((completeEdges V r).card - M) :=
  Fintype.equivFinOfCardEq (missing_card F)

abbrev MissingOrder (V : Type*) [Fintype V] [DecidableEq V] (r M : ℕ) :=
  Equiv.Perm (Fin ((completeEdges V r).card - M))

/-- The exact joint law Q: independently sample the uniform terminal state and a
uniform permutation of its K-M missing-edge positions. -/
@[expose] def extensionLaw (r M : ℕ) (ell : V → ℕ) [Nonempty (TerminalState V r M ell)] :
    FiniteEntropy.Law (TerminalState V r M ell × MissingOrder V r M) :=
  (terminalLaw r M ell).prod FiniteEntropy.uniform

/-- The resulting missing-edge order is an equivalence, not an arbitrary sequence. -/
@[expose] def missingOrder {r M : ℕ} {ell : V → ℕ} (F : TerminalState V r M ell)
    (σ : MissingOrder V r M) : MissingEdge F ≃ Fin ((completeEdges V r).card - M) :=
  (missingEquiv F).trans σ

/-- Bijection onto all possible missing-edge orders: uniform sampling of σ
therefore assigns the same mass to every missing-edge order. -/
@[expose] def missingOrderEquiv {r M : ℕ} {ell : V → ℕ} (F : TerminalState V r M ell) :
    MissingOrder V r M ≃ (MissingEdge F ≃ Fin ((completeEdges V r).card - M)) where
  toFun := missingOrder F
  invFun e := (missingEquiv F).symm.trans e
  left_inv σ := by ext a; simp [missingOrder]
  right_inv e := by ext a; simp [missingOrder]

/-- At j=M, no missing edges have been inserted. Indices below M are clamped. -/
@[expose] def extensionState {r M : ℕ} {ell : V → ℕ}
    (F : TerminalState V r M ell) (σ : MissingOrder V r M) (j : ℕ) : SimpleHypergraph V :=
  F.val ∪ (((Finset.univ : Finset (MissingEdge F)).filter
    (fun e => (missingOrder F σ e).val < j - M)).image Subtype.val)

@[simp] theorem extensionState_initial {r M : ℕ} {ell : V → ℕ}
    (F : TerminalState V r M ell) (σ : MissingOrder V r M) :
    extensionState F σ M = F.val := by simp [extensionState]

theorem extensionState_mono {r M : ℕ} {ell : V → ℕ}
    (F : TerminalState V r M ell) (σ : MissingOrder V r M) :
    Monotone (extensionState F σ) := by
  intro i j hij
  apply Finset.union_subset_union (Finset.Subset.refl _)
  apply Finset.image_subset_image
  intro e he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact lt_of_lt_of_le he (Nat.sub_le_sub_right hij M)

theorem extensionState_subset {r M : ℕ} {ell : V → ℕ}
    (F : TerminalState V r M ell) (σ : MissingOrder V r M) (j : ℕ) :
    extensionState F σ j ⊆ completeEdges V r := by
  apply Finset.union_subset F.property.1
  intro e he
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
  exact (Finset.mem_sdiff.mp a.property).1

@[simp] theorem extensionState_terminal {r M : ℕ} {ell : V → ℕ}
    (F : TerminalState V r M ell) (σ : MissingOrder V r M) :
    extensionState F σ (completeEdges V r).card = completeEdges V r := by
  apply Finset.Subset.antisymm (extensionState_subset F σ _)
  intro e he
  by_cases hF : e ∈ F.val
  · exact Finset.mem_union_left _ hF
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨⟨e, Finset.mem_sdiff.mpr ⟨he, hF⟩⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (missingOrder F σ _).isLt

theorem extensionState_card {r M : ℕ} {ell : V → ℕ}
    (F : TerminalState V r M ell) (σ : MissingOrder V r M) (j : ℕ)
    (hMj : M ≤ j) (hjK : j ≤ (completeEdges V r).card) :
    (extensionState F σ j).card = j := by
  let A := (Finset.univ : Finset (MissingEdge F)).filter
    (fun e => (missingOrder F σ e).val < j - M)
  have hdis : Disjoint F.val (A.image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro e he hA
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hA
    exact (Finset.mem_sdiff.mp a.property).2 he
  have hcard : A.card = j - M := by
    calc
      A.card = (Finset.range (j - M)).card := by
        apply Finset.card_bij (fun e _ => (missingOrder F σ e).val)
        · intro e he
          exact Finset.mem_range.mpr (Finset.mem_filter.mp he).2
        · intro a _ b _ hab
          exact (missingOrder F σ).injective (Fin.ext hab)
        · intro b hb
          have hb' : b < (completeEdges V r).card - M :=
            lt_of_lt_of_le (Finset.mem_range.mp hb) (Nat.sub_le_sub_right hjK M)
          refine ⟨(missingOrder F σ).symm ⟨b, hb'⟩, ?_, ?_⟩
          · simpa [A] using Finset.mem_range.mp hb
          · simp
      _ = j - M := Finset.card_range _
  change (F.val ∪ A.image Subtype.val).card = j
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_image_iff.mpr (fun a _ b _ h => Subtype.ext h),
    F.property.2.1, hcard, Nat.add_sub_of_le hMj]

/-- Exactly the uniform missing-edge-order law, via the displayed bijection. -/
theorem missingOrder_mass {r M : ℕ} {ell : V → ℕ}
    (F : TerminalState V r M ell)
    (e : MissingEdge F ≃ Fin ((completeEdges V r).card - M)) :
    ((FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).map
      (missingOrder F)).mass e = 1 / Fintype.card (MissingOrder V r M) := by
  classical
  have h : ∀ σ : MissingOrder V r M,
      missingOrder F σ = e ↔ σ = (missingOrderEquiv F).symm e := by
    intro σ
    exact (missingOrderEquiv F).apply_eq_iff_eq_symm_apply
  simp [FiniteEntropy.Law.map, FiniteEntropy.Law.event, h, FiniteEntropy.uniform]

@[simp] theorem extensionLaw_terminal_mass (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (F : TerminalState V r M ell) :
    (extensionLaw r M ell).fst.mass F = (terminalLaw r M ell).mass F := by
  change (∑ σ : MissingOrder V r M,
    (terminalLaw r M ell).mass F * FiniteEntropy.uniform.mass σ) = _
  rw [← Finset.mul_sum, FiniteEntropy.uniform.total, mul_one]

@[simp] theorem terminalLaw_mass (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (F : TerminalState V r M ell) :
    (terminalLaw r M ell).mass F = 1 / Fintype.card (TerminalState V r M ell) := by simp [terminalLaw, FiniteEntropy.uniform, one_div]

theorem completeEdges_card (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :
    (completeEdges V r).card = (Fintype.card V).choose r := by
  have h : completeEdges V r = (Finset.univ : Finset V).powersetCard r := by
    ext e
    simp
  rw [h, Finset.card_powersetCard, Finset.card_univ]

@[simp] theorem extensionLaw_order_mass (r M : ℕ) (ell : V → ℕ)
    [Nonempty (TerminalState V r M ell)] (σ : MissingOrder V r M) :
    (extensionLaw r M ell).snd.mass σ =
      (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).mass σ := by
  change (∑ F : TerminalState V r M ell,
    (terminalLaw r M ell).mass F * FiniteEntropy.uniform.mass σ) = _
  rw [← Finset.sum_mul, (terminalLaw r M ell).total, one_mul]

end LooseHamilton
