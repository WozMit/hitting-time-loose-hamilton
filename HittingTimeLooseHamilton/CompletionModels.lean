module

public import HittingTimeLooseHamilton.CycleOnCounting

public section

/-! # Private-block completions

`completionCount` is the manuscript's unrestricted count `W_G(P;yz)`.
Deleting `P` changes the active vertices to `univ \ P`. The equivalence with
`X(G-P, M ∪ {yz})` on the actual vertex subtype is `completionCount_eq_X`.
No assumption that `P ∪ yz` belongs to the host is part of this definition.
-/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A private block and fresh pair disjoint from each other and the old ports. -/
structure LegalPrivateCompletion (r : ℕ) (markers : Finset (Finset V))
    (P pair : Finset V) : Prop where
  private_card : P.card = r - 2
  pair_card : pair.card = 2
  private_pair_disjoint : Disjoint P pair
  ports_disjoint : Disjoint (P ∪ pair) (originalPorts markers)

namespace LegalPrivateCompletion
variable {r : ℕ} {markers : Finset (Finset V)} {P pair : Finset V}

theorem pair_subset_active (h : LegalPrivateCompletion r markers P pair) :
    pair ⊆ univ \ P := by
  intro x hx
  exact mem_sdiff.mpr ⟨mem_univ _, fun hp => disjoint_left.mp h.private_pair_disjoint hp hx⟩

theorem marker_subset_active (h : LegalPrivateCompletion r markers P pair)
    {m : Finset V} (hm : m ∈ markers) : m ⊆ univ \ P := by
  intro x hx
  refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
  intro hp
  exact disjoint_left.mp h.ports_disjoint (mem_union_left _ hp)
    (mem_biUnion.mpr ⟨m, hm, hx⟩)

theorem augmented_subset_active (h : LegalPrivateCompletion r markers P pair) :
    ∀ m ∈ insert pair markers, m ⊆ univ \ P := by
  intro m hm
  rcases mem_insert.mp hm with rfl | hm
  · exact h.pair_subset_active
  · exact h.marker_subset_active hm

end LegalPrivateCompletion

/-- The actual ordinary edge sets completing the fresh marked pair after deleting `P`. -/
@[expose] def completionFamily (r : ℕ) (markers host : Finset (Finset V)) (P pair : Finset V) :
    Finset (Finset (Finset V)) :=
  cycleOnFamily r (univ \ P) (insert pair markers) host

/-- The manuscript's `W_G(P;yz)`, counted as unoriented ordinary edge sets. -/
@[expose] def completionCount (r : ℕ) (markers host : Finset (Finset V)) (P pair : Finset V) : ℕ :=
  cycleOnCount r (univ \ P) (insert pair markers) host

@[simp] theorem mem_completionFamily (r : ℕ) (markers host : Finset (Finset V))
    (P pair : Finset V) (E : Finset (Finset V)) :
    E ∈ completionFamily r markers host P pair ↔
      IsMixedCycleOn r (univ \ P) (insert pair markers) E ∧ E ⊆ host := by
  exact mem_cycleOnFamily _ _ _ _ _

/-- `W` is exactly `X` on the induced host after deleting the private vertices. -/
theorem completionCount_eq_X {r : ℕ} {markers host : Finset (Finset V)}
    {P pair : Finset V} (hr : 3 ≤ r) (h : LegalPrivateCompletion r markers P pair) :
    completionCount r markers host P pair =
      unrestrictedCycleCount r (restrictEdges (univ \ P) (insert pair markers))
        (inducedHost (univ \ P) host) := by
  exact cycleOnCount_eq_unrestricted hr (univ \ P) (insert pair markers) host
    h.augmented_subset_active


/-- The completion count depends only on the induced host outside the private block. -/
theorem completionCount_congr_inducedHost (r : ℕ) (markers : Finset (Finset V))
    (P pair : Finset V) (G H : Finset (Finset V))
    (hGH : inducedHost (univ \ P) G = inducedHost (univ \ P) H) :
    completionCount r markers G P pair = completionCount r markers H P pair := by
  exact congrArg Finset.card
    (cycleOnFamily_congr_inducedHost r (univ \ P) (insert pair markers) G H hGH)

end LooseHamilton
