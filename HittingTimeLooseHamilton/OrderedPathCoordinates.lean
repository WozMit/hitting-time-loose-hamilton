module

public import HittingTimeLooseHamilton.OrderPrefixDecomposition

public section
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]

@[expose] def outsideExtensionPath (K : Finset A) (τ : FiniteOrder (OutsideVertex K))
    (j : ℕ) : Finset A := K ∪ (orderPrefix τ (j-K.card)).image Subtype.val

/-- Every time of the suffix path, including saturation and clamping, is
independent of the internal ordering of the prescribed prefix. -/
theorem concatenateOrder_path (K : Finset A) (ρ : FiniteOrder ↥K)
    (τ : FiniteOrder (OutsideVertex K)) (j : ℕ) :
    orderPrefix (concatenateOrder K ρ τ) (max K.card j) = outsideExtensionPath K τ j := by
  ext x
  simp only [mem_orderPrefix,outsideExtensionPath,mem_union,mem_image]
  by_cases hx : x ∈ K
  · have ht : (ρ ⟨x,hx⟩).val < K.card := by simpa only [Fintype.card_coe] using (ρ ⟨x,hx⟩).isLt
    rw [concatenateOrder_inside K ρ τ ⟨x,hx⟩]
    exact iff_of_true (ht.trans_le (le_max_left _ _)) (Or.inl hx)
  · rw [concatenateOrder_outside K ρ τ ⟨x,hx⟩]
    simp only [hx,false_or]
    constructor
    · intro h
      exact ⟨⟨x,hx⟩,by omega,rfl⟩
    · rintro ⟨y,hy,hyx⟩
      have he : y = ⟨x,hx⟩ := Subtype.ext hyx
      subst y
      omega

lemma prefixOrder_path (K : Finset A) (σ : PrefixOrderFiber K) :
    (fun j => orderPrefix σ.val (max K.card j)) =
      outsideExtensionPath K (prefixOutsideOrder K σ) := by
  have he := congrArg Subtype.val ((prefixOrderEquiv K).left_inv σ)
  change concatenateOrder K (prefixInternalOrder K σ) (prefixOutsideOrder K σ) = σ.val at he
  funext j
  rw [← he,concatenateOrder_path]
end LooseHamilton
