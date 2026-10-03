module

public import HittingTimeLooseHamilton.OrderedPathCoordinates
public import HittingTimeLooseHamilton.UniformSubtypeProbability

public section
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
local instance {B : Type*} [Fintype B] : Nonempty (FiniteOrder B) := ⟨Fintype.equivFin B⟩
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Full suffix-path law given the initial set. The internal prefix order
is averaged out exactly, rather than just comparing one-time marginals. -/
theorem ordered_path_kernel (K : Finset A) (P : (ℕ → Finset A) → Prop) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder A)).event (fun σ =>
      orderPrefix σ K.card = K ∧ P (fun j => orderPrefix σ (max K.card j))) =
    (1 / ((Fintype.card A).choose K.card : ℝ)) *
      (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder (OutsideVertex K))).event
        (fun τ => P (outsideExtensionPath K τ)) := by
  classical
  letI : Nonempty (FiniteOrder A) := ⟨Fintype.equivFin A⟩
  letI : Nonempty (FiniteOrder ↥K) := ⟨Fintype.equivFin ↥K⟩
  letI : Nonempty (FiniteOrder (OutsideVertex K)) := ⟨Fintype.equivFin _⟩
  letI : Nonempty (PrefixOrderFiber K) := ⟨(prefixOrderEquiv K).symm
    (Fintype.equivFin ↥K,Fintype.equivFin (OutsideVertex K))⟩
  rw [uniform_event_and_eq_mul_subtype]
  have hp : (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder A)).event
      (fun σ => orderPrefix σ K.card = K) = 1 / ((Fintype.card A).choose K.card : ℝ) := by
    rw [FiniteEntropy.Law.uniform_event]
    exact uniform_order_prefix_probability K.card (card_le_univ K) K rfl
  rw [hp]
  congr 1
  have he : (fun σ : PrefixOrderFiber K => P (fun j => orderPrefix σ.val (max K.card j))) =
      (fun σ => P (outsideExtensionPath K ((prefixOrderEquiv K) σ).2)) := by
    funext σ
    rw [prefixOrder_path]
    rfl
  rw [he,FiniteEntropy.Law.uniform_event_equiv (prefixOrderEquiv K) (fun p => P (outsideExtensionPath K p.2))]
  rw [uniform_product_eq,FiniteEntropy.Law.event_prod_sum]
  simp only [← Finset.sum_mul,FiniteEntropy.uniform.total,one_mul]
end LooseHamilton
