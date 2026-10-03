module

public import HittingTimeLooseHamilton.EndpointCoreCounts

public section

/-! # Finite disjoint-sum bookkeeping for the exact cut partition -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A cut remembers its type, every labelled vertex/private block, and the
actual ordinary edge set of its core. Witness presentations are not counted. -/
abbrev EndpointCutDomain (r : ℕ) (M G : Finset (Finset V)) (P : Finset V) (y z : V) :=
  (Σ l : ↥(endpointCutLabelsI r M G P y z),
      ↥(endpointCutCoreFamilyI r M G P y z l.val)) ⊕
  (Σ l : ↥(endpointCutLabelsII r M G P y z),
      ↥(endpointCutCoreFamilyII r M G P y z l.val))

theorem endpointCutDomain_card (r : ℕ) (M G : Finset (Finset V)) (P : Finset V) (y z : V) :
    Fintype.card (EndpointCutDomain r M G P y z) =
      (∑ l ∈ endpointCutLabelsI r M G P y z,
        (endpointCutCoreFamilyI r M G P y z l).card) +
      ∑ l ∈ endpointCutLabelsII r M G P y z,
        (endpointCutCoreFamilyII r M G P y z l).card := by
  classical
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma]
  simp only [Fintype.card_coe]
  congr 1
  · exact Finset.sum_coe_sort _ (fun l => (endpointCutCoreFamilyI r M G P y z l).card)
  · exact Finset.sum_coe_sort _ (fun l => (endpointCutCoreFamilyII r M G P y z l).card)

/-- Counting an established bijection counts neither cyclic orientations nor
presentations. The geometric bijection is supplied by the cut surgery. -/
theorem endpointCut_partition_of_bijective {r : ℕ} {M G : Finset (Finset V)}
    {P : Finset V} {y z : V}
    (expand : EndpointCutDomain r M G P y z → ↥(completionFamily r M G P {y,z}))
    (hbij : Function.Bijective expand) :
    completionCount r M G P {y,z} =
      (∑ l ∈ endpointCutLabelsI r M G P y z,
        (endpointCutCoreFamilyI r M G P y z l).card) +
      ∑ l ∈ endpointCutLabelsII r M G P y z,
        (endpointCutCoreFamilyII r M G P y z l).card := by
  have hc := Fintype.card_congr (Equiv.ofBijective expand hbij)
  rw [endpointCutDomain_card, Fintype.card_coe] at hc
  exact hc.symm

end LooseHamilton
