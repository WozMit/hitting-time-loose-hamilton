module

public import HittingTimeLooseHamilton.EndpointSpliceImages

public section

/-! # Counting the full disjoint sum over cuts, private blocks and endpoints -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev EndpointSpliceDomainI (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) :=
  Σ l : ↥(endpointCutLabelsI r M G P y z),
    Σ b : ↥(endpointSpliceLabelsI r M G P y z t l.val),
      ↥(endpointSpliceInputFamilyI r M G P y z t l.val b.val)
abbrev EndpointSpliceDomainII (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) :=
  Σ l : ↥(endpointCutLabelsII r M G P y z),
    Σ b : ↥(endpointSpliceLabelsII r M G P y z t l.val),
      ↥(endpointSpliceInputFamilyII r M G P y z t l.val b.val)
abbrev EndpointSpliceDomain (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) :=
  EndpointSpliceDomainI r M G P y z t ⊕ EndpointSpliceDomainII r M G P y z t

theorem endpointSpliceDomain_card (r : ℕ) (M G : Finset (Finset V)) (P : Finset V)
    (y z t : V) :
    Fintype.card (EndpointSpliceDomain r M G P y z t) =
      (∑ l ∈ endpointCutLabelsI r M G P y z,
        ∑ b ∈ endpointSpliceLabelsI r M G P y z t l,
          (endpointSpliceInputFamilyI r M G P y z t l b).card) +
      ∑ l ∈ endpointCutLabelsII r M G P y z,
        ∑ b ∈ endpointSpliceLabelsII r M G P y z t l,
          (endpointSpliceInputFamilyII r M G P y z t l b).card := by
  classical
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma]
  congr 1
  · trans ∑ l : ↥(endpointCutLabelsI r M G P y z),
      ∑ b ∈ endpointSpliceLabelsI r M G P y z t l.val,
        (endpointSpliceInputFamilyI r M G P y z t l.val b).card
    · apply sum_congr rfl
      intro l _
      rw [Fintype.card_sigma]
      simp only [Fintype.card_coe]
      exact sum_coe_sort _ (fun b => (endpointSpliceInputFamilyI r M G P y z t l.val b).card)
    · exact sum_coe_sort _ (fun l => ∑ b ∈ endpointSpliceLabelsI r M G P y z t l,
        (endpointSpliceInputFamilyI r M G P y z t l b).card)
  · trans ∑ l : ↥(endpointCutLabelsII r M G P y z),
      ∑ b ∈ endpointSpliceLabelsII r M G P y z t l.val,
        (endpointSpliceInputFamilyII r M G P y z t l.val b).card
    · apply sum_congr rfl
      intro l _
      rw [Fintype.card_sigma]
      simp only [Fintype.card_coe]
      exact sum_coe_sort _ (fun b => (endpointSpliceInputFamilyII r M G P y z t l.val b).card)
    · exact sum_coe_sort _ (fun l => ∑ b ∈ endpointSpliceLabelsII r M G P y z t l,
        (endpointSpliceInputFamilyII r M G P y z t l b).card)

/-- The local constructions will discharge these image properties. -/
structure EndpointSpliceImageProperties (r : ℕ) (M G : Finset (Finset V))
    (P : Finset V) (y z t : V) : Prop where
  typeI : ∀ l, EndpointCutLegalI r M G P y z l → ∀ b,
    EndpointSpliceLegalI r M G P y z t l b → ∀ F,
    F ∈ endpointSpliceInputFamilyI r M G P y z t l b →
    Nonempty (EndpointSpliceImageI r M G P y z t l b F)
  typeII : ∀ l, EndpointCutLegalII r M G P y z l → ∀ b,
    EndpointSpliceLegalII r M G P y z t l b → ∀ F,
    F ∈ endpointSpliceInputFamilyII r M G P y z t l b →
    Nonempty (EndpointSpliceImageII r M G P y z t l b F)

variable {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z t : V}

@[expose] def endpointSpliceImageOfI (h : EndpointSpliceImageProperties r M G P y z t)
    (a : EndpointSpliceDomainI r M G P y z t) :
    EndpointSpliceImageI r M G P y z t a.1.val a.2.1.val a.2.2.val :=
  Classical.choice (h.typeI _ ((mem_endpointCutLabelsI _ _ _ _ _ _ _).mp a.1.property)
    _ ((mem_endpointSpliceLabelsI _ _ _ _ _ _ _ _ _).mp a.2.1.property) _ a.2.2.property)
@[expose] def endpointSpliceImageOfII (h : EndpointSpliceImageProperties r M G P y z t)
    (a : EndpointSpliceDomainII r M G P y z t) :
    EndpointSpliceImageII r M G P y z t a.1.val a.2.1.val a.2.2.val :=
  Classical.choice (h.typeII _ ((mem_endpointCutLabelsII _ _ _ _ _ _ _).mp a.1.property)
    _ ((mem_endpointSpliceLabelsII _ _ _ _ _ _ _ _ _).mp a.2.1.property) _ a.2.2.property)

@[expose] def endpointSpliceMap (h : EndpointSpliceImageProperties r M G P y z t) :
    EndpointSpliceDomain r M G P y z t → ↥(completionFamily r M G P {t,z})
  | .inl a => ⟨endpointSpliceOutputI y a.1.val a.2.1.val a.2.2.val,
      (mem_completionFamily _ _ _ _ _ _).mpr
        ⟨⟨(endpointSpliceImageOfI h a).cycle⟩,(endpointSpliceImageOfI h a).host_subset⟩⟩
  | .inr a => ⟨endpointSpliceOutputII y a.1.val a.2.1.val a.2.2.val,
      (mem_completionFamily _ _ _ _ _ _).mpr
        ⟨⟨(endpointSpliceImageOfII h a).cycle⟩,(endpointSpliceImageOfII h a).host_subset⟩⟩

end LooseHamilton
