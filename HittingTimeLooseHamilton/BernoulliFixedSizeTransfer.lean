module

public import HittingTimeLooseHamilton.BernoulliSubsetLaw
public import HittingTimeLooseHamilton.UniformPrefixProbability
public import HittingTimeLooseHamilton.NatLawAtoms

public section

/-! Transfer of increasing events from independent subsets to uniform fixed size. -/
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace LooseHamilton.BernoulliSubset
variable {A : Type*} [Fintype A] [DecidableEq A]

@[expose] instance orderNonempty : Nonempty (FiniteOrder A) := ⟨Fintype.equivFin A⟩

@[expose] def prefixProbability (m : ℕ) (P : Finset A → Prop) : ℝ :=
  (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder A)).event
    (fun σ => P (orderPrefix σ m))

lemma prefixProbability_mono (P : Finset A → Prop) (hP : Monotone P)
    {m M : ℕ} (hm : m ≤ M) : prefixProbability m P ≤ prefixProbability M P := by
  apply FiniteEntropy.Law.event_mono
  intro σ hσ
  apply hP _ hσ
  intro a ha
  simp only [mem_orderPrefix] at ha ⊢
  omega

lemma prefixProbability_eq (m : ℕ) (hm : m ≤ Fintype.card A) (P : Finset A → Prop) :
    prefixProbability m P =
      (((univ : Finset A).powersetCard m).filter P).card /
        ((Fintype.card A).choose m : ℝ) := by
  classical
  let T := (univ : Finset A).powersetCard m
  let E : ↥T → FiniteOrder A → Prop := fun S σ => P S.val ∧ orderPrefix σ m = S.val
  let ρ : FiniteEntropy.Law (FiniteOrder A) := FiniteEntropy.uniform
  have hev : (fun σ => P (orderPrefix σ m)) = (fun σ => ∃ S, E S σ) := by
    funext σ
    apply propext
    constructor
    · intro hp
      exact ⟨⟨orderPrefix σ m,mem_powersetCard.mpr
        ⟨subset_univ _,orderPrefix_card σ m hm⟩⟩,hp,rfl⟩
    · rintro ⟨S,hp,hS⟩; simpa only [hS] using hp
  change ρ.event _ = _
  rw [hev,event_exists_eq_sum ρ E (by
    intro σ S T hS hT; exact Subtype.ext (hS.2.symm.trans hT.2))]
  have hevent (S : ↥T) : ρ.event (E S) =
      if P S.val then 1 / ((Fintype.card A).choose m : ℝ) else 0 := by
    change ρ.event (fun σ => P S.val ∧ orderPrefix σ m = S.val) = _
    rw [FiniteEntropy.Law.event_const_and]
    split_ifs with hp
    · rw [FiniteEntropy.Law.uniform_event]
      exact uniform_order_prefix_probability m hm S.val (mem_powersetCard.mp S.property).2
    · rfl
  simp_rw [hevent]
  rw [show (∑ S : ↥T, if P S.val then 1 / ((Fintype.card A).choose m : ℝ) else 0) =
      ∑ S ∈ T, if P S then 1 / ((Fintype.card A).choose m : ℝ) else 0 from
      sum_coe_sort T (fun S => if P S then 1 / ((Fintype.card A).choose m : ℝ) else 0)]
  rw [← sum_filter]
  simp [T,mul_one_div,div_eq_mul_inv]

lemma slice_probability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (m : ℕ) (P : Finset A → Prop) :
    (law (A := A) p hp0 hp1).event (fun S => S.card = m ∧ P S) =
      p^m * (1-p)^(Fintype.card A-m) *
        (((univ : Finset A).powersetCard m).filter P).card := by
  classical
  have hsum : (law (A := A) p hp0 hp1).event (fun S => S.card = m ∧ P S) =
      ∑ S ∈ ((univ : Finset A).powersetCard m).filter P,
        p^m*(1-p)^(Fintype.card A-m) := by
    unfold FiniteEntropy.Law.event
    rw [sum_filter]
    have hs : ((univ : Finset A).powersetCard m) =
        (univ : Finset (Finset A)).filter (fun S => S.card=m) := by
      ext S; simp
    rw [hs,sum_filter]
    apply sum_congr rfl
    intro S hS
    by_cases hc : S.card=m <;> by_cases hP : P S <;>
      simp [hc,hP,law,weight_const]
  rw [hsum,sum_const,nsmul_eq_mul]
  ring

lemma slice_factorization (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (m : ℕ) (hm : m ≤ Fintype.card A) (P : Finset A → Prop) :
    (law (A := A) p hp0 hp1).event (fun S => S.card = m ∧ P S) =
      natLawAtom (law (A := A) p hp0 hp1) Finset.card m * prefixProbability m P := by
  classical
  have ha := slice_probability p hp0 hp1 m (fun _ : Finset A => True)
  simp [card_powersetCard] at ha
  rw [natLawAtom,ha,prefixProbability_eq m hm,slice_probability]
  have hc : ((Fintype.card A).choose m : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast Nat.choose_pos hm)
  field_simp <;> ring

/-- The exact mixture identity, using the actual binomial subset-size atoms. -/
lemma event_mixture (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : Finset A → Prop) :
    (law (A := A) p hp0 hp1).event P = ∑ m ∈ range (Fintype.card A+1),
      natLawAtom (law (A := A) p hp0 hp1) Finset.card m * prefixProbability m P := by
  classical
  have hs : (law (A := A) p hp0 hp1).event P = ∑ m ∈ range (Fintype.card A+1),
      (law (A := A) p hp0 hp1).event (fun S => S.card=m ∧ P S) := by
    unfold FiniteEntropy.Law.event
    rw [sum_comm]
    apply sum_congr rfl
    intro S hS
    have hc : S.card < Fintype.card A+1 := by have := card_le_univ S; omega
    by_cases hP : P S <;> simp [hP,hc,eq_comm]
  rw [hs]
  apply sum_congr rfl
  intro m hm
  exact slice_factorization p hp0 hp1 m (by have := mem_range.mp hm; omega) P

/-- Monotonicity transfers the lower bound, losing only the overflow probability. -/
theorem fixed_size_transfer (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (M : ℕ) (P : Finset A → Prop) (hP : Monotone P) :
    (law (A := A) p hp0 hp1).event P - (law (A := A) p hp0 hp1).event (fun S => M < S.card) ≤
      prefixProbability M P := by
  classical
  let ρ := law (A := A) p hp0 hp1
  have hpoint (m : ℕ) : prefixProbability m P ≤
      prefixProbability M P + if M < m then 1 else 0 := by
    by_cases h : M < m
    · rw [if_pos h]
      exact (FiniteEntropy.Law.event_le_one _ _).trans
        (by have := (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder A)).event_nonneg
              (fun σ => P (orderPrefix σ M))
            change 0 ≤ prefixProbability M P at this
            linarith)
    · simpa [h] using prefixProbability_mono P hP (Nat.le_of_not_gt h)
  have hsum := sum_le_sum (s := range (Fintype.card A+1)) (fun m hm =>
    mul_le_mul_of_nonneg_left (hpoint m) (natLawAtom_nonneg ρ Finset.card m))
  have htotal := sum_natLawAtom_total ρ Finset.card (Fintype.card A) card_le_univ
  have hover : (∑ m ∈ range (Fintype.card A+1),
      natLawAtom ρ Finset.card m * (if M<m then (1:ℝ) else 0)) =
        ρ.event (fun S => M < S.card) := by
    unfold natLawAtom FiniteEntropy.Law.event
    simp_rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro S hS
    have hc : S.card < Fintype.card A+1 := by have := card_le_univ S; omega
    rw [sum_eq_single S.card]
    · by_cases hh : M < S.card <;> simp [hh]
    · intro m hm hne
      simp [Ne.symm hne]
    · simp [hc]
  simp_rw [mul_add] at hsum
  rw [sum_add_distrib,← sum_mul,htotal,one_mul,hover] at hsum
  have he := event_mixture p hp0 hp1 P
  change ρ.event P = _ at he
  rw [← he] at hsum
  linarith
end LooseHamilton.BernoulliSubset
