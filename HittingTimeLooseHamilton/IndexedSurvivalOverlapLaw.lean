module

public import HittingTimeLooseHamilton.IndexedSurvivalVariance
public import HittingTimeLooseHamilton.OverlapMoments

public section

/-! The overlap parameter is the actual expectation for two independent
uniform labels, including repeated supports and the diagonal. -/
noncomputable section
namespace LooseHamilton.IndexedSurvival
open Finset FiniteEntropy

/-- No quotient by equal supports is taken when computing expected overlap. -/
theorem uniformOverlap_eq_independent {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (F : Finset ι) (support : ι → Finset α) (hF : F.Nonempty) :
    letI : Nonempty ↥F := ⟨⟨hF.choose,hF.choose_spec⟩⟩
    uniformOverlap F support =
      (uniform : Law ↥F).independentOverlap (fun i => support i.val) := by
  classical
  letI : Nonempty ↥F := ⟨⟨hF.choose,hF.choose_spec⟩⟩
  unfold uniformOverlap Law.independentOverlap
  simp only [uniform, Fintype.card_coe]
  change _ = ∑ i : ↥F, ∑ j : ↥F,
    (F.card:ℝ)⁻¹*(F.card:ℝ)⁻¹*((support i.val ∩ support j.val).card:ℝ)
  rw [sum_coe_sort F (fun i => ∑ j : ↥F,
    (F.card:ℝ)⁻¹*(F.card:ℝ)⁻¹*((support i ∩ support j.val).card:ℝ))]
  have hh (i : ι) : (∑ j : ↥F,
      (F.card:ℝ)⁻¹*(F.card:ℝ)⁻¹*((support i ∩ support j.val).card:ℝ)) =
      ∑ j ∈ F, (F.card:ℝ)⁻¹*(F.card:ℝ)⁻¹*((support i ∩ support j).card:ℝ) :=
    (sum_subtype F (p := fun j => j∈F) (fun _ => Iff.rfl)
      (fun j => (F.card:ℝ)⁻¹*(F.card:ℝ)⁻¹*((support i ∩ support j).card:ℝ))).symm
  simp_rw [hh]
  simp only [div_eq_mul_inv, ← sum_mul, ← mul_sum]
  ring

end LooseHamilton.IndexedSurvival
