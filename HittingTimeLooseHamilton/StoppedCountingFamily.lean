module

public import HittingTimeLooseHamilton.Counting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section
noncomputable section
open scoped BigOperators
namespace LooseHamilton.StoppedCounting
variable {E : Type*} [DecidableEq E]
@[expose] def survivingFamily (C : Finset (Finset E)) (H : Finset E) : Finset (Finset E) :=
  C.filter (fun c => c ⊆ H)
@[expose] def familyCount (C : Finset (Finset E)) (H : Finset E) : ℕ :=
  FiniteFamily.count (survivingFamily C H)
@[expose] def marginal (C : Finset (Finset E)) (H : Finset E) (e : E) : ℝ :=
  FiniteFamily.marginal (survivingFamily C H) e
@[expose] def UniformFamily (C : Finset (Finset E)) (k : ℕ) : Prop :=
  ∀ c ∈ C, c.card = k

theorem marginal_nonneg (C : Finset (Finset E)) (H : Finset E) (e : E) :
    0 ≤ marginal C H e := FiniteFamily.marginal_nonneg _ _
theorem marginal_le_one (C : Finset (Finset E)) (H : Finset E) (e : E) :
    marginal C H e ≤ 1 := FiniteFamily.marginal_le_one _ _
theorem sum_marginal (C : Finset (Finset E)) (H : Finset E) (k : ℕ)
    (hC : UniformFamily C k) (hpos : 0 < familyCount C H) :
    ∑ e ∈ H, marginal C H e = (k : ℝ) := by
  apply FiniteFamily.sum_marginal _ H k hpos
  · intro c hc; exact (Finset.mem_filter.mp hc).2
  · intro c hc; exact hC c (Finset.mem_filter.mp hc).1

theorem survivingFamily_erase (C : Finset (Finset E)) (H : Finset E) (e : E) :
    survivingFamily C (H.erase e) = (survivingFamily C H).filter (fun c => e ∉ c) := by
  ext c
  simp only [survivingFamily, Finset.mem_filter]
  constructor
  · rintro ⟨hc, hs⟩
    exact ⟨⟨hc, fun x hx => (Finset.mem_erase.mp (hs hx)).2⟩,
      fun he => (Finset.mem_erase.mp (hs he)).1 rfl⟩
  · rintro ⟨⟨hc, hs⟩, he⟩
    exact ⟨hc, fun x hx => Finset.mem_erase.mpr ⟨fun h => he (h ▸ hx), hs hx⟩⟩

theorem count_erase_add_incidence (C : Finset (Finset E)) (H : Finset E) (e : E) :
    familyCount C (H.erase e) + FiniteFamily.incidenceCount (survivingFamily C H) e =
      familyCount C H := by
  unfold familyCount FiniteFamily.count FiniteFamily.incidenceCount
  rw [survivingFamily_erase, Nat.add_comm]
  exact Finset.card_filter_add_card_filter_not _

theorem count_erase_identity (C : Finset (Finset E)) (H : Finset E) (e : E)
    (hpos : 0 < familyCount C H) :
    (familyCount C (H.erase e) : ℝ) = familyCount C H * (1 - marginal C H e) := by
  have hid := count_erase_add_incidence C H e
  have hr : (familyCount C (H.erase e) : ℝ) +
      FiniteFamily.incidenceCount (survivingFamily C H) e = familyCount C H := by
    exact_mod_cast hid
  have hn : (familyCount C H : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hpos
  change _ = (familyCount C H : ℝ) * (1 -
    (FiniteFamily.incidenceCount (survivingFamily C H) e : ℝ) / familyCount C H)
  field_simp
  nlinarith

theorem count_erase_pos_of_marginal_lt_one (C : Finset (Finset E)) (H : Finset E) (e : E)
    (hpos : 0 < familyCount C H) (hq : marginal C H e < 1) :
    0 < familyCount C (H.erase e) := by
  have : (0 : ℝ) < familyCount C (H.erase e) := by
    rw [count_erase_identity C H e hpos]
    exact mul_pos (Nat.cast_pos.mpr hpos) (sub_pos.mpr hq)
  exact_mod_cast this

theorem log_count_erase (C : Finset (Finset E)) (H : Finset E) (e : E)
    (hpos : 0 < familyCount C H) (hq : marginal C H e < 1) :
    Real.log (familyCount C (H.erase e)) =
      Real.log (familyCount C H) + Real.log (1 - marginal C H e) := by
  rw [count_erase_identity C H e hpos]
  exact Real.log_mul (by exact_mod_cast Nat.ne_of_gt hpos) (ne_of_gt (sub_pos.mpr hq))
@[simp] theorem familyCount_univ [Fintype E] (C : Finset (Finset E)) :
    familyCount C Finset.univ = C.card := by
  simp [familyCount, survivingFamily, FiniteFamily.count]

end LooseHamilton.StoppedCounting
