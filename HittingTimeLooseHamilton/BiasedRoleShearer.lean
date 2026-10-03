module

public import HittingTimeLooseHamilton.BiasedShearerFixedCount
public import Mathlib.Data.Finset.Prod

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy
variable {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]

/-- The Bernoulli-compatible junction pattern for a directed role. -/
@[expose] def roleJunctionPattern (s : Finset V) (u v : V) : s → Bool :=
  fun w => decide (w.val = u ∨ w.val = v)

/-- Probability that precisely the prescribed two vertices of the edge are
junctions. The two ordered roles use the same compatibility event. -/
@[expose] def roleCompatibilityProbability (p : Law Ω) (X : Ω → V → Bool)
    (s : Finset V) (u v : V) : ℝ :=
  (coordinateRestrictionLaw p X s).mass (roleJunctionPattern s u v)

lemma roleCompatibilityProbability_eq_event (p : Law Ω) (X : Ω → V → Bool)
    (s : Finset V) (u v : V) :
    roleCompatibilityProbability p X s u v =
      p.event (fun ω => ∀ w : s, X ω w.val = decide (w.val = u ∨ w.val = v)) := by
  unfold roleCompatibilityProbability coordinateRestrictionLaw Law.map
  apply congrArg p.event
  funext ω
  exact propext funext_iff

lemma bernoulli_roleJunctionPattern_mass (s : Finset V) {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (independentCoordinateLaw (fun _ : s => bernoulliBitLaw a ha0 ha1)).mass
      (roleJunctionPattern s u v) = a^2 * (1-a)^(s.card-2) := by
  have hne : (⟨u,hu⟩ : s) ≠ ⟨v,hv⟩ := fun h => huv (congrArg Subtype.val h)
  have h := bernoulli_two_point_pattern_mass a ha0 ha1 (⟨u,hu⟩ : s) ⟨v,hv⟩ hne
  have hf : (fun w : s => decide (w ∈ ({⟨u,hu⟩,⟨v,hv⟩} : Finset s))) =
      roleJunctionPattern s u v := by
    funext w
    simp [roleJunctionPattern, Subtype.ext_iff]
  rw [hf] at h
  simpa only [Fintype.card_coe] using h

lemma roleCompatibility_error_le (p : Law Ω) (X : Ω → V → Bool)
    (s : Finset V) {u v : V} (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |roleCompatibilityProbability p X s u v - a^2*(1-a)^(s.card-2)| ≤
      coordinateMarginalError p X (fun _ => bernoulliBitLaw a ha0 ha1) s := by
  rw [← bernoulli_roleJunctionPattern_mass s hu hv huv a ha0 ha1]
  unfold roleCompatibilityProbability coordinateMarginalError
  exact Finset.single_le_sum (fun x _ => abs_nonneg
    ((coordinateRestrictionLaw p X s).mass x -
      (independentCoordinateLaw (fun _ : s => bernoulliBitLaw a ha0 ha1)).mass x))
    (Finset.mem_univ (roleJunctionPattern s u v))

/-- Total role-compatibility error for any bounded-degree family of r-sets. -/
theorem roleCompatibility_sum_le {I : Type*} [Fintype I]
    (p : Law Ω) (X : Ω → V → Bool) (e : I → Finset V)
    (r : ℕ) (he : ∀ i, (e i).card = r)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (D : ℝ) (hD : 0 ≤ D)
    (hdeg : ∀ v, (∑ i, if v ∈ e i then (1 : ℝ) else 0) ≤ D) :
    (∑ i, ∑ uv ∈ (e i).offDiag,
      |roleCompatibilityProbability p X (e i) uv.1 uv.2 - a^2*(1-a)^(r-2)|) ≤
      (r*(r-1) : ℕ) * Real.sqrt (4*(Fintype.card I:ℝ)*D*
        coordinateDeficit p X (coordinateCrossEntropy p X
          (fun _ => bernoulliBitLaw a ha0.le ha1.le)) Finset.univ) := by
  classical
  let q : V → Law Bool := fun _ => bernoulliBitLaw a ha0.le ha1.le
  let d : I → ℝ := fun i => coordinateMarginalError p X q (e i)
  have hlocal (i : I) : (∑ uv ∈ (e i).offDiag,
      |roleCompatibilityProbability p X (e i) uv.1 uv.2 - a^2*(1-a)^(r-2)|) ≤
      (r*(r-1) : ℕ) * d i := by
    calc
      _ ≤ ∑ uv ∈ (e i).offDiag, d i := by
        apply Finset.sum_le_sum
        intro uv huv
        obtain ⟨hu,hv,hne⟩ := Finset.mem_offDiag.mp huv
        simpa only [he i] using roleCompatibility_error_le p X (e i) hu hv hne a ha0.le ha1.le
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.offDiag_card, he]
        simp [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hs := coordinateMarginalError_sum_sq p X q (fun _ => bernoulliBitLaw_pos ha0 ha1)
    e D hD hdeg
  have hb : (∑ i, d i) ≤ Real.sqrt (4*(Fintype.card I:ℝ)*D*
      coordinateDeficit p X (coordinateCrossEntropy p X q) Finset.univ) := by
    apply Real.le_sqrt_of_sq_le
    exact hs
  calc
    _ ≤ ∑ i, (r*(r-1) : ℕ) * d i := Finset.sum_le_sum (fun i _ => hlocal i)
    _ = (r*(r-1) : ℕ) * ∑ i, d i := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)

end LooseHamilton
