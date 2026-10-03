module

public import HittingTimeLooseHamilton.NoDeficitBoundary

public section

noncomputable section
namespace LooseHamilton
open Finset Filter

/-- The extra original slack absorbs both a logarithmic sampling threshold
and every fixed bounded vertex deletion. -/
theorem eventually_no_deficit_slack (B : ℝ) (h : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ ell : ℕ,
      |(ell:ℝ)-Nat.floor (epsilon*Real.log n)| ≤ B →
      (ell + Nat.floor (epsilon*Real.log n) + 2*h : ℕ) ≤
        (3*epsilon*Real.log n:ℝ) := by
  have hlog : Tendsto (fun n : ℕ=>Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (max 0 (100*(B+2*h))))] with n hn
  have hn0 : 0 ≤ Real.log (n:ℝ) := (le_max_left _ _).trans hn
  have hnB : 100*(B+2*h) ≤ Real.log (n:ℝ) := (le_max_right _ _).trans hn
  intro ell he
  have hf : (Nat.floor (epsilon*Real.log (n:ℝ)):ℝ) ≤ epsilon*Real.log n :=
    Nat.floor_le (by unfold epsilon; positivity)
  have he' := (abs_le.mp he).2
  push_cast
  unfold epsilon at *
  linarith

/-- Feasibility, the original low-set cardinal bound and a logarithmic slack
threshold are inherited by every bounded boundary, on terminal regularity. -/
theorem eventually_no_deficit_boundary_inheritance (B C : ℝ) (h : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type*) [Fintype V] [DecidableEq V], Fintype.card V=n →
      ∀ (r M : ℕ) (ell : V → ℕ) (markers : Finset (Finset V)),
      CoreAdmissible r M ell markers B → ∀ F : TerminalState V r M ell,
      TerminalRegular C F.val → ∀ D : Finset V, D.card≤h →
      (∀ v, adjustedBoundaryLower ell D (boundaryEdges D F.val) v ≤
        vertexDegree (deleteVertices D F.val) v) ∧
      ((inheritedBoundaryLowVertices F.val D).card:ℝ) ≤ (n:ℝ)^(1/4:ℝ) ∧
      (∀ v, (vertexDegree (deleteVertices D F.val) v:ℝ) ≤ C*Real.log n) ∧
      (∀ v ∉ inheritedBoundaryLowVertices F.val D,
        adjustedBoundaryLower ell D (boundaryEdges D F.val) v + lowerDegreeBase V ≤
          vertexDegree (deleteVertices D F.val) v) := by
  filter_upwards [eventually_no_deficit_slack B h] with n hn
  intro V _ _ hV r M ell markers hadm F hF D hD
  refine ⟨adjustedBoundaryLower_feasible F.val ell D F.property.2.2,?_,?_,?_⟩
  · exact (Nat.cast_le.mpr (inheritedBoundaryLowVertices_card_le F.val D)).trans
      (by simpa only [hV] using hF.low_set)
  · intro v
    rw [vertexDegree_deleteVertices]
    have hm := vertexDegree_mono (filter_subset (fun e=>Disjoint e D) F.val) v.val
    exact (Nat.cast_le.mpr hm).trans (by simpa only [hV] using hF.maximum_degree v.val)
  · apply inherited_boundary_slack F.val ell D (lowerDegreeBase V) hF.pair_degree
    intro v hv
    have hd : 3*epsilon*Real.log (n:ℝ) < vertexDegree F.val v := by
      simpa only [mem_terminalLowVertices,hV,not_le] using hv
    have he := hn (ell v) (by simpa only [lowerDegreeBase,hV] using hadm.offsets v)
    have heN : ell v + lowerDegreeBase V + 2*h ≤ vertexDegree F.val v := by
      unfold lowerDegreeBase
      rw [hV]
      exact_mod_cast (le_of_lt (lt_of_le_of_lt he hd))
    omega

end LooseHamilton
