module

public import HittingTimeLooseHamilton.BootstrapSamplingGates
public import HittingTimeLooseHamilton.BootstrapActualSourceFrames
public import HittingTimeLooseHamilton.PrivateCompletionLifting

public section

/-! Elementary parameter gates and actual source-frame construction for the
private bootstrap. Frame existence follows from residual completion legality. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateAdmissibleParameters
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The terminal mean lower bound implies the required ambient lower time. -/
theorem later_time_lower {r M j : ℕ} (hr : 3 ≤ r)
    (hN : 0 < Fintype.card V) (hj : M ≤ j)
    (hmean : Real.log (Fintype.card V : ℝ)/2 ≤ meanDegree (V := V) r M) :
    (1 / (2 * (r : ℝ))) * (Fintype.card V : ℝ) *
      Real.log (Fintype.card V : ℝ) ≤ (j : ℝ) := by
  have h := BootstrapCatalogue.later_mean_lower hj hmean
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hN
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  unfold meanDegree at h
  have hh := (le_div_iff₀ hn).mp h
  have he : (1 / (2 * (r : ℝ))) * (Fintype.card V : ℝ) *
      Real.log (Fintype.card V : ℝ) =
      (Real.log (Fintype.card V : ℝ) / 2 * Fintype.card V) / r := by ring
  rw [he]
  apply (div_le_iff₀ hr').mpr
  nlinarith

/-- Every legal residual private source is realized by an actual ambient frame. -/
theorem exists_source {r : ℕ} {M : Finset (Finset V)}
    (hM : IsPairMatching M) (b : Base M) (hr : 3 ≤ r)
    (S q : Finset ↥(active b)) (x : ↥(active b))
    (hs : LegalPrivateCompletion r (restrictEdges (active b) (markers hM b))
      (insert x S) q) :
    ∃ F : AuxiliaryFrame.Frame r M,
      F.val.deleted = deleted b ∪ liftEdge (active b) (insert x S) ∧
      F.markers = insert (liftEdge (active b) q) (markers hM b) ∧
      F.val.relative = none := by
  obtain ⟨u,v,huv,hq⟩ := card_eq_two.mp hs.pair_card
  have hpair : liftEdge (active b) q = {u.val,v.val} := by rw [hq, liftEdge_pair]
  have hl := hs.lift
  rw [hpair] at hl
  have hp : ({u.val,v.val} : Finset V) ⊆ active b := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact u.property
    · exact v.property
  obtain ⟨F,hd,hm,_,hrel⟩ := BootstrapActualSourceFrames.exists_source hM b hr
    (liftEdge (active b) (insert x S)) u.val v.val hl hp
  exact ⟨F,hd,by simpa only [hpair] using hm,hrel⟩

/-- The large-source bound is strictly positive whenever the ambient source is. -/
theorem positive_source_of_large {N r X W : ℕ} (hN : 0 < N) (hX : 0 < X)
    (hlarge : (X : ℝ) / (N : ℝ)^(3*r) ≤ (W : ℝ)) : 0 < W := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hw : (0 : ℝ) < W := (div_pos hx (pow_pos hn _)).trans_le hlarge
  exact_mod_cast hw

end LooseHamilton.BootstrapPrivateAdmissibleParameters
