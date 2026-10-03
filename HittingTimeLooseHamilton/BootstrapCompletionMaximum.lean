module

public import HittingTimeLooseHamilton.BootstrapOriginalFrame
public import HittingTimeLooseHamilton.BootstrapFrameMeanNormalization
public import HittingTimeLooseHamilton.BootstrapMaximumMeans

public section

/-! The original frame and a finite maximum argument on its actual legal
completion labels. -/
noncomputable section
namespace LooseHamilton.BootstrapCompletionMaximum
open Finset AuxiliaryFrame
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

theorem exists_original_frame (hM : IsPairMatching M) (hne : M.Nonempty) :
    ∃ F : Frame r M, F.val.deleted = ∅ ∧ F.markers = M ∧ F.val.relative = none := by
  obtain ⟨e,he⟩ := hne
  obtain ⟨u,v,huv,hpair⟩ := card_eq_two.mp (hM.1 e he)
  obtain ⟨F,hd,hm,_,hrel⟩ := exists_frame r M M ∅ (u,v) none hM hM
    (by simp) ⟨by simp,by simp⟩ (by simp) (by simpa [hpair] using he) (by simp)
  exact ⟨F,hd,hm,hrel⟩

/-- The maximum is taken on the finite set of actual directed legal labels;
its value is the unoriented completion count. -/
@[expose] def weight (H : SimpleHypergraph V) (a : Finset V × V × V) : ℕ :=
  completionCount r M (H ∩ allowedEdges r (originalPorts M)) a.1 {a.2.1,a.2.2}

theorem exists_maximum (F : Frame r M) (H : SimpleHypergraph V)
    (hne : F.candidates.Nonempty) :
    ∃ a ∈ F.candidates, ∀ b ∈ F.candidates,
      weight (r:=r) (M:=M) H b ≤ weight (r:=r) (M:=M) H a := by
  exact Finset.exists_max_image _ _ hne

/-- A bound on the actual low-weight labels supplies the precise intersection
hypothesis; no independently chosen large family is required. -/
theorem bound_of_failed_labels (F : Frame r M) (hr : 3 ≤ r)
    (hd : F.val.deleted = ∅) (hm : F.markers = M) (hrel : F.val.relative = none)
    (H : SimpleHypergraph V) (α κ B δ : ℝ) (hκ : 0 < κ)
    (hX : 0 < cycleCount r M H (originalPorts M))
    (hbalance : ¬F.candidateBad H α)
    (hfailed : ((F.candidates.filter (fun a => (weight (r:=r) (M:=M) H a:ℝ) < κ*B)).card:ℝ)
      ≤ δ)
    (hintersection : δ + 2*α*(F.candidates.card:ℝ) < F.candidates.card) :
    B ≤ (2*(1+α)/κ)*((cycleCount r M H (originalPorts M):ℝ)/
      (((r:ℝ)-1)^2*F.mu H)) := by
  classical
  let large := F.candidates.filter (fun a => κ*B ≤ (weight (r:=r) (M:=M) H a:ℝ))
  have hmu : 0 < F.mu H := F.mu_pos_of_cycleCount_pos hr H (by
    rw [F.original_cycleCount hr hrel hd hm H]; exact hX)
  have hscale : 0 < (cycleCount r M H (originalPorts M):ℝ)/
      (((r:ℝ)-1)^2*F.mu H) := by
    have hrr : 1 < (r:ℝ) := by exact_mod_cast (show 1 < r by omega)
    exact div_pos (Nat.cast_pos.mpr hX) (mul_pos (sq_pos_of_pos (by linarith)) hmu)
  apply F.original_maximum_le hr hrel hd hm H α κ B hκ hscale hbalance large
    (filter_subset _ _) (by intro a ha; exact (mem_filter.mp ha).2)
  have he : F.candidates \ large = F.candidates.filter
      (fun a => (weight (r:=r) (M:=M) H a:ℝ) < κ*B) := by
    ext a
    simp [large]; tauto
  rw [he]
  linarith

/-- Converting the original allowed-host mean to the raw mean incurs only
an explicit constant, independent of the source label. -/
theorem bound_of_failed_labels_raw (F : Frame r M) (hr : 3 ≤ r)
    (hd : F.val.deleted = ∅) (hm : F.markers = M) (hrel : F.val.relative = none)
    (H : SimpleHypergraph V) (α κ B δ μ : ℝ) (hκ : 0 < κ)
    (hX : 0 < cycleCount r M H (originalPorts M))
    (hα : α ≤ 1/2) (hμ : 0 < μ) (hmean : μ/2 ≤ F.mu H)
    (hbalance : ¬F.candidateBad H α)
    (hfailed : ((F.candidates.filter (fun a => (weight (r:=r) (M:=M) H a:ℝ) < κ*B)).card:ℝ)
      ≤ δ)
    (hintersection : δ + 2*α*(F.candidates.card:ℝ) < F.candidates.card) :
    B ≤ (6/(κ*((r:ℝ)-1)^2))*(cycleCount r M H (originalPorts M):ℝ)/μ := by
  have hb := bound_of_failed_labels F hr hd hm hrel H α κ B δ hκ hX
    hbalance hfailed hintersection
  have hrr : 1 < (r:ℝ) := by exact_mod_cast (show 1 < r by omega)
  have hsq : 0 < ((r:ℝ)-1)^2 := sq_pos_of_pos (by linarith)
  have hmupos : 0 < F.mu H := by linarith
  have hscale : 0 ≤ (cycleCount r M H (originalPorts M):ℝ)/
      (((r:ℝ)-1)^2*F.mu H) := by positivity
  have hcoeff : 2*(1+α)/κ ≤ 3/κ := (div_le_div_iff_of_pos_right hκ).mpr (by linarith)
  refine hb.trans ((mul_le_mul_of_nonneg_right hcoeff hscale).trans ?_)
  have hden : ((r:ℝ)-1)^2*μ ≤ 2*(((r:ℝ)-1)^2*F.mu H) := by nlinarith
  apply (le_div_iff₀ hμ).mpr
  rw [div_mul_eq_mul_div 6]
  apply (le_div_iff₀ (mul_pos hκ hsq)).mpr
  have hh : (cycleCount r M H (originalPorts M):ℝ)*(((r:ℝ)-1)^2*μ)/
      (((r:ℝ)-1)^2*F.mu H) ≤ 2*(cycleCount r M H (originalPorts M):ℝ) := by
    apply (div_le_iff₀ (mul_pos hsq hmupos)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hden
      (Nat.cast_nonneg (cycleCount r M H (originalPorts M)) : (0:ℝ)≤_)]
  have he : (3/κ*((cycleCount r M H (originalPorts M):ℝ)/
      (((r:ℝ)-1)^2*F.mu H))*μ*(κ*((r:ℝ)-1)^2) =
      3*((cycleCount r M H (originalPorts M):ℝ)*(((r:ℝ)-1)^2*μ)/
        (((r:ℝ)-1)^2*F.mu H))) := by field_simp <;> ring
  rw [he]
  nlinarith
 
/-- Choosing a genuine maximum also handles the negligible-source branch.
Only the large maximum needs the actual low-label bound. -/
theorem all_weights_le_of_failed_labels {N : ℕ} {M : Finset (Finset (Fin N))}
    (F : Frame r M) (hr : 3 ≤ r) (hN : 1 ≤ N)
    (hd : F.val.deleted = ∅) (hm : F.markers = M) (hrel : F.val.relative = none)
    (H : SimpleHypergraph (Fin N)) (hH : H ⊆ completeEdges (Fin N) r)
    (α κ δ : ℝ) (hκ : 0 < κ)
    (hX : 0 < cycleCount r M H (originalPorts M)) (hα : α ≤ 1/2)
    (hμ : 0 < meanDegree (V:=Fin N) r H.card)
    (hmean : meanDegree (V:=Fin N) r H.card/2 ≤ F.mu H)
    (hbalance : ¬F.candidateBad H α)
    (hfailed : ∀ a ∈ F.candidates,
      (cycleCount r M H (originalPorts M):ℝ)/(N:ℝ)^(2*r) ≤ weight (r:=r) (M:=M) H a →
      ((F.candidates.filter (fun b => (weight (r:=r) (M:=M) H b:ℝ) <
        κ*(weight (r:=r) (M:=M) H a:ℝ))).card:ℝ) ≤ δ)
    (hintersection : δ+2*α*(F.candidates.card:ℝ)<F.candidates.card) :
    ∀ a ∈ F.candidates, (weight (r:=r) (M:=M) H a:ℝ) ≤
      max (r:ℝ) (6/(κ*((r:ℝ)-1)^2)) *
        (cycleCount r M H (originalPorts M):ℝ)/meanDegree (V:=Fin N) r H.card := by
  intro a ha
  obtain ⟨b,hb,hmax⟩ := exists_maximum F H ⟨a,ha⟩
  have hle : (weight (r:=r) (M:=M) H a:ℝ) ≤ weight (r:=r) (M:=M) H b := Nat.cast_le.mpr (hmax a ha)
  have hXnonneg : (0:ℝ) ≤ cycleCount r M H (originalPorts M) := Nat.cast_nonneg _
  by_cases hlarge : (cycleCount r M H (originalPorts M):ℝ)/(N:ℝ)^(2*r) ≤ weight (r:=r) (M:=M) H b
  · have hbound := bound_of_failed_labels_raw F hr hd hm hrel H α κ
      (weight (r:=r) (M:=M) H b:ℝ) δ (meanDegree (V:=Fin N) r H.card) hκ hX hα hμ hmean
      hbalance (hfailed b hb hlarge) hintersection
    exact hle.trans (hbound.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hXnonneg) hμ.le))
  · have htiny := BootstrapMaximumMeans.tiny_source_le (by omega : 1≤r) hN H hH
      hμ (cycleCount r M H (originalPorts M):ℝ) hXnonneg
    exact hle.trans ((le_of_not_ge hlarge).trans (htiny.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hXnonneg) hμ.le)))

end LooseHamilton.BootstrapCompletionMaximum
