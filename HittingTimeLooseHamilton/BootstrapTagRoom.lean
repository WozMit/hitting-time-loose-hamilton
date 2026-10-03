module

public import HittingTimeLooseHamilton.FrameScalarEnvelopes
public import HittingTimeLooseHamilton.Setup

public section

/-! Two unused vertices exist uniformly at the admissible marker scale.
The bound is chosen before the original matching and the sampled outcome.
-/
noncomputable section
namespace LooseHamilton.BootstrapTagFrames
open Filter

theorem eventually_tag_room :
    ∀ᶠ N : ℕ in atTop, ∀ s : ℕ, (s : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) →
      2*s+2 ≤ N := by
  filter_upwards [CandidateBalance.eventually_frame_loss_small 2 2 1 (by norm_num)]
    with N hN s hs
  have hb : (2*(s:ℝ)+2) ≤ 2*(N:ℝ)^(1/10:ℝ)+2 := by linarith
  have hh := hN (2*(s:ℝ)+2) hb
  norm_num only [one_mul] at hh
  exact_mod_cast hh

/-- The only extra finite size requirement of the tag construction follows
uniformly from the existing admissibility hypotheses. -/
theorem eventually_admissible_tag_room :
    ∀ᶠ N : ℕ in atTop, ∀ (r M : ℕ) (ell : Fin N → ℕ)
      (original : Finset (Finset (Fin N))) (offset : ℝ),
      CoreAdmissible r M ell original offset → 2*original.card+2 ≤ N := by
  filter_upwards [eventually_tag_room] with N hN r M ell original offset hadm
  exact hN original.card (by simpa using hadm.markers_small)

end LooseHamilton.BootstrapTagFrames
