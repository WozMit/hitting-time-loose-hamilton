module

public import HittingTimeLooseHamilton.FrameEntropyScalarTransport
public import HittingTimeLooseHamilton.CandidateEntropyTolerance
public import HittingTimeLooseHamilton.FrameEntropyBridgeExisting

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset Filter

/-- Uniform-in-t entropy bound for the actual prescribed-direction frame law.
The regularity window L is explicitly at least six, matching marker transport. -/
theorem entropyInstance_exceptional_rate (r : ℕ) (hr : 3≤r)
    (C B L : ℝ) (hC : 0<C) (hB : 0≤B) (hL : 6≤L) :
    ∃ K : ℝ, 0<K ∧ ∀ N : ℕ→ℕ, Tendsto N atTop atTop →
      ∀ original : (i : ℕ) → Finset (Finset (Fin (N i))),
      ∀ F : (i : ℕ) → AuxiliaryFrame.Frame r (original i),
      ∀ H : (i : ℕ) → SimpleHypergraph (Fin (N i)),
      ∀ budget : ∀ i, (F i).entropyBudget (H i) B,
      Tendsto (fun i => (F i).mu (H i)) atTop atTop →
      (∀ᶠ i in atTop, ((original i).card:ℝ) ≤ (N i:ℝ)^(1/10:ℝ)) →
      (∀ᶠ i in atTop, PathGraphUpperRegular r C L
        ((F i).entropyInstance (H i) (budget i).1).host) →
      ∀ᶠ i in atTop, ∀ t : ℝ, 0<t →
        ((F i).entropyInstance (H i) (budget i).1).exceptionalProportion t ≤
          K/(t*Real.sqrt (Real.log (Real.log (N i:ℝ)))) := by
  obtain ⟨K,hK,hbound⟩ := entropy_path_exceptional_roles_uniform r hr C hC (2*B) L
  refine ⟨2*K,by positivity,?_⟩
  intro N hN original F H budget hmu ho hreg
  let D := fun i => (F i).entropyInstance (H i) (budget i).1
  have hmut : Tendsto (fun i => (D i).μ) atTop atTop := by simpa [D] using hmu
  have hs : ∀ᶠ i in atTop, ((D i).s:ℝ)≤L*((D i).N:ℝ)^(1/10:ℝ) := by
    filter_upwards [hN.eventually (CandidateBalance.eventually_frame_marker_transport r),ho]
      with i hi ho
    have hh := hi (original i) ho (F i)
    simp only [D,entropyInstance_s,entropyInstance_N]
    exact hh.trans (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hx := hN.eventually (CandidateBalance.eventually_frame_entropy_transport r B hB)
  have hb := hbound D (fun i => (F i).entropyXi B) hmut hs hreg
    (by filter_upwards [hx] with i hi; exact ⟨(hi (original i) (F i)).1,
      (hi (original i) (F i)).2.1⟩)
    (Eventually.of_forall (fun i => (F i).imposed_budget_entropyBound (H i) B (budget i)))
  have hlogs := (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN))).eventually
      (eventually_gt_atTop 0)
  have hloga := (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp (BiasedRoleInstance.N_real_tendsto_atTop D hmut))).eventually
      (eventually_gt_atTop 0)
  filter_upwards [hb,hx,hlogs,hloga] with i hi hx hlN hln
  intro t ht
  have hnpos : 0<Real.sqrt (Real.log (Real.log ((F i).n:ℝ))) := Real.sqrt_pos.mpr hln
  have hNpos := Real.sqrt_pos.mpr hlN
  have hh := (hx (original i) (F i)).2.2
  apply (hi t ht).trans
  change K/(t*Real.sqrt (Real.log (Real.log ((F i).n:ℝ)))) ≤ _
  apply (div_le_div_iff₀ (mul_pos ht hnpos) (mul_pos ht hNpos)).mpr
  dsimp only [Function.comp_def] at *
  nlinarith [mul_le_mul_of_nonneg_left hh (mul_nonneg hK.le ht.le)]


/-- Converts the existing-role proportion into a count bounded by all raw edges.
The zero-eligible-role case is included and does not assume a positive count. -/
theorem existingExceptional_count_of_proportion
    {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    {original : Finset (Finset V)} (F : Frame r original) (hr : 2≤r)
    (H : SimpleHypergraph V) (t q : ℝ) (hq : 0≤q)
    (hp : F.existingExceptionalProportion H t ≤ q) :
    ((F.existingExceptional H t).card:ℝ) ≤ q*(r*(r-1:ℕ):ℕ)*(F.m H:ℝ) := by
  have hc : (F.existingExceptional H t).card ≤ (F.existingCandidates H).card :=
    card_le_card (filter_subset _ _)
  have hb : (F.existingCandidates H).card ≤ F.m H*(r*(r-1)) := by
    rw [F.existingCandidates_card hr]
    exact Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _))
  by_cases hz : (F.existingCandidates H).card=0
  · have he : (F.existingExceptional H t).card=0 := by omega
    rw [he, Nat.cast_zero]
    positivity
  · have hpos : 0<((F.existingCandidates H).card:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hz)
    have hh := (div_le_iff₀ hpos).mp hp
    have hbr : ((F.existingCandidates H).card:ℝ) ≤ (F.m H:ℝ)*(r*(r-1:ℕ):ℕ) := by exact_mod_cast hb
    calc
      _ ≤ _ := hh
      _ ≤ q*((F.m H:ℝ)*(r*(r-1:ℕ):ℕ)) := mul_le_mul_of_nonneg_left hbr hq
      _ = _ := by ring

end LooseHamilton.AuxiliaryFrame.Frame
