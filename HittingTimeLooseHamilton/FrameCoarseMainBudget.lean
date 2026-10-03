module

public import HittingTimeLooseHamilton.FrameEntropyUniform
public import HittingTimeLooseHamilton.CoarseOverlapUniform

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Filter FiniteEntropy

/-- The imposed entropy budget yields the coarse bound in the active size.
The factor two accounts for the bounded deleted vertex set. -/
theorem coarse_budget_eventually (r : ℕ) (hr : 3≤r) (B : ℝ) (hB : 0≤B) :
    ∀ᶠ N : ℕ in atTop, ∀ original : Finset (Finset (Fin N)),
      ∀ F : Frame r original, ∀ H : SimpleHypergraph (Fin N),
      F.entropyBudget H B →
      (F.k:ℝ)*Real.log (F.mu H)- (2*((r:ℝ)-1+B))*F.n ≤
        Real.log (F.cycleCount H) := by
  filter_upwards [eventually_ge_atTop (8*r+4),
    FrameScales.L1_tendsto.eventually (eventually_ge_atTop 1)] with N hN hlog original F H hb
  have hn := F.n_add_deleted
  have hd := F.val.deleted_card_le
  simp only [Fintype.card_fin] at hn
  have hnN : F.n ≤ N := by omega
  have hNn : (N:ℝ) ≤ 2*F.n := by exact_mod_cast (show N≤2*F.n by omega)
  have hscale : 1≤Real.sqrt (FrameScales.L1 N) := by
    simpa using Real.sqrt_le_sqrt hlog
  have hc := FrameEntropy.budget_coarse hr (F.entropyBudget_mu_pos hr H hb) hB
    (F.k_le_n.trans hnN) hscale (by simpa only [entropyBudget, Fintype.card_fin] using hb)
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hmul := mul_le_mul_of_nonneg_left hNn (show 0≤(r:ℝ)-1+B by linarith)
  change (F.k:ℝ)*Real.log (F.mu H)-((r:ℝ)-1+B)*N ≤ Real.log (F.cycleCount H) at hc
  nlinarith

/-- Main-family coarse overlap, for actual simultaneous-direction cycle laws.
The constant is chosen before the original vertex-size sequence or any frame. -/
theorem entropyInstance_coarse_overlap (r : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃ K : ℝ, 0<K ∧ ∀ N : ℕ→ℕ, Tendsto N atTop atTop →
      ∀ original : (i : ℕ) → Finset (Finset (Fin (N i))),
      ∀ F : (i : ℕ) → Frame r (original i),
      ∀ H : (i : ℕ) → SimpleHypergraph (Fin (N i)),
      ∀ budget : ∀i, (F i).entropyBudget (H i) B,
      Tendsto (fun i => (F i).mu (H i)) atTop atTop →
      (∀ᶠ i in atTop, ∀v,
        (vertexDegree ((F i).entropyInstance (H i) (budget i).1).host v:ℝ) ≤
          C*(F i).mu (H i)) →
      ∀ᶠ i in atTop,
        ((F i).entropyInstance (H i) (budget i).1).ordinaryOverlap ≤
          K*(N i:ℝ)/Real.log ((F i).mu (H i)) := by
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  obtain ⟨K,hK,hbound⟩ := BiasedRoleInstance.eventual_ordinary_overlap_bound r hr C
    (2*((r:ℝ)-1+B)) hC (by nlinarith)
  refine ⟨K,hK,?_⟩
  intro N hN original F H budget hmu hdeg
  let D := fun i => (F i).entropyInstance (H i) (budget i).1
  have hμ : Tendsto (fun i => (D i).μ) atTop atTop := by simpa [D] using hmu
  have he : ∀ᶠ i in atTop, (D i).k*Real.log (D i).μ-
      (2*((r:ℝ)-1+B))*(D i).N ≤ entropy (D i).cycleLaw.mass := by
    filter_upwards [hN.eventually (coarse_budget_eventually r hr B hB)] with i hi
    change _ ≤ entropy ((F i).entropyInstance (H i) (budget i).1).cycleLaw.mass
    rw [(F i).entropyInstance_entropy]
    simpa only [D, entropyInstance_k, entropyInstance_N, entropyInstance_mu] using hi (original i) (F i) (H i) (budget i)
  have hh := hbound D hμ (by simpa [D] using hdeg) he
  filter_upwards [hh,hmu.eventually (eventually_gt_atTop 1)] with i hi hmi
  apply hi.trans
  have hn := (F i).n_add_deleted
  simp only [Fintype.card_fin] at hn
  have hnN : ((F i).n:ℝ)≤N i := by exact_mod_cast (show (F i).n≤N i by omega)
  simp only [D, entropyInstance_N, entropyInstance_mu]
  change K*(F i).n/Real.log ((F i).mu (H i)) ≤ _
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnN hK.le) (Real.log_pos hmi).le

end LooseHamilton.AuxiliaryFrame.Frame
