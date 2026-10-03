module

public import HittingTimeLooseHamilton.CoarseOverlapBudget
public import HittingTimeLooseHamilton.CoarseOverlapIncidence
public import HittingTimeLooseHamilton.CoarseOverlapProjection
public import HittingTimeLooseHamilton.CoarseOverlapParameters
public import HittingTimeLooseHamilton.OverlapMoments

public section

noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open FiniteEntropy Filter Finset
variable {r : ℕ}

@[expose] def ordinaryOverlap (D : BiasedRoleInstance r) : ℝ :=
  D.cycleLaw.independentOverlap Subtype.val

theorem coarse_ordinary_overlap_bound (D : BiasedRoleInstance r) (hr : 3≤r)
    (C B C₁ C₂ : ℝ) (hC : 1≤C) (hB : 0≤B) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (hμ : 1<D.μ)
    (hdeg : ∀v,(vertexDegree D.host v:ℝ)≤C*D.μ)
    (hent : (D.k:ℝ)*Real.log D.μ-B*D.N≤entropy D.cycleLaw.mass)
    (hK : D.KahnBounds hr C₁ C₂) :
    D.ordinaryOverlap ≤ (r:ℝ)^2*coarseOverlapConstant r C B C₁ C₂*D.N/Real.log D.μ := by
  have hp := BiasedEnsemble.original_collision_le hr
    (fun e he => (mem_completeEdges _ _).mp (D.host_uniform he)) D.root D.initial D.cycleLaw
  have hi := D.coarse_actual_incidence_bound hr C B C₁ C₂ hC hB hC₁ hC₂ hμ hdeg hent hK
  rw [ordinaryOverlap, Law.independentOverlap_eq_sum_sq]
  apply hp.trans
  have he : (∑i,D.ensembleLaw.mass i *
      ∑f∈(D.ensembleHost hr i).edges,
        ((D.ensembleMatchingLaw hr i).event (fun M => f∈M.val.val))^2) ≤
      ∑i,D.ensembleLaw.mass i * ∑v,∑e : KahnIncident (D.ensembleHost hr i) v,
        ((kahnIncidentLaw (D.ensembleMatchingLaw hr i) v).mass e)^2 := by
    apply sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left
      (coarse_edge_collision_le_incidence _ _ (by omega)) (D.ensembleLaw.nonneg i)
  have hh := mul_le_mul_of_nonneg_left (he.trans hi) (sq_nonneg (r:ℝ))
  convert hh using 1 <;> first | rfl | ring

/-- Uniform big-O constants are chosen before the sequence of hosts or laws. -/
theorem eventual_ordinary_overlap_bound (r : ℕ) (hr : 3≤r)
    (C B : ℝ) (hC : 0<C) (hB : 0≤B) :
    ∃K : ℝ, 0<K ∧ ∀D : ℕ→BiasedRoleInstance r,
      Tendsto (fun n => (D n).μ) atTop atTop →
      (∀ᶠn in atTop,∀v,(vertexDegree (D n).host v:ℝ)≤C*(D n).μ) →
      (∀ᶠn in atTop,((D n).k:ℝ)*Real.log (D n).μ-B*(D n).N≤entropy (D n).cycleLaw.mass) →
      ∀ᶠn in atTop,(D n).ordinaryOverlap≤K*(D n).N/Real.log (D n).μ := by
  obtain ⟨C₁,C₂,hC₁,hC₂,N₀,hKahn⟩ := Kahn.theorem42 r hr
  let K := (r:ℝ)^2*coarseOverlapConstant r (C+1) B C₁ C₂
  have hK0 : 0≤K := mul_nonneg (sq_nonneg _) (coarseOverlapConstant_nonneg r (by linarith) hB hC₁.le hC₂.le)
  refine ⟨K+1,by linarith,?_⟩
  intro D hμ hdeg hent
  have hthreshold := (k_tendsto_without_sparse_markers hr D hμ).eventually (eventually_ge_atTop N₀)
  filter_upwards [hμ.eventually (eventually_gt_atTop 1),hthreshold,hdeg,hent] with n hm hn hd he
  have hk : (D n).KahnBounds hr C₁ C₂ := by
    intro i
    apply hKahn (r*(D n).k) _ (dvd_mul_right r (D n).k)
      ((D n).ensembleHost hr i) ((D n).ensembleMatchingLaw hr i)
    have hr1 : 1≤r := by omega
    nlinarith
  have hh := (D n).coarse_ordinary_overlap_bound hr (C+1) B C₁ C₂ (by linarith) hB hC₁.le hC₂.le hm
    (fun v => (hd v).trans (by nlinarith)) he hk
  exact hh.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : K≤K+1) (Nat.cast_nonneg _)) (Real.log_pos hm).le)
end LooseHamilton.BiasedRoleInstance
