module

public import HittingTimeLooseHamilton.BiasedEntropyBudgetAbsorb

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open FiniteEntropy Filter Topology

/-- The three-deficit bound for the actual sequence of conditioned clone hosts.
The constant is chosen before the instance and error sequences, and depends
only on fixed r,C. Kahn's cached theorem is used with its uniform constants. -/
theorem eventual_entropy_deficit_bound (r : ℕ) (hr : 3≤r) (C : ℝ) (hC : 0<C) :
    ∃ B : ℝ, 0<B ∧
    ∀ (D : ℕ → BiasedRoleInstance r) (ξ δ : ℕ → ℝ),
      Tendsto (fun n => (D n).μ) atTop atTop →
      Tendsto (fun n => ((D n).s:ℝ)/(D n).N) atTop (nhds 0) →
      Tendsto (fun n => (D n).η) atTop (nhds 0) →
      Tendsto δ atTop (nhds 0) → Tendsto ξ atTop (nhds 0) →
      (∀ᶠ n in atTop,0≤ξ n) →
      (∀ᶠ n in atTop,∀v,(vertexDegree (D n).host v:ℝ)≤C*(D n).μ) →
      (∀ᶠ n in atTop,(D n).partitionBound (δ n)) →
      (∀ᶠ n in atTop,(D n).entropyBound (ξ n)) →
      ∀ᶠ n in atTop,(D n).entropyDeficit hr ≤
        B*((D n).N:ℝ)*biasedRoleError r (D n).N (D n).s (ξ n) (δ n) (D n).η := by
  obtain ⟨C₁,C₂,hC₁,hC₂,N₀,hKahn⟩ := Kahn.theorem42 r hr
  obtain ⟨B,hB,hfinite⟩ := finite_entropy_deficit_rate r hr C hC C₁ C₂ hC₁.le hC₂.le
  refine ⟨B,hB,?_⟩
  intro D ξ δ hμ hs hη _hδ hξ hξ0 hdeg hpart hent
  let K : ℝ := (r.choose 2:ℝ)/C
  have hK : 0<K := div_pos (by exact_mod_cast Nat.choose_pos (by omega : 2≤r)) hC
  have hηpos : ∀ᶠ n in atTop,0<(D n).η := Eventually.of_forall (fun n => (D n).η_pos hr)
  have hζpos : ∀ᶠ n in atTop,0<(D n).cloneCollisionRate C :=
    Eventually.of_forall (fun n => (D n).cloneCollisionRate_pos hr C hC)
  have hcomp : ∀ᶠ n in atTop,(D n).cloneCollisionRate C≤K*(D n).η :=
    Eventually.of_forall (fun n => (D n).cloneCollisionRate_le hr C hC)
  have hlogs := eventually_comparable_inverse_log_bound hη hηpos hζpos hK hcomp
  have hηsmall := hη.eventually (gt_mem_nhds (one_div_pos.mpr hK))
  have hζone : ∀ᶠ n in atTop,(D n).cloneCollisionRate C<1 := by
    filter_upwards [hηsmall,hcomp] with n hn hc
    have hm := (lt_div_iff₀ hK).mp hn
    nlinarith
  have hηone := hη.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hξone : ∀ᶠ n in atTop,ξ n≤1 := by
    filter_upwards [hξ.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
    exact hn.le
  have hμone := eventually_mu_one D hμ
  have hrange := eventually_sparse_marker_range hr D hs
  have hlogN := eventually_log_N_one D hμ
  have hthreshold := (k_tendsto_atTop hr D hμ hs).eventually (eventually_ge_atTop N₀)
  have hconditional : ∀ᶠ n in atTop,(D n).KahnBounds hr C₁ C₂ := by
    filter_upwards [hthreshold] with n hn
    intro i
    apply hKahn (r*(D n).k) _ (dvd_mul_right r (D n).k)
      ((D n).ensembleHost hr i) ((D n).ensembleMatchingLaw hr i)
    have hr1 : 1≤r := by omega
    nlinarith
  filter_upwards [hμone,hrange,hξ0,hξone,hdeg,hpart,hent,hconditional,
    hηone,hζone,hlogs,hlogN] with n hmn hsn hxn hxon hdn hpn hen hkn het hzt hln hNn
  exact hfinite (D n) (ξ n) (δ n) hmn hsn.1 hsn.2.1 hxn hxon hdn hpn hen hkn het hzt hln.2 hNn

end LooseHamilton.BiasedRoleInstance
