module

public import HittingTimeLooseHamilton.StoppedCountingPath
public import HittingTimeLooseHamilton.StoppedDeletionHistory
public import HittingTimeLooseHamilton.KahnEntropy

public section
noncomputable section
namespace LooseHamilton.StoppedCounting
open Finset StoppedDeletion
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma state_history {σ τ : FiniteOrder A} {t u : ℕ} (hu : u ≤ t)
    (h : History (Fintype.card A-t) σ = History (Fintype.card A-t) τ) :
    state σ u = state τ u :=
  history_prefix_eq (history_mono (Nat.sub_le_sub_left hu _) h)

lemma active_history (C : Finset (Finset A)) (C0 : ℝ) (k M : ℕ)
    {σ τ : FiniteOrder A} {t : ℕ}
    (h : History (Fintype.card A-t) σ = History (Fintype.card A-t) τ) :
    Active C C0 k M σ t ↔ Active C C0 k M τ t := by
  have hg (u : ℕ) (hu : u ≤ t) : Good C C0 k σ u ↔ Good C C0 k τ u := by
    simp only [Good,state_history hu h]
  constructor
  · rintro ⟨ht,hh⟩; exact ⟨ht,fun u hu => (hg u hu).mp (hh u hu)⟩
  · rintro ⟨ht,hh⟩; exact ⟨ht,fun u hu => (hg u hu).mpr (hh u hu)⟩

lemma boundary_history {σ τ : FiniteOrder A} {t u : ℕ} (hu : u < t)
    (huK : u < Fintype.card A)
    (h : History (Fintype.card A-t) σ = History (Fintype.card A-t) τ) :
    orderBoundary σ (Fintype.card A-u) (Nat.sub_le _ _) (by omega) =
    orderBoundary τ (Fintype.card A-u) (Nat.sub_le _ _) (by omega) := by
  let a := orderBoundary σ (Fintype.card A-u) (Nat.sub_le _ _) (by omega)
  have hr : (σ a).val = Fintype.card A-u-1 := by simp [a,orderBoundary]
  have he := history_rank_eq h a (by omega)
  apply τ.injective
  rw [← he]
  simp [a,orderBoundary]

lemma increment_history (C : Finset (Finset A)) (C0 : ℝ) (k M : ℕ)
    {σ τ : FiniteOrder A} {t u : ℕ} (hu : u < t)
    (h : History (Fintype.card A-t) σ = History (Fintype.card A-t) τ) :
    increment C C0 k M σ u = increment C C0 k M τ u := by
  have ha := active_history C C0 k M (t := u) (history_mono (Nat.sub_le_sub_left hu.le _) h)
  have hs := state_history hu.le h
  have hl : loss C σ u = loss C τ u := by
    unfold loss
    split_ifs with huK
    · rw [hs,boundary_history hu huK h]
    · rfl
  simp only [increment,hl]
  split_ifs <;> tauto

lemma mean_le_cap {C : Finset (Finset A)} {C0 : ℝ} {k t : ℕ}
    (hC : UniformFamily C k) {σ : FiniteOrder A} (hg : Good C C0 k σ t)
    (ht : t < Fintype.card A) :
    (k : ℝ) / (Fintype.card A-t : ℕ) ≤ cap A C0 k t := by
  have hs := sum_marginal C (state σ t) k hC hg.1
  have hc : (state σ t).card = Fintype.card A-t := orderPrefix_card σ _ (Nat.sub_le _ _)
  have hb : (k : ℝ) ≤ (Fintype.card A-t : ℕ) * cap A C0 k t := by
    rw [← hs]
    calc
      _ ≤ ∑ e ∈ state σ t, cap A C0 k t := sum_le_sum (fun e he => hg.2 e he)
      _ = _ := by simp [hc]
  exact (div_le_iff₀ (by exact_mod_cast (show 0<Fintype.card A-t by omega))).mpr
    (by simpa only [mul_comm] using hb)

lemma increment_abs_le {C : Finset (Finset A)} {C0 : ℝ} {k M : ℕ}
    (hC : UniformFamily C k) (hC0 : 0 ≤ C0) (σ : FiniteOrder A) (t : ℕ) :
    |increment C C0 k M σ t| ≤ cap A C0 k t := by
  classical
  unfold increment
  split_ifs with ha
  · have ht : t < Fintype.card A := lt_of_lt_of_le ha.1 (Nat.sub_le _ _)
    have hg := ha.2 t le_rfl
    have hm := mean_le_cap hC hg ht
    have hl := loss_le_cap hg ht
    have hn := loss_nonneg C σ t
    have hk : 0 ≤ (k : ℝ)/(Fintype.card A-t : ℕ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · simp only [abs_zero]
    exact div_nonneg (mul_nonneg hC0 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

lemma increment_centering (C : Finset (Finset A)) (C0 : ℝ) (k M t : ℕ)
    (hC : UniformFamily C k) (W : FiniteOrder A → ℝ)
    (hW : ∀ σ τ, History (Fintype.card A-t) σ = History (Fintype.card A-t) τ → W σ = W τ) :
    ∑ σ : FiniteOrder A, W σ * increment C C0 k M σ t = 0 := by
  classical
  by_cases ht : t < Fintype.card A
  · let V : FiniteOrder A → ℝ := fun σ => if Active C C0 k M σ t then W σ else 0
    let q : Finset A → A → ℝ := fun S a => marginal C S a - k/(Fintype.card A-t : ℕ)
    have hv : ∀ σ τ, History (Fintype.card A-t) σ = History (Fintype.card A-t) τ → V σ = V τ := by
      intro σ τ h
      simp only [V,active_history C C0 k M h,hW σ τ h]
    have hq (σ : FiniteOrder A) (hv : V σ ≠ 0) :
        ∑ a ∈ orderPrefix σ (Fintype.card A-t), q (orderPrefix σ (Fintype.card A-t)) a = 0 := by
      have ha : Active C C0 k M σ t := by by_contra hn; simp [V,hn] at hv
      have hs := sum_marginal C (state σ t) k hC (ha.2 t le_rfl).1
      have hj : ((Fintype.card A-t : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (show 0<Fintype.card A-t by omega))
      simp only [q,sum_sub_distrib,sum_const,nsmul_eq_mul,orderPrefix_card σ _ (Nat.sub_le _ _)]
      change (∑ a ∈ state σ t, marginal C (state σ t) a) - _ = 0
      rw [hs,mul_div_cancel₀ _ hj,sub_self]
    have hh := weighted_centering_of (Fintype.card A-t) (Nat.sub_le _ _) (by omega) V q hv hq
    convert hh using 1
    apply sum_congr rfl
    intro σ hσ
    simp only [increment,V,q,state,loss,dif_pos ht]
    split_ifs <;> simp
  · apply sum_eq_zero
    intro σ hσ
    have hn : ¬ Active C C0 k M σ t := fun ha => ht (lt_of_lt_of_le ha.1 (Nat.sub_le _ _))
    simp [increment,hn]

lemma uniform_increment_centering (C : Finset (Finset A)) (C0 : ℝ) (k M t : ℕ)
    (hC : UniformFamily C k) (W : FiniteOrder A → ℝ)
    (hW : ∀ σ τ, History (Fintype.card A-t) σ = History (Fintype.card A-t) τ → W σ = W τ) :
    letI : Nonempty (FiniteOrder A) := ⟨Fintype.equivFin A⟩
    ∑ σ : FiniteOrder A, (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteOrder A)).mass σ *
      W σ * increment C C0 k M σ t = 0 := by
  dsimp only [FiniteEntropy.uniform]
  simp_rw [mul_assoc]
  rw [← mul_sum,increment_centering C C0 k M t hC W hW,mul_zero]

end LooseHamilton.StoppedCounting
