module

public import HittingTimeLooseHamilton.StoppedCountingFamily
public import HittingTimeLooseHamilton.UniformOrderCounting
public import HittingTimeLooseHamilton.HarmonicDeletion

public section
noncomputable section
open scoped BigOperators
namespace LooseHamilton.StoppedCounting
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]
@[expose] def state (σ : FiniteOrder A) (t : ℕ) : Finset A := orderPrefix σ (Fintype.card A-t)
@[expose] def Good (C : Finset (Finset A)) (C0 : ℝ) (k : ℕ) (σ : FiniteOrder A) (t : ℕ) : Prop :=
  0 < familyCount C (state σ t) ∧ ∀ e ∈ state σ t,
    marginal C (state σ t) e ≤ C0 * k / (Fintype.card A-t : ℕ)
@[expose] def Reached (C : Finset (Finset A)) (C0 : ℝ) (k M : ℕ) (σ : FiniteOrder A) (t : ℕ) : Prop :=
  t ≤ Fintype.card A-M ∧ ∀ u < t, Good C C0 k σ u
@[expose] def Active (C : Finset (Finset A)) (C0 : ℝ) (k M : ℕ) (σ : FiniteOrder A) (t : ℕ) : Prop :=
  t < Fintype.card A-M ∧ ∀ u ≤ t, Good C C0 k σ u
@[expose] def loss (C : Finset (Finset A)) (σ : FiniteOrder A) (t : ℕ) : ℝ :=
  if ht : t < Fintype.card A then
    marginal C (state σ t) (orderBoundary σ (Fintype.card A-t) (Nat.sub_le _ _) (by omega))
  else 0
@[expose] def increment (C : Finset (Finset A)) (C0 : ℝ) (k M : ℕ) (σ : FiniteOrder A) (t : ℕ) : ℝ := by
  classical
  exact if Active C C0 k M σ t then loss C σ t - k / (Fintype.card A-t : ℕ) else 0
@[expose] def cap (A : Type*) [Fintype A] (C0 : ℝ) (k t : ℕ) : ℝ := C0 * k / (Fintype.card A-t : ℕ)
@[simp] theorem state_zero (σ : FiniteOrder A) : state σ 0 = univ := by
  ext a; simp [state, (σ a).isLt]
theorem state_step (σ : FiniteOrder A) (t : ℕ) (ht : t < Fintype.card A) :
    state σ (t+1) = (state σ t).erase
      (orderBoundary σ (Fintype.card A-t) (Nat.sub_le _ _) (by omega)) := by
  ext a
  simp only [state, mem_orderPrefix, mem_erase, orderBoundary]
  have he : a = σ.symm ⟨Fintype.card A-t-1, by omega⟩ ↔
      (σ a).val = Fintype.card A-t-1 := by
    rw [Equiv.eq_symm_apply]; exact Fin.ext_iff
  simp only [ne_eq, he]
  omega
theorem boundary_mem_state (σ : FiniteOrder A) (t : ℕ) (ht : t < Fintype.card A) :
    orderBoundary σ (Fintype.card A-t) (Nat.sub_le _ _) (by omega) ∈ state σ t := by
  simp only [state, mem_orderPrefix, orderBoundary, Equiv.apply_symm_apply]
  omega
theorem reached_active_before {C : Finset (Finset A)} {C0 : ℝ} {k M t : ℕ}
    {σ : FiniteOrder A} (ht : Reached C C0 k M σ t) {u : ℕ} (hu : u < t) :
    Active C C0 k M σ u :=
  ⟨by have := ht.1; omega, fun v hv => ht.2 v (by omega)⟩
theorem loss_nonneg (C : Finset (Finset A)) (σ : FiniteOrder A) (t : ℕ) :
    0 ≤ loss C σ t := by
  unfold loss; split_ifs; exact marginal_nonneg _ _ _; rfl
theorem loss_le_cap {C : Finset (Finset A)} {C0 : ℝ} {k t : ℕ} {σ : FiniteOrder A}
    (hg : Good C C0 k σ t) (ht : t < Fintype.card A) :
    loss C σ t ≤ cap A C0 k t := by
  rw [loss, dif_pos ht]
  exact hg.2 _ (boundary_mem_state σ t ht)
theorem cap_le_half {C0 : ℝ} {k M t : ℕ} (hM : 0<M) (hC0 : 0≤C0)
    (hsmall : C0*k/M ≤ (1/2:ℝ)) (ht : t ≤ Fintype.card A-M)
    (hMK : M≤Fintype.card A) : cap A C0 k t ≤ 1/2 := by
  apply le_trans _ hsmall
  exact div_le_div_of_nonneg_left (mul_nonneg hC0 (Nat.cast_nonneg _))
    (Nat.cast_pos.mpr hM) (by exact_mod_cast (show M≤Fintype.card A-t by omega))
theorem log_state_step {C : Finset (Finset A)} {C0 : ℝ} {k M t : ℕ} {σ : FiniteOrder A}
    (hM : 0<M) (hMK : M≤Fintype.card A) (hC0 : 0≤C0)
    (hsmall : C0*k/M ≤ (1/2:ℝ)) (hg : Good C C0 k σ t)
    (ht : t < Fintype.card A-M) :
    Real.log (familyCount C (state σ (t+1))) =
      Real.log (familyCount C (state σ t)) + Real.log (1-loss C σ t) := by
  have htK : t<Fintype.card A := by omega
  rw [state_step σ t htK]
  have hl := (loss_le_cap hg htK).trans (cap_le_half hM hC0 hsmall ht.le hMK)
  rw [loss, dif_pos htK] at hl ⊢
  exact log_count_erase _ _ _ hg.1 (by linarith)
theorem reached_count_pos {C : Finset (Finset A)} {C0 : ℝ} {k M t : ℕ} {σ : FiniteOrder A}
    (hC : C.Nonempty) (hM : 0<M) (hMK : M≤Fintype.card A) (hC0 : 0≤C0)
    (hsmall : C0*k/M ≤ (1/2:ℝ)) (ht : Reached C C0 k M σ t) :
    0 < familyCount C (state σ t) := by
  cases t with
  | zero => simpa [familyCount, survivingFamily, FiniteFamily.count] using hC.card_pos
  | succ t =>
    have htK : t<Fintype.card A := by have := ht.1; omega
    have hg := ht.2 t (by omega)
    have hl := (loss_le_cap hg htK).trans
      (cap_le_half hM hC0 hsmall (by have := ht.1; omega) hMK)
    rw [loss, dif_pos htK] at hl
    rw [state_step σ t htK]
    exact count_erase_pos_of_marginal_lt_one _ _ _ hg.1 (by linarith)

theorem log_state_telescope {C : Finset (Finset A)} {C0 : ℝ} {k M t : ℕ} {σ : FiniteOrder A}
    (hM : 0<M) (hMK : M≤Fintype.card A) (hC0 : 0≤C0)
    (hsmall : C0*k/M ≤ (1/2:ℝ)) (ht : Reached C C0 k M σ t) :
    Real.log (familyCount C (state σ t)) = Real.log (familyCount C univ) +
      ∑ u ∈ range t, Real.log (1-loss C σ u) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hprev : Reached C C0 k M σ t := ⟨by have := ht.1; omega,
      fun u hu => ht.2 u (by omega)⟩
    rw [log_state_step hM hMK hC0 hsmall (ht.2 t (by omega)) (by have := ht.1; omega),
      ih hprev, sum_range_succ]
    ring
end LooseHamilton.StoppedCounting
