module

public import HittingTimeLooseHamilton.BiasedEntropyBudgetModels
public import HittingTimeLooseHamilton.BiasedRoleSupportEstimate

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open FiniteEntropy
variable {r : ℕ}

lemma roleSupport_choose_pos (D : BiasedRoleInstance r) (hr : 3≤r)
    (hsk : D.s<D.k) : 0<(D.N-2*D.s).choose (D.k-D.s) := by
  apply Nat.choose_pos
  have hb := D.vertex_bookkeeping hr
  have hr1 : 2≤r-1 := by omega
  have hnk : 2*D.k+D.s≤D.N := by nlinarith
  omega

lemma roleSupport_eq (D : BiasedRoleInstance r) (hr : 3≤r) (hsk : D.s<D.k) :
    D.roleSupport = Real.log ((D.N-2*D.s).choose (D.k-D.s):ℝ)+
      ((D.s:ℝ)-1)*Real.log 2 := by
  have hc : ((D.N-2*D.s).choose (D.k-D.s):ℝ) ≠ 0 := by
    exact_mod_cast (D.roleSupport_choose_pos hr hsk).ne'
  have hs : 1≤D.s := D.s_pos
  unfold roleSupport
  rw [Real.log_mul hc (by positivity), Real.log_pow,
    Nat.cast_sub hs, Nat.cast_one]

lemma roleSupport_coarse (D : BiasedRoleInstance r) (hr : 3≤r) (hsk : D.s<D.k) :
    D.roleSupport ≤ 2*(D.N:ℝ)*Real.log 2 := by
  rw [D.roleSupport_eq hr hsk]
  have hc : 0<((D.N-2*D.s).choose (D.k-D.s):ℝ) := by
    exact_mod_cast D.roleSupport_choose_pos hr hsk
  have hchoose : ((D.N-2*D.s).choose (D.k-D.s):ℝ) ≤ (2:ℝ)^(D.N-2*D.s) := by
    have hb := D.vertex_bookkeeping hr
    have hr1 : 2≤r-1 := by omega
    have hnk : 2*D.k+D.s≤D.N := by nlinarith
    have hp : 0<D.N-2*D.s := by omega
    exact_mod_cast (Nat.choose_le_two_pow (D.N-2*D.s) (D.k-D.s))
  have hlog := Real.log_le_log hc hchoose
  rw [Real.log_pow] at hlog
  have hN : ((D.N-2*D.s:ℕ):ℝ)≤D.N := by exact_mod_cast Nat.sub_le D.N (2*D.s)
  have hs : (D.s:ℝ)≤D.N := by
    have := D.vertex_bookkeeping hr
    exact_mod_cast (by omega : D.s≤D.N)
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

lemma roleSupport_density_cancellation (r : ℕ) (hr : 3≤r) :
    ∃ A : ℝ, 0≤A ∧ ∀ D : BiasedRoleInstance r,
      D.s<D.k → 3*D.s≤D.N →
      |D.roleSupport+(D.k:ℝ)*Real.log ((privateFraction r)^(r-2)*D.μ)-
        (D.k:ℝ)*Real.log (((r:ℝ)-1)*D.μ)| ≤
      A*((D.s:ℝ)+Real.log ((D.N:ℝ)+1)+1) := by
  obtain ⟨A,hA,hbound⟩ := finite_role_support_density_cancellation_nat r hr
  refine ⟨A,hA,?_⟩
  intro D hsk hsN
  rw [D.roleSupport_eq hr hsk]
  exact hbound D.N D.k D.s D.μ (D.vertex_bookkeeping hr) D.s_pos hsk
    (by omega) (D.μ_pos hr)

end LooseHamilton.BiasedRoleInstance
