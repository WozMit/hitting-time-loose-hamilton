module

public import HittingTimeLooseHamilton.BiasedRoleMain

public section

/-! Finite counting form of the exceptional directed-role bound. -/
noncomputable section
namespace LooseHamilton
open Finset
attribute [local instance] Classical.propDecidable
namespace BiasedRoleInstance
variable {r : ℕ}

@[expose] def eligibleEdges (D : BiasedRoleInstance r) :=
  D.host.filter (fun e => Disjoint e (originalPorts D.markers))

@[expose] def roleReference (D : BiasedRoleInstance r) : ℝ := 1/(((r:ℝ)-1)^2*D.μ)

@[expose] def roleProbability (D : BiasedRoleInstance r) (e : Finset (Fin D.N))
    (uv : Fin D.N × Fin D.N) : ℝ :=
  directedRoleProbability r D.markers D.host D.root D.initial D.cycleLaw e uv.1 uv.2

@[expose] def exceptionalRoles (D : BiasedRoleInstance r) (t : ℝ) : ℕ :=
  ∑ e ∈ D.eligibleEdges,
    (e.offDiag.filter (fun uv => t*D.roleReference < |D.roleProbability e uv-D.roleReference|)).card

@[expose] def eligibleRoles (D : BiasedRoleInstance r) : ℕ :=
  ∑ e ∈ D.eligibleEdges, e.offDiag.card

@[expose] def exceptionalProportion (D : BiasedRoleInstance r) (t : ℝ) : ℝ :=
  (D.exceptionalRoles t:ℝ)/D.eligibleRoles

lemma roleReference_pos (D : BiasedRoleInstance r) (hr : 3≤r) :
    0<D.roleReference := by
  unfold roleReference
  have h := D.μ_pos hr
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hr1 : (0:ℝ)<(r:ℝ)-1 := by linarith
  positivity

lemma exceptional_role_iff_relative (D : BiasedRoleInstance r) (hr : 3≤r)
    (t : ℝ) (e : Finset (Fin D.N)) (uv : Fin D.N × Fin D.N) :
    t*D.roleReference < |D.roleProbability e uv-D.roleReference| ↔
      t < |D.roleProbability e uv/D.roleReference-1| := by
  have hp := D.roleReference_pos hr
  rw [show D.roleProbability e uv/D.roleReference-1 =
    (D.roleProbability e uv-D.roleReference)/D.roleReference by
      rw [sub_div, div_self hp.ne']]
  rw [abs_div, abs_of_pos hp]
  exact (lt_div_iff₀ hp).symm

lemma eligibleRoles_eq (D : BiasedRoleInstance r) :
    D.eligibleRoles=D.eligibleEdges.card*(r*(r-1)) := by
  unfold eligibleRoles
  calc
    _ = ∑ e ∈ D.eligibleEdges, r*(r-1) := by
      apply sum_congr rfl
      intro e he
      exact directedRole_card ((mem_completeEdges _ _).mp (D.host_uniform (mem_filter.mp he).1))
    _ = _ := by simp

lemma exceptionalRoles_bound (D : BiasedRoleInstance r) (t : ℝ) :
    (D.exceptionalRoles t:ℝ)*(t*D.roleReference) ≤ D.deviation := by
  unfold exceptionalRoles deviation biasedRoleDeviation
  push_cast
  rw [sum_mul]
  apply sum_le_sum
  intro e he
  let bad := e.offDiag.filter
    (fun uv => t*D.roleReference < |D.roleProbability e uv-D.roleReference|)
  calc
    _ = ∑ uv ∈ bad, t*D.roleReference := by simp [bad]
    _ ≤ ∑ uv ∈ bad, |D.roleProbability e uv-D.roleReference| := by
      apply sum_le_sum
      intro uv huv
      exact (mem_filter.mp huv).2.le
    _ ≤ ∑ uv ∈ e.offDiag, |D.roleProbability e uv-D.roleReference| :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
    _ = _ := rfl

/-- Finite Markov bound with the actual number of existing eligible roles. -/
lemma exceptionalProportion_bound (D : BiasedRoleInstance r) (hr : 3≤r)
    {t : ℝ} (ht : 0<t) (hroles : 0<D.eligibleRoles) :
    D.exceptionalProportion t ≤ D.deviation /
      ((D.eligibleRoles:ℝ)*t*D.roleReference) := by
  have href := D.roleReference_pos hr
  have hq : (0:ℝ)<D.eligibleRoles := Nat.cast_pos.mpr hroles
  apply (le_div_iff₀ (by positivity)).mpr
  unfold exceptionalProportion
  have h := D.exceptionalRoles_bound t
  calc
    _ = (D.exceptionalRoles t:ℝ)*(t*D.roleReference) := by field_simp <;> ring
    _ ≤ _ := h
end BiasedRoleInstance
end LooseHamilton
