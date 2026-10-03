module

public import HittingTimeLooseHamilton.EntropyExceptionalRoles
public import HittingTimeLooseHamilton.EntropyEligibleCount

public section

noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open Finset
variable {r : ℕ}

lemma eligible_reference_mass (D : BiasedRoleInstance r) (hr : 3≤r)
    (hh : (D.host.card:ℝ)/2≤D.eligibleEdges.card) :
    (D.N:ℝ)/(2*((r:ℝ)-1))≤(D.eligibleRoles:ℝ)*D.roleReference := by
  have hμ := D.μ_pos hr
  have hN : (0:ℝ)<D.N := Nat.cast_pos.mpr D.N_pos
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hr1 : (0:ℝ)<(r:ℝ)-1 := by linarith
  have hr0 : (0:ℝ)<r := by linarith
  have hm : (r:ℝ)*(D.host.card:ℝ)=D.μ*D.N := by
    unfold μ meanDegree
    simp only [Fintype.card_fin]
    field_simp
  rw [D.eligibleRoles_eq]
  push_cast
  rw [Nat.cast_sub (by omega : 1≤r),Nat.cast_one]
  unfold roleReference
  have hmul := mul_le_mul_of_nonneg_right hh
    (show 0≤(r:ℝ)*((r:ℝ)-1)/( ((r:ℝ)-1)^2*D.μ) by positivity)
  have he : (D.host.card:ℝ)/2*((r:ℝ)*((r:ℝ)-1)/(((r:ℝ)-1)^2*D.μ))=
      (D.N:ℝ)/(2*((r:ℝ)-1)) := by
    field_simp [hμ.ne', show (r:ℝ)-1≠0 by linarith]
    nlinarith [congrArg (fun x : ℝ => x*((r:ℝ)-1)) hm]
  rw [he] at hmul
  convert hmul using 1; ring

lemma exceptionalProportion_rate (D : BiasedRoleInstance r) (hr : 3≤r)
    {K q t : ℝ} (hK : 0≤K) (hq : 0<q) (ht : 0<t)
    (hh : (D.host.card:ℝ)/2≤D.eligibleEdges.card)
    (hd : D.deviation≤K*D.N/q) :
    D.exceptionalProportion t≤(2*((r:ℝ)-1)*K)/(t*q) := by
  have hm := D.eligible_reference_mass hr hh
  have hN : (0:ℝ)<D.N := Nat.cast_pos.mpr D.N_pos
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hr1 : (0:ℝ)<(r:ℝ)-1 := by linarith
  have hr0 : (0:ℝ)<r := by linarith
  have hmass : 0<(D.eligibleRoles:ℝ)*D.roleReference :=
    lt_of_lt_of_le (by positivity) hm
  have hroles : 0<D.eligibleRoles := by
    by_contra h
    have hz : D.eligibleRoles=0 := by omega
    simp [hz] at hmass
  have hp := D.exceptionalProportion_bound hr ht hroles
  have hden : (D.N:ℝ)*t/(2*((r:ℝ)-1))≤(D.eligibleRoles:ℝ)*t*D.roleReference := by
    convert mul_le_mul_of_nonneg_right hm ht.le using 1 <;> ring
  calc
    _ ≤ D.deviation/((D.eligibleRoles:ℝ)*t*D.roleReference) := hp
    _ ≤ (K*D.N/q)/((D.eligibleRoles:ℝ)*t*D.roleReference) :=
      div_le_div_of_nonneg_right hd (by
        convert mul_nonneg hmass.le ht.le using 1; ring)
    _ ≤ (K*D.N/q)/((D.N:ℝ)*t/(2*((r:ℝ)-1))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by field_simp <;> ring
end LooseHamilton.BiasedRoleInstance
