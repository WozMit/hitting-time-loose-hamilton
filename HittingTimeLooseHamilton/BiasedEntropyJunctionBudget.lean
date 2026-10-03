module

public import HittingTimeLooseHamilton.BiasedEntropyBudgetModels
public import HittingTimeLooseHamilton.BiasedRoleReference
public import HittingTimeLooseHamilton.BiasedRoleJunctions
public import HittingTimeLooseHamilton.BiasedRoleSupportEstimate

public section

open scoped BigOperators
noncomputable section
namespace LooseHamilton
open FiniteEntropy Finset

/-- The Bernoulli reference costs only a marker and logarithmic counting error
relative to the fixed-weight ordinary-junction support. -/
theorem fixed_weight_junction_budget (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N k s : ℕ,
      N = (r-1)*k+s → 1 ≤ s → s < k → s ≤ N-2*s →
      -((k-s : ℕ) : ℝ)*Real.log (1/((r : ℝ)-1)) -
        (((N-2*s : ℕ) : ℝ)-(k-s : ℕ))*Real.log (1-1/((r : ℝ)-1)) -
        Real.log ((N-2*s).choose (k-s) : ℝ) ≤
        C*((s : ℝ)+Real.log ((N : ℝ)+1)+1) := by
  obtain ⟨C₀,hC₀,hweight⟩ := fixed_weight_cross_entropy_bound
  let C := ((r : ℝ)-2)+3+C₀
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro N k s hbook hs hsk hsL
  have h2s : 2*s ≤ N := by
    have hr1 : 2 ≤ r-1 := by omega
    nlinarith
  have hLcast : ((N-2*s : ℕ) : ℝ) = (N : ℝ)-2*s := by
    rw [Nat.cast_sub h2s]
    push_cast
    ring
  have hbookR := congrArg (fun n : ℕ => (n : ℝ)) hbook
  push_cast [Nat.cast_sub (show 1 ≤ r by omega)] at hbookR
  have hjrel : ((k-s : ℕ) : ℝ) = (k : ℝ)-s := Nat.cast_sub hsk.le
  have hLrel : ((N-2*s : ℕ) : ℝ) = ((r : ℝ)-1)*k-s := by
    rw [Nat.cast_sub h2s]
    push_cast
    linarith
  have hj : 0 < k-s := Nat.sub_pos_of_lt hsk
  have hjL : k-s < N-2*s := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hh : ((k-s : ℕ) : ℝ) < (N-2*s : ℕ) := by rw [hjrel,hLrel]; nlinarith
    exact_mod_cast hh
  have hLpos : (0 : ℝ) < (N-2*s : ℕ) := by exact_mod_cast (lt_trans hj hjL)
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsLR : (s : ℝ) ≤ (N-2*s : ℕ) := by exact_mod_cast hsL
  have hr1 : (0 : ℝ) < (r : ℝ)-1 := by linarith
  have hr2 : (0 : ℝ) ≤ (r : ℝ)-2 := by linarith
  have ha : (0 : ℝ) < 1/((r : ℝ)-1) := by positivity
  have ha1 : 1/((r : ℝ)-1) < 1 := (div_lt_one hr1).2 (by linarith)
  have hw := hweight (N-2*s) (k-s) hj hjL _ ha ha1
  have hquad : ((N-2*s : ℕ) : ℝ) *
      ((((k-s : ℕ) : ℝ)/(N-2*s : ℕ)-1/((r : ℝ)-1))^2 /
        ((1/((r : ℝ)-1))*(1-1/((r : ℝ)-1)))) =
      ((r : ℝ)-2)*(s : ℝ)^2/(N-2*s : ℕ) := by
    have h := role_weight_quadratic_identity (r := (r : ℝ))
      (N := (N : ℝ)) (k := (k : ℝ)) (s := (s : ℝ)) (by linarith)
      (by rw [← hLcast]; exact hLpos) hbookR
    rw [← hjrel, ← hLcast] at h
    exact h
  rw [hquad] at hw
  have hqle : ((r : ℝ)-2)*(s : ℝ)^2/(N-2*s : ℕ) ≤ ((r : ℝ)-2)*s := by
    apply (div_le_iff₀ hLpos).2
    nlinarith [mul_le_mul_of_nonneg_left hsLR (by linarith : (0 : ℝ) ≤ s)]
  have hlogN : 0 ≤ Real.log ((N : ℝ)+1) := Real.log_nonneg (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  have hlog : Real.log ((N-2*s : ℕ)+(1 : ℝ)) ≤ Real.log ((N : ℝ)+1) := by
    apply Real.log_le_log (by positivity)
    have hh : ((N-2*s : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N (2*s)
    linarith
  have hsB : (s : ℝ) ≤ s+Real.log ((N : ℝ)+1)+1 := by linarith
  have hlB : Real.log ((N : ℝ)+1) ≤ (s : ℝ)+Real.log ((N : ℝ)+1)+1 := by linarith
  have h1B : 1 ≤ (s : ℝ)+Real.log ((N : ℝ)+1)+1 := by linarith
  calc
    _ ≤ ((r : ℝ)-2)*s+3*Real.log ((N : ℝ)+1)+C₀ := by linarith only [hw,hqle,hlog]
    _ ≤ C*((s : ℝ)+Real.log ((N : ℝ)+1)+1) := by
      dsimp [C]
      nlinarith only [mul_le_mul_of_nonneg_left hsB hr2,
        mul_le_mul_of_nonneg_left h1B hC₀,hlB]

/-- Actual Bernoulli deficit of junction indicators, controlled by the complete
role entropy deficit and a fixed-uniformity marker/counting error. -/
theorem connected_junction_deficit_budget (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (markers : SimpleHypergraph V) ( _hM : IsPairMatching markers)
      (root : ↥markers) (a : ↥root.val) (p : Law (ConnectedCloneCycle r markers))
      (hb0 : 0 ≤ 1/((r : ℝ)-1)) (hb1 : 1/((r : ℝ)-1) ≤ 1),
      Fintype.card V = (r-1)*ordinaryEdgeCount r markers+markers.card →
      1 ≤ markers.card → markers.card < ordinaryEdgeCount r markers →
      markers.card ≤ Fintype.card V-2*markers.card →
      coordinateDeficit p (ConnectedCloneCycle.junctionBits root a)
        (coordinateCrossEntropy p (ConnectedCloneCycle.junctionBits root a)
          (fun _ => bernoulliBitLaw (1/((r : ℝ)-1)) hb0 hb1)) univ ≤
        (Real.log (((Fintype.card V-2*markers.card).choose
            (ordinaryEdgeCount r markers-markers.card) : ℝ)*2^(markers.card-1)) -
          entropy (p.map (ConnectedCloneCycle.role root a)).mass) +
        C*((markers.card : ℝ)+Real.log ((Fintype.card V : ℝ)+1)+1) := by
  obtain ⟨C,hC,hbudget⟩ := fixed_weight_junction_budget r hr
  refine ⟨C,hC,?_⟩
  intro V _ _ markers hM root a p hb0 hb1 hbook hs hsk hsL
  have hcross := hbudget _ _ _ hbook hs hsk hsL
  let N := Fintype.card V
  let k := ordinaryEdgeCount r markers
  let s := markers.card
  have hjL : k-s ≤ N-2*s := by
    have hr1 : 2 ≤ r-1 := by omega
    change N = (r-1)*k+s at hbook
    change s < k at hsk
    have hmul := Nat.mul_le_mul_right k hr1
    omega
  have hchoose : (((N-2*s).choose (k-s) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hjL).ne'
  have hsupp : Real.log (((N-2*s).choose (k-s) : ℝ)*2^(s-1)) =
      Real.log ((N-2*s).choose (k-s) : ℝ) + ((s-1 : ℕ) : ℝ)*Real.log 2 := by
    rw [Real.log_mul hchoose (by positivity), Real.log_pow]
  have hmain := ConnectedCloneCycle.junctionBits_deficit_le_role_deficit hr hM
    root a p (1/((r : ℝ)-1)) hb0 hb1
    (Real.log (((N-2*s).choose (k-s) : ℝ)*2^(s-1)))
  change coordinateDeficit _ _ _ _ ≤ _ at hmain
  change -((k-s : ℕ) : ℝ)*_ - (((N-2*s : ℕ) : ℝ)-(k-s : ℕ))*_ - _ ≤ _ at hcross
  change _ ≤ (_-entropy _)+C*((s : ℝ)+Real.log ((N : ℝ)+1)+1)
  change _ ≤ (_-entropy _)+(-(((k-s : ℕ) : ℝ)*_+
    (((N-2*s)-(k-s) : ℕ) : ℝ)*_)+((s-1 : ℕ) : ℝ)*_ - _) at hmain
  rw [Nat.cast_sub hjL, hsupp] at hmain
  rw [hsupp]
  linarith

/-- The junction budget for the actual cycle law of a Theorem 6.1 instance. -/
theorem instance_junction_deficit_budget (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : BiasedRoleInstance r)
      (hb0 : 0 ≤ 1/((r : ℝ)-1)) (hb1 : 1/((r : ℝ)-1) ≤ 1),
      D.s < D.k → D.s ≤ D.N-2*D.s →
      coordinateDeficit (D.cycleLaw.map biasedConnectedCycle)
        (ConnectedCloneCycle.junctionBits D.root D.initial)
        (coordinateCrossEntropy (D.cycleLaw.map biasedConnectedCycle)
          (ConnectedCloneCycle.junctionBits D.root D.initial)
          (fun _ => bernoulliBitLaw (1/((r : ℝ)-1)) hb0 hb1)) univ ≤
        D.roleDeficit + C*((D.s : ℝ)+Real.log ((D.N : ℝ)+1)+1) := by
  obtain ⟨C,hC,hbudget⟩ := connected_junction_deficit_budget r hr
  refine ⟨C,hC,?_⟩
  intro D hb0 hb1 hsk hsL
  have h := hbudget (Fin D.N) D.markers D.marked_matching D.root D.initial
    (D.cycleLaw.map biasedConnectedCycle) hb0 hb1
    (by simpa only [Fintype.card_fin, BiasedRoleInstance.k, BiasedRoleInstance.s] using D.vertex_bookkeeping hr)
    D.s_pos hsk (by simpa only [Fintype.card_fin, BiasedRoleInstance.s] using hsL)
  simp only [Fintype.card_fin, Law.map_map] at h
  change _ ≤ D.roleDeficit + C*((D.s : ℝ)+Real.log ((D.N : ℝ)+1)+1) at h
  exact h

namespace BiasedRoleInstance

/-- Bernoulli relative-entropy deficit of actual ordinary junction indicators. -/
@[expose] def junctionDeficit {r : ℕ} (D : BiasedRoleInstance r) (hr : 3 ≤ r) : ℝ :=
  coordinateDeficit (D.cycleLaw.map biasedConnectedCycle)
    (ConnectedCloneCycle.junctionBits D.root D.initial)
    (coordinateCrossEntropy (D.cycleLaw.map biasedConnectedCycle)
      (ConnectedCloneCycle.junctionBits D.root D.initial)
      (fun _ => bernoulliBitLaw (junctionFraction r)
        (junctionFraction_pos_lt_one r hr).1.le
        (junctionFraction_pos_lt_one r hr).2.le)) univ

lemma junctionDeficit_nonneg {r : ℕ} (D : BiasedRoleInstance r) (hr : 3 ≤ r) :
    0 ≤ D.junctionDeficit hr := by
  let p := D.cycleLaw.map biasedConnectedCycle
  let X := ConnectedCloneCycle.junctionBits (r:=r) D.root D.initial
  let q := fun _ : NonPortVertex D.markers => bernoulliBitLaw (junctionFraction r)
    (junctionFraction_pos_lt_one r hr).1.le (junctionFraction_pos_lt_one r hr).2.le
  have hq : ∀ v b, 0 < (q v).mass b := by
    intro v b
    exact bernoulliBitLaw_pos (junctionFraction_pos_lt_one r hr).1
      (junctionFraction_pos_lt_one r hr).2 b
  have h := coordinateDeficit_mono p X (coordinateCrossEntropy p X q)
    (coordinateEntropy_singleton_le_crossEntropy p X q hq) (Finset.empty_subset univ)
  rw [coordinateDeficit_empty] at h
  exact h

/-- Uniform-in-instance bound; the constant depends only on r. -/
theorem junctionDeficit_budget (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : BiasedRoleInstance r,
      D.s < D.k → D.s ≤ D.N-2*D.s →
      D.junctionDeficit hr ≤ D.roleDeficit +
        C*((D.s : ℝ)+Real.log ((D.N : ℝ)+1)+1) := by
  obtain ⟨C,hC,hbudget⟩ := instance_junction_deficit_budget r hr
  refine ⟨C,hC,?_⟩
  intro D hsk hsL
  exact hbudget D (junctionFraction_pos_lt_one r hr).1.le
    (junctionFraction_pos_lt_one r hr).2.le hsk hsL

end BiasedRoleInstance
end LooseHamilton
