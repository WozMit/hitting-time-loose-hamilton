module

public import HittingTimeLooseHamilton.BiasedMatchingBalance
public import HittingTimeLooseHamilton.BiasedCloneAverage
public import HittingTimeLooseHamilton.BiasedEntropyEnsemble
public import HittingTimeLooseHamilton.BiasedCloneKahnDegrees

public section

/-! Averaged marginal balance for genuine conditional perfect-matching laws. -/
noncomputable section
open scoped BigOperators
namespace LooseHamilton
open FiniteEntropy Finset

/-- Actual Kahn matching laws, with a common positive vertex count, satisfy the
averaged clone balance including the exact change to a common reference degree. -/
theorem kahn_matching_average_balance {Z : Type*} [Fintype Z] {n r : ℕ}
    (ν : Law Z) (H : Z → Kahn.Hypergraph n r)
    (μ : ∀ z, Law (Kahn.MatchingIn (H z)))
    (hn : 0 < n) (hr : 0 < r) (lam₀ : ℝ) :
    (∑ z, ν.mass z * (∑ e : ↥(H z).edges, |kahnEdgeProbability (μ z) e-1/lam₀|)) ≤
      (2/(r : ℝ))*Real.sqrt (2*(n : ℝ)*
        (∑ z, ν.mass z * (kahnLocalDeficit (μ z)+kahnDegreeDeficit (H z) (kahnMeanDegree (H z))))) +
      ((n : ℝ)/r)*(∑ z, ν.mass z * |kahnMeanDegree (H z)/lam₀-1|) := by
  classical
  let D := fun z => kahnLocalDeficit (μ z)
  let Q := fun z => kahnDegreeDeficit (H z) (kahnMeanDegree (H z))
  let A := fun z => ∑ e : ↥(H z).edges, |kahnEdgeProbability (μ z) e-1/lam₀|
  let t := fun z => |kahnMeanDegree (H z)/lam₀-1|
  have hlocal : ∀ z, (r : ℝ)*A z ≤
      2*Real.sqrt ((n : ℝ)*D z)+2*Real.sqrt ((n : ℝ)*Q z)+(n : ℝ)*t z := by
    intro z
    have hp := kahn_mean_degree_pos (μ z) hn
    have hcard : (r : ℝ)*(Fintype.card ↥(H z).edges : ℝ) =
        (n : ℝ)*kahnMeanDegree (H z) := by
      rw [Fintype.card_coe, ← kahn_incident_card_sum, kahn_incident_mean (H z) hn]
    have href := scaled_reciprocal_reference_l1 (kahnEdgeProbability (μ z))
      (r : ℝ) (n : ℝ) (kahnMeanDegree (H z)) lam₀ (Nat.cast_nonneg _) hp hcard
    have hm := kahn_matching_balance_mean (μ z) hn
    exact href.trans (add_le_add_left hm _)
  have havg := average_clone_balance ν A D Q t (r : ℝ) (n : ℝ) (Nat.cast_nonneg _)
    (fun z => kahn_local_deficit_nonneg (μ z))
    (fun z => kahn_degree_deficit_nonneg (μ z) _
      (kahn_mean_degree_pos (μ z) hn) (kahn_incident_mean (H z) hn)) hlocal
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  calc
    _ ≤ (2*Real.sqrt (2*(n : ℝ)*(∑ z, ν.mass z*(D z+Q z)))+
        (n : ℝ)*(∑ z, ν.mass z*t z))/(r : ℝ) := by
      apply (le_div_iff₀ hrR).mpr
      simpa only [mul_comm (r : ℝ)] using havg
    _ = _ := by dsimp [D,Q,t]; ring

namespace BiasedEnsemble
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers G : SimpleHypergraph V}
variable (hr : 3 ≤ r) (hG : ∀ B∈G,B.card=r)
variable (root : ↥markers) (a : ↥root.val) (p : Law (BiasedCycleState r markers G))

/-- The canonical Kahn mean is the compatible clone-edge count divided by k. -/
theorem host_mean_degree (hk : 0 < ordinaryEdgeCount r markers) (z : Index root a p) :
    kahnMeanDegree (host hr hG root a p z) =
      ((cloneHost G (biasedCloneUniverse root a (reference root a p z))).card : ℝ)/
        ordinaryEdgeCount r markers := by
  unfold kahnMeanDegree host biasedCloneKahnHost
  rw [CloneRelabel.host_card, Nat.cast_mul]
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hk0 : (ordinaryEdgeCount r markers : ℝ) ≠ 0 := by positivity
  field_simp <;> ring

@[expose] def meanLocalDeficit : ℝ :=
  ∑ z, (law root a p).mass z * kahnLocalDeficit (matchingLaw hr hG root a p z)

@[expose] def meanDegreeDeficit : ℝ :=
  ∑ z, (law root a p).mass z *
    kahnDegreeDeficit (host hr hG root a p z) (kahnMeanDegree (host hr hG root a p z))

theorem meanLocalDeficit_nonneg : 0 ≤ meanLocalDeficit hr hG root a p := by
  exact sum_nonneg fun z _ => mul_nonneg ((law root a p).nonneg z)
    (kahn_local_deficit_nonneg (matchingLaw hr hG root a p z))

theorem meanDegreeDeficit_nonneg (hk : 0 < ordinaryEdgeCount r markers) :
    0 ≤ meanDegreeDeficit hr hG root a p := by
  have hn : 0 < r*ordinaryEdgeCount r markers := Nat.mul_pos (by omega) hk
  exact sum_nonneg fun z _ => mul_nonneg ((law root a p).nonneg z)
    (kahn_degree_deficit_nonneg (matchingLaw hr hG root a p z) _
      (kahn_mean_degree_pos (matchingLaw hr hG root a p z) hn)
      (kahn_incident_mean (host hr hG root a p z) hn))

theorem mean_deficits_add :
    meanLocalDeficit hr hG root a p+meanDegreeDeficit hr hG root a p =
      ∑ z, (law root a p).mass z *
        (((r*ordinaryEdgeCount r markers : ℕ) : ℝ)*Real.log (kahnMeanDegree (host hr hG root a p z))-
          Kahn.MatchingLaw.marginalEntropySum (matchingLaw hr hG root a p z)) := by
  unfold meanLocalDeficit meanDegreeDeficit
  rw [← sum_add_distrib]
  simp_rw [← mul_add, kahn_deficits_add]

/-- Averaged clone balance for the exact role-fibre ensemble built from the
original connected-cycle distribution. -/
theorem clone_average_balance (hk : 0 < ordinaryEdgeCount r markers) (lam₀ : ℝ) :
    (∑ z, (law root a p).mass z *
      (∑ e : ↥(host hr hG root a p z).edges,
        |kahnEdgeProbability (matchingLaw hr hG root a p z) e-1/lam₀|)) ≤
      (2/(r : ℝ))*Real.sqrt (2*((r*ordinaryEdgeCount r markers : ℕ) : ℝ)*
        (meanLocalDeficit hr hG root a p+meanDegreeDeficit hr hG root a p)) +
      (ordinaryEdgeCount r markers : ℝ) * (∑ z, (law root a p).mass z *
        |kahnMeanDegree (host hr hG root a p z)/lam₀-1|) := by
  have hrp : 0 < r := by omega
  have hn := Nat.mul_pos hrp hk
  have hb := kahn_matching_average_balance (law root a p) (host hr hG root a p)
    (matchingLaw hr hG root a p) hn hrp lam₀
  have hd : (∑ z, (law root a p).mass z *
      (kahnLocalDeficit (matchingLaw hr hG root a p z)+
        kahnDegreeDeficit (host hr hG root a p z) (kahnMeanDegree (host hr hG root a p z)))) =
      meanLocalDeficit hr hG root a p+meanDegreeDeficit hr hG root a p := by
    simp only [meanLocalDeficit,meanDegreeDeficit,mul_add,sum_add_distrib]
  have hc : ((r*ordinaryEdgeCount r markers : ℕ) : ℝ)/(r : ℝ) = ordinaryEdgeCount r markers := by
    rw [Nat.cast_mul]
    have hr0 : (r : ℝ) ≠ 0 := by positivity
    field_simp
  simpa only [hd,hc] using hb

end BiasedEnsemble
end LooseHamilton
