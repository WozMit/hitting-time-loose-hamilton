module

public import HittingTimeLooseHamilton.BootstrapBaseMeanBounds
public import HittingTimeLooseHamilton.BootstrapActualDeletionBounds

public section

/-! The source means used by the actual tests satisfy the ambient comparison.
Block-size assumptions are static geometry; no observation-dependent gate is added.
-/
noncomputable section
namespace LooseHamilton.BootstrapMeans
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual private-source mean on a residual base. -/
theorem private_mean_bounds {r : ℕ} (hr : 3 ≤ r) {M : Finset (Finset V)}
    (b : BootstrapBases.Base M) (H : SimpleHypergraph V)
    (S : Finset ↥(BootstrapBases.active b)) (x : ↥(BootstrapBases.active b))
    (hS : S.card = r-3) (hN : 8*r ≤ Fintype.card V) :
    privateRootSourceMean r (inducedHost (BootstrapBases.active b) H) S x ≤
      (r : ℝ)*H.card/(univ \ insert x S).card ∧
    (r : ℝ)*H.card/(univ \ insert x S).card ≤ 2*meanDegree (V := V) r H.card := by
  have hdel : (BootstrapBases.deleted b).card + (univ \ (univ \ insert x S)).card ≤ 4*r := by
    rw [show univ \ (univ \ insert x S) = insert x S by ext v; simp]
    have := card_insert_le x S
    have := BootstrapBases.deleted_card_le b
    omega
  have hb := base_mean_bounds b r (4*r) H (univ \ insert x S) (by omega) (by omega) hdel
  simpa only [inducedMean, meanDegree, Fintype.card_coe, privateRootSourceMean] using hb

/-- The actual endpoint mean, for either complete cut-label type. -/
theorem endpoint_mean_bounds {r : ℕ} (hr : 3 ≤ r) {M : Finset (Finset V)}
    (b : BootstrapBases.Base M) (H : SimpleHypergraph V)
    (P : Finset ↥(BootstrapBases.active b)) (y : ↥(BootstrapBases.active b))
    (l : RootFreeEndpointLabel ↥(BootstrapBases.active b)) (hP : P.card = r-2)
    (hl : match l with
      | .inl l => l.2.card = r-2
      | .inr l => l.2.2.2.1.card = r-2 ∧ l.2.2.2.2.card = r-2)
    (hN : 8*r ≤ Fintype.card V) :
    rootFreeEndpointMean r (inducedHost (BootstrapBases.active b) H) P y l ≤
      (r : ℝ)*H.card/(rootFreeEndpointActive P y l).card ∧
    (r : ℝ)*H.card/(rootFreeEndpointActive P y l).card ≤
      2*meanDegree (V := V) r H.card := by
  have hδ := BootstrapBases.deleted_card_le b
  have hdel : (BootstrapBases.deleted b).card + (univ \ rootFreeEndpointActive P y l).card ≤ 4*r := by
    cases l with
    | inl l =>
      have hd := BootstrapActualDeletionBounds.endpointI_core
        (M := (∅ : Finset (Finset ↥(BootstrapBases.active b)))) none P y l hP hl
      simp only [BootstrapBases.deleted_none, empty_union, card_empty, zero_add] at hd
      change (BootstrapBases.deleted b).card + (univ \ (univ \ (P ∪ l.deleted y))).card ≤ 4*r
      rw [show univ \ (univ \ (P ∪ l.deleted y)) = P ∪ l.deleted y by ext v; simp]
      omega
    | inr l =>
      have hd := BootstrapActualDeletionBounds.endpointII_core
        (M := (∅ : Finset (Finset ↥(BootstrapBases.active b)))) none P y l hP hl.1 hl.2
      simp only [BootstrapBases.deleted_none, empty_union, card_empty, zero_add] at hd
      change (BootstrapBases.deleted b).card + (univ \ (univ \ (P ∪ l.deleted y))).card ≤ 4*r
      rw [show univ \ (univ \ (P ∪ l.deleted y)) = P ∪ l.deleted y by ext v; simp]
      omega
  exact base_mean_bounds b r (4*r) H _ (by omega) (by omega) hdel

end LooseHamilton.BootstrapMeans
