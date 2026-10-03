module

public import HittingTimeLooseHamilton.BiasedRoleModels
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-! Exact asymptotic specification of Theorem 6.1. The root and its initial
endpoint implement the orientation convention fixed in Section 2. -/
noncomputable section
namespace LooseHamilton
open Filter

/-- One actual host and an arbitrary law on its connected spanning mixed cycles. -/
structure BiasedRoleInstance (r : ℕ) where
  N : ℕ
  host : SimpleHypergraph (Fin N)
  markers : SimpleHypergraph (Fin N)
  host_uniform : host ⊆ completeEdges (Fin N) r
  marked_matching : IsPairMatching markers
  root : ↥markers
  initial : ↥root.val
  cycleLaw : FiniteEntropy.Law (BiasedCycleState r markers host)

namespace BiasedRoleInstance
variable {r : ℕ}
@[expose] def s (D : BiasedRoleInstance r) : ℕ := D.markers.card
@[expose] def k (D : BiasedRoleInstance r) : ℕ := ordinaryEdgeCount r D.markers
@[expose] def μ (D : BiasedRoleInstance r) : ℝ := meanDegree (V:=Fin D.N) r D.host.card
@[expose] def η (D : BiasedRoleInstance r) : ℝ := (maxPairDegree D.host : ℝ)/D.μ

@[expose] def partitionBound (D : BiasedRoleInstance r) (δ : ℝ) : Prop :=
  ∀ A : Finset (Fin D.N), originalPorts D.markers ⊆ A → A.card=D.k+D.s →
    |(partitionCount D.host A:ℝ)-partitionDensity r*D.host.card| ≤ δ*D.N*D.μ

@[expose] def entropyBound (D : BiasedRoleInstance r) (ξ : ℝ) : Prop :=
  (D.k:ℝ)*Real.log (((r:ℝ)-1)*D.μ)-((r:ℝ)-1)*D.k-ξ*D.N ≤
    FiniteEntropy.entropy D.cycleLaw.mass

@[expose] def deviation (D : BiasedRoleInstance r) : ℝ :=
  biasedRoleDeviation r D.markers D.host D.root D.initial D.cycleLaw
end BiasedRoleInstance

/-- The exact sequence interpretation of the printed O_{r,C} bound: one
constant depends only on r and C, before any host sequence or error sequence.
No uniformity or independence is imposed on the cycle distribution. -/
@[expose] def Theorem61 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ C : ℝ, 0<C →
  ∃ K : ℝ, 0<K ∧
  ∀ D : ℕ → BiasedRoleInstance r, ∀ ξ δ : ℕ → ℝ,
    Tendsto (fun n => (D n).μ) atTop atTop →
    Tendsto (fun n => ((D n).s:ℝ)/(D n).N) atTop (nhds 0) →
    Tendsto (fun n => (D n).η) atTop (nhds 0) →
    Tendsto δ atTop (nhds 0) →
    Tendsto ξ atTop (nhds 0) →
    (∀ᶠ n in atTop, 0≤ξ n) →
    (∀ᶠ n in atTop, ∀ v, (vertexDegree (D n).host v:ℝ) ≤ C*(D n).μ) →
    (∀ᶠ n in atTop, (D n).partitionBound (δ n)) →
    (∀ᶠ n in atTop, (D n).entropyBound (ξ n)) →
    ∀ᶠ n in atTop, (D n).deviation ≤ K*(D n).N*
      Real.sqrt (biasedRoleError r (D n).N (D n).s (ξ n) (δ n) (D n).η)
end LooseHamilton
