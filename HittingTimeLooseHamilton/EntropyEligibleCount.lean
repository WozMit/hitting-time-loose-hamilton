module

public import HittingTimeLooseHamilton.BiasedRoleParameters
public import HittingTimeLooseHamilton.PathPerturbationBounds

public section

/-! Existing host edges avoiding marked ports retain almost all of the host. -/
noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open Finset
variable {r : ℕ}

lemma eligible_edge_loss (D : BiasedRoleInstance r) {C : ℝ}
    (hdeg : ∀ v, (vertexDegree D.host v : ℝ) ≤ C*D.μ) :
    (D.host.card : ℝ) - (D.host.filter (fun e => Disjoint e (originalPorts D.markers))).card
      ≤ 2*(D.s : ℝ)*C*D.μ := by
  have h := deleteVertices_edge_loss_real D.host (originalPorts D.markers) (C*D.μ) hdeg
  rw [deleteVertices_card] at h
  rw [D.marked_matching.ports_card] at h
  simpa only [survivingHost, Nat.cast_mul, Nat.cast_ofNat, s, mul_assoc] using h

lemma eligible_edge_half (D : BiasedRoleInstance r) {C : ℝ}
    (hdeg : ∀ v, (vertexDegree D.host v : ℝ) ≤ C*D.μ)
    (hs : 4*(D.s : ℝ)*C*D.μ ≤ D.host.card) :
    (D.host.card : ℝ)/2 ≤
      (D.host.filter (fun e => Disjoint e (originalPorts D.markers))).card := by
  have h := D.eligible_edge_loss hdeg
  linarith

end LooseHamilton.BiasedRoleInstance
