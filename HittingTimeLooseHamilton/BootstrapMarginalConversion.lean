module

public import HittingTimeLooseHamilton.CompletionMarginalCap

public section

/-! The inverse-mean and k/j scales agree under exact admissible bookkeeping. -/
noncomputable section
namespace LooseHamilton.BootstrapMarginalConversion
open Finset

/-- The half-size bound on the marker count follows from matching disjointness
for every instance; no additional eventual assumption is necessary. -/
theorem of_admissible {N r m : ℕ} {ell : Fin N → ℕ}
    {M : Finset (Finset (Fin N))} {offset q D : ℝ}
    (hadm : CoreAdmissible r m ell M offset) (j : ℕ) (hD : 0 ≤ D)
    (hq : q ≤ D/meanDegree (V:=Fin N) r j) :
    q ≤ (2*D)*(ordinaryEdgeCount r M:ℝ)/j := by
  have hs : 2*M.card ≤ N := by simpa using hadm.marker_matching.twice_card_le
  have hN : 0<N := by have := hadm.markers_nonempty; omega
  by_cases hj : j=0
  · subst j
    simpa [meanDegree] using hq
  · exact inverse_degree_cap_to_k_over_j (r:=r) (s:=M.card) (k:=ordinaryEdgeCount r M) hN (Nat.pos_of_ne_zero hj)
      (by have := hadm.uniformity; omega)
      (by simpa using hadm.vertex_bookkeeping) hs
      (by simp only [meanDegree,Fintype.card_fin]) hD hq

end LooseHamilton.BootstrapMarginalConversion
