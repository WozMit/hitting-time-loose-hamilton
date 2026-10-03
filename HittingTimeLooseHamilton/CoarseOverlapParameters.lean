module

public import HittingTimeLooseHamilton.BiasedRoleParametersLimit

public section

noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open Filter Finset
variable {r : ℕ}

lemma twice_markers_le_vertices (D : BiasedRoleInstance r) : 2*D.s≤D.N := by
  have h := card_le_card (subset_univ (originalPorts D.markers))
  rw [D.marked_matching.ports_card] at h
  simpa [s] using h

/-- The lower comparison k ≍ N follows from the matching and cycle identities. -/
lemma vertices_le_two_rk (D : BiasedRoleInstance r) (hr : 3≤r) :
    D.N≤2*(r-1)*D.k := by
  have hb := D.vertex_bookkeeping hr
  have hs := D.twice_markers_le_vertices
  nlinarith

lemma k_tendsto_without_sparse_markers (hr : 3≤r) (D : ℕ→BiasedRoleInstance r)
    (hμ : Tendsto (fun n => (D n).μ) atTop atTop) :
    Tendsto (fun n => (D n).k) atTop atTop := by
  have hrR : (3:ℝ)≤r := by exact_mod_cast hr
  have hp : (0:ℝ)<2*((r:ℝ)-1) := by linarith
  apply (tendsto_natCast_atTop_iff (R:=ℝ)).mp
  have ht := (N_real_tendsto_atTop D hμ).atTop_div_const hp
  apply tendsto_atTop_mono' atTop _ ht
  apply Eventually.of_forall
  intro n
  apply (div_le_iff₀ hp).mpr
  have h := (D n).vertices_le_two_rk hr
  have hc : ((D n).N:ℝ) ≤ ((2*(r-1)*(D n).k:ℕ):ℝ) := by exact_mod_cast h
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1≤r), Nat.cast_one] at hc
  nlinarith only [hc]
end LooseHamilton.BiasedRoleInstance
