module

public import HittingTimeLooseHamilton.BiasedCloneHostPorts

public section

/-! Explicit finite error bounds for the average degree of the actual clone host. -/
noncomputable section
open Finset
namespace LooseHamilton.MixedCycleWitness
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {markers edges : Finset (Finset V)}

theorem cloneHost_count_error (C : MixedCycleWitness r markers edges)
    (G : SimpleHypergraph V) (L : ℕ) (hG : ∀e∈G,e.card=r)
    (hdeg : ∀v, vertexDegree G v ≤ L) (target error : ℝ)
    (hpart : |(partitionCount G (univ.image C.junction):ℝ)-target| ≤ error) :
    |((cloneHost G C.cloneVertices).card:ℝ)-2*target| ≤
      2*error + 2*(markers.card:ℝ)*(r:ℝ)*(r:ℝ)*L := by
  obtain ⟨hu,hl⟩ := C.cloneHost_cycle_port_error G L hG hdeg
  have hu' : ((cloneHost G C.cloneVertices).card:ℝ) ≤
      2*(partitionCount G (univ.image C.junction):ℝ) := by exact_mod_cast hu
  have hl' : 2*(partitionCount G (univ.image C.junction):ℝ) ≤
      ((cloneHost G C.cloneVertices).card:ℝ)+2*(markers.card:ℝ)*((r:ℝ)*r*L) := by exact_mod_cast hl
  have he : 0≤2*(markers.card:ℝ)*((r:ℝ)*r*L) := by positivity
  rcases abs_le.mp hpart with ⟨hpl,hpu⟩
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Since the active slot set has size `r*k`, its average degree is `|H|/k`. -/
theorem cloneHost_mean_error (C : MixedCycleWitness r markers edges)
    (G : SimpleHypergraph V) (L : ℕ) (hG : ∀e∈G,e.card=r)
    (hdeg : ∀v, vertexDegree G v ≤ L) (target error : ℝ)
    (hpart : |(partitionCount G (univ.image C.junction):ℝ)-target| ≤ error)
    (hk : 0 < edges.card) :
    |((cloneHost G C.cloneVertices).card:ℝ)/(edges.card:ℝ)-2*target/(edges.card:ℝ)| ≤
      (2*error + 2*(markers.card:ℝ)*(r:ℝ)*(r:ℝ)*L)/(edges.card:ℝ) := by
  have hk' : (0:ℝ)<edges.card := by exact_mod_cast hk
  rw [← sub_div, abs_div, abs_of_pos hk']
  exact (div_le_div_iff_of_pos_right hk').mpr (C.cloneHost_count_error G L hG hdeg target error hpart)
end LooseHamilton.MixedCycleWitness
