module

public import HittingTimeLooseHamilton.BootstrapInducedMeans
public import HittingTimeLooseHamilton.RootFreeEndpointMean
public import HittingTimeLooseHamilton.RootFreePrivateTests
public import HittingTimeLooseHamilton.VertexRestriction

public section

/-! Flattening actual source normalizations from a base subtype to ambient V. -/
noncomputable section
namespace LooseHamilton.BootstrapMeans
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem ambientEdge_subset_base (A : Finset V) (e : Finset ↥A) :
    ambientEdge A e ⊆ A := by
  intro x hx
  obtain ⟨v,_,rfl⟩ := mem_map.mp hx
  exact v.property

theorem ambientEdge_restrict (A e : Finset V) (he : e ⊆ A) :
    ambientEdge A (restrictEdge A e) = e := by
  unfold ambientEdge
  rw [map_eq_image]
  exact lift_restrictEdge A e he

theorem induced_card_filter (A : Finset V) (H : SimpleHypergraph V) :
    (inducedHost A H).card = (H.filter fun e => e ⊆ A).card := by
  have hi : (inducedHost A H).image (ambientEdge A) = H.filter (fun e => e ⊆ A) := by
    ext e
    constructor
    · intro he
      obtain ⟨q,hq,rfl⟩ := mem_image.mp he
      exact mem_filter.mpr ⟨(mem_inducedHost _ _ _).mp hq, ambientEdge_subset_base A q⟩
    · intro he
      obtain ⟨hH,hA⟩ := mem_filter.mp he
      refine mem_image.mpr ⟨restrictEdge A e, ?_, ambientEdge_restrict A e hA⟩
      simpa only [mem_inducedHost, ambientEdge_restrict A e hA] using hH
  rw [← hi]
  exact (card_image_of_injective _ (Finset.map_injective _)).symm

omit [Fintype V] [DecidableEq V] in
theorem ambientEdge_subset_iff (A : Finset V) (e T : Finset ↥A) :
    ambientEdge A e ⊆ ambientEdge A T ↔ e ⊆ T := by
  exact map_subset_map

theorem induced_nested_card (A : Finset V) (T : Finset ↥A) (H : SimpleHypergraph V) :
    (inducedHost T (inducedHost A H)).card = (inducedHost (ambientEdge A T) H).card := by
  rw [induced_card_filter]
  have he : (inducedHost A H).filter (fun e => e ⊆ T) =
      inducedHost A (H.filter fun e => e ⊆ ambientEdge A T) := by
    ext e
    simp only [mem_filter, mem_inducedHost, ambientEdge_subset_iff]
  rw [he, induced_card_filter, induced_card_filter]
  congr 1
  ext e
  simp only [mem_filter]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, h.2.trans (ambientEdge_subset_base A T)⟩

theorem inducedMean_nested (r : ℕ) (H : SimpleHypergraph V)
    (A : Finset V) (T : Finset ↥A) :
    inducedMean r (inducedHost A H) T = inducedMean r H (ambientEdge A T) := by
  simp only [inducedMean, meanDegree, Fintype.card_coe, ambientEdge_card, induced_nested_card]

theorem privateRootSourceMean_ambient (r : ℕ) (H : SimpleHypergraph V)
    (A : Finset V) (S : Finset ↥A) (x : ↥A) :
    privateRootSourceMean r (inducedHost A H) S x =
      inducedMean r H (ambientEdge A (univ \ insert x S)) := by
  rw [← inducedMean_nested]
  simp only [privateRootSourceMean, inducedMean, meanDegree, Fintype.card_coe]

theorem rootFreeEndpointMean_ambient (r : ℕ) (H : SimpleHypergraph V)
    (A : Finset V) (P : Finset ↥A) (y : ↥A) (l : RootFreeEndpointLabel ↥A) :
    rootFreeEndpointMean r (inducedHost A H) P y l =
      inducedMean r H (ambientEdge A (rootFreeEndpointActive P y l)) :=
  inducedMean_nested r H A (rootFreeEndpointActive P y l)

end LooseHamilton.BootstrapMeans
