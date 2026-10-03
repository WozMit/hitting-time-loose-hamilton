module

public import HittingTimeLooseHamilton.RootSamplingModels
public import HittingTimeLooseHamilton.RootLinkCoordinates

public section

/-! Literal degree and erased-link interpretation of the root sampling statement. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma root_degree_from_rootfree (y : V) (H H₀ : SimpleHypergraph V)
    (hfree : rootFreeEdges y H=H₀) : vertexDegree H y=H.card-H₀.card := by
  have h := card_filter_add_card_filter_not (s:=H) (p:=fun e=>y∈e)
  change vertexDegree H y+(rootFreeEdges y H).card=H.card at h
  rw [hfree] at h
  omega

/-- Root-edge coordinates preserve the occupancy count in the actual erased link. -/
lemma root_erased_link_intersection_card (r : ℕ) (y : V) (H Γ : SimpleHypergraph V)
    (hΓ : Γ⊆rootEdgeUniverse r y) :
    (rootLinkErase y (H∩rootEdgeUniverse r y) ∩ rootLinkErase y Γ).card=(H∩Γ).card := by
  have he : rootLinkErase y (H∩rootEdgeUniverse r y) ∩ rootLinkErase y Γ =
      rootLinkErase y (H∩Γ) := by
    ext e
    simp only [rootLinkErase,mem_inter,mem_image]
    constructor
    · rintro ⟨⟨a,⟨ha,hay⟩,hae⟩,⟨b,hb,hbe⟩⟩
      have ha0 := ((mem_rootEdgeUniverse r y a).mp hay).2
      have hb0 := ((mem_rootEdgeUniverse r y b).mp (hΓ hb)).2
      have hab : a=b := by
        have hh := congrArg (fun s=>insert y s) (hae.trans hbe.symm)
        simpa only [insert_erase ha0,insert_erase hb0] using hh
      exact ⟨a,⟨ha,hab ▸ hb⟩,hae⟩
    · rintro ⟨a,⟨ha,hag⟩,hae⟩
      exact ⟨⟨a,⟨ha,hΓ hag⟩,hae⟩,⟨a,hag,hae⟩⟩
  rw [he]
  exact rootLinkErase_card r y (H∩Γ) (inter_subset_right.trans hΓ)

lemma rootLinkBad_iff_erased (r : ℕ) (y : V) (F H Γ : SimpleHypergraph V)
    (hΓ : Γ⊆rootEdgeUniverse r y) (q : ℕ) :
    RootLinkBad Γ q (F,H) ↔
      (2:ℝ)*(q:ℝ)/3 ≤
        ((rootLinkErase y (H∩rootEdgeUniverse r y) ∩ rootLinkErase y Γ).card:ℝ) := by
  rw [root_erased_link_intersection_card r y H Γ hΓ]
  unfold RootLinkBad
  constructor
  · intro h
    have hh : (2:ℝ)*(q:ℝ)≤3*((H∩Γ).card:ℝ) := by exact_mod_cast h
    linarith
  · intro h
    have hh : (2:ℝ)*(q:ℝ)≤3*((H∩Γ).card:ℝ) := by linarith
    exact_mod_cast hh

end LooseHamilton
