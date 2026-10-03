module

public import HittingTimeLooseHamilton.BiasedCloneKahnRelabel
public import HittingTimeLooseHamilton.Models
public import HittingTimeLooseHamilton.BiasedMatchingCollisionModels

public section

/-! Relabelling the common clone universe preserves all host incidence counts. -/
noncomputable section
open Finset
namespace LooseHamilton.CloneRelabel
variable {A : Type*} [Fintype A] [DecidableEq A] {n r : ℕ}
variable (U : Finset A) (e : ↥U ≃ Fin n) (G : Finset (Finset A))
variable (hsub : ∀ B ∈ G, B ⊆ U) (hunif : ∀ B ∈ G, B.card=r)

include hsub in
theorem family_card : (family U e G).card = G.card := by
  apply card_image_iff.mpr
  intro B hB D hD h
  exact edge_injective_on U e (hsub B hB) (hsub D hD) h

theorem family_filter (P : Finset (Fin n) → Prop) [DecidablePred P] :
    (family U e G).filter P = family U e (G.filter (fun B => P (edge U e B))) := by
  ext B
  simp only [family, mem_filter, mem_image]
  constructor
  · rintro ⟨⟨D,hD,rfl⟩,hP⟩
    exact ⟨D,⟨hD,hP⟩,rfl⟩
  · rintro ⟨D,⟨hD,hP⟩,rfl⟩
    exact ⟨⟨D,hD,rfl⟩,hP⟩

theorem host_card : (host U e G hsub hunif).edges.card = G.card :=
  family_card U e G hsub

theorem host_vertexDegree (v : Fin n) :
    vertexDegree (host U e G hsub hunif).edges v = vertexDegree G (e.symm v).val := by
  change ((family U e G).filter (fun B => v∈B)).card = _
  rw [family_filter, family_card U e _ (fun B hB => hsub B (mem_filter.mp hB).1)]
  simp only [mem_edge]
  rfl

theorem host_pairDegree (v w : Fin n) :
    pairDegree (host U e G hsub hunif).edges v w =
      pairDegree G (e.symm v).val (e.symm w).val := by
  change ((family U e G).filter (fun B => v∈B ∧ w∈B)).card = _
  rw [family_filter, family_card U e _ (fun B hB => hsub B (mem_filter.mp hB).1)]
  simp only [mem_edge]
  rfl

theorem kahnIncident_card (v : Fin n) :
    Fintype.card (KahnIncident (host U e G hsub hunif) v) =
      vertexDegree G (e.symm v).val := by
  rw [← host_vertexDegree U e G hsub hunif v]
  simp only [KahnIncident, vertexDegree, Fintype.card_subtype]
  congr 1
  ext B
  simp

end LooseHamilton.CloneRelabel
