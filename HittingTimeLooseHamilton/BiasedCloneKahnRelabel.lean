module

public import HittingTimeLooseHamilton.KahnStatement
public import HittingTimeLooseHamilton.KahnConditioning

public section

/-! A finite common clone universe is relabelled to Kahn's `Fin n` interface.
All partition and support assertions are proved, not supplied as entropy axioms. -/
noncomputable section
open Finset FiniteEntropy
namespace LooseHamilton.CloneRelabel
variable {A : Type*} [DecidableEq A] {n r : ℕ}
variable (U : Finset A) (e : ↥U ≃ Fin n)

@[expose] def edge (B : Finset A) : Finset (Fin n) :=
  (B.subtype (fun v => v ∈ U)).map e.toEmbedding

@[simp] theorem mem_edge (B : Finset A) (i : Fin n) :
    i ∈ edge U e B ↔ (e.symm i).val ∈ B := by
  simp [edge, mem_map, Equiv.eq_symm_apply]

theorem edge_card (B : Finset A) (hB : B ⊆ U) : (edge U e B).card = B.card := by
  rw [edge, card_map, card_subtype, filter_eq_self.mpr hB]

theorem edge_injective_on {B D : Finset A} (hB : B ⊆ U) (hD : D ⊆ U)
    (h : edge U e B = edge U e D) : B = D := by
  ext v
  by_cases hv : v ∈ U
  · have he := congrArg (fun S : Finset (Fin n) => e ⟨v,hv⟩ ∈ S) h
    simpa using iff_of_eq he
  · exact ⟨fun hb => False.elim (hv (hB hb)), fun hd => False.elim (hv (hD hd))⟩

@[expose] def family (F : Finset (Finset A)) : Finset (Finset (Fin n)) := F.image (edge U e)

theorem family_injective_on {F D : Finset (Finset A)}
    (hF : ∀ B ∈ F, B ⊆ U) (hD : ∀ B ∈ D, B ⊆ U)
    (h : family U e F = family U e D) : F = D := by
  ext B
  constructor
  · intro hB
    have hm : edge U e B ∈ family U e D := h ▸ mem_image_of_mem _ hB
    obtain ⟨B', hB', he⟩ := mem_image.mp hm
    have hb := edge_injective_on U e (hD B' hB') (hF B hB) he
    exact hb ▸ hB'
  · intro hB
    have hm : edge U e B ∈ family U e F := h.symm ▸ mem_image_of_mem _ hB
    obtain ⟨B', hB', he⟩ := mem_image.mp hm
    have hb := edge_injective_on U e (hF B' hB') (hD B hB) he
    exact hb ▸ hB'

/-- Any genuine uniform partition of the common universe becomes a perfect matching. -/
@[expose] def matching (F : Finset (Finset A))
    (hsub : ∀ B ∈ F, B ⊆ U) (hunif : ∀ B ∈ F, B.card = r)
    (hpart : ∀ v ∈ U, ∃! B, B ∈ F ∧ v ∈ B) : Kahn.PerfectMatching n r := by
  refine ⟨family U e F, ?_, ?_⟩
  · intro B hB
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hB
    rw [edge_card U e D (hsub D hD), hunif D hD]
  · intro i
    obtain ⟨B, ⟨hB, hi⟩, hu⟩ := hpart (e.symm i).val (e.symm i).property
    refine ⟨edge U e B, ⟨mem_image_of_mem _ hB, (mem_edge U e B i).mpr hi⟩, ?_⟩
    intro D hD
    obtain ⟨D', hD', rfl⟩ := mem_image.mp hD.1
    exact congrArg (edge U e) (hu D' ⟨hD', (mem_edge U e D' i).mp hD.2⟩)

/-- The host itself is relabelled by precisely the same map. -/
@[expose] def host (G : Finset (Finset A))
    (hsub : ∀ B ∈ G, B ⊆ U) (hunif : ∀ B ∈ G, B.card = r) : Kahn.Hypergraph n r :=
  ⟨family U e G, by
    intro B hB
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hB
    rw [edge_card U e D (hsub D hD), hunif D hD]⟩

@[expose] def matchingIn (G F : Finset (Finset A))
    (hGsub : ∀ B ∈ G, B ⊆ U) (hGunif : ∀ B ∈ G, B.card = r)
    (hFG : F ⊆ G) (hpart : ∀ v ∈ U, ∃! B, B ∈ F ∧ v ∈ B) :
    Kahn.MatchingIn (host U e G hGsub hGunif) :=
  ⟨matching U e F (fun B hB => hGsub B (hFG hB))
    (fun B hB => hGunif B (hFG hB)) hpart, image_subset_image hFG⟩

end LooseHamilton.CloneRelabel
