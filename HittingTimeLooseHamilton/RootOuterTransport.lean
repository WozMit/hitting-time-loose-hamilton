module

public import HittingTimeLooseHamilton.UniformNestedOuter
public import HittingTimeLooseHamilton.RootLinkTailTransfer

public section
noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]
attribute [local instance] Classical.propDecidable

/-- All fixed-size outer subsets containing a prescribed inner subset. -/
@[expose] def OuterExtension (U I : Finset A) (q : ℕ) :=
  {T : Finset A // I ⊆ T ∧ T ∈ U.powersetCard q}
@[expose] instance (U I : Finset A) (q : ℕ) : Fintype (OuterExtension U I q) := by
  unfold OuterExtension
  infer_instance

/-- Relabeling a universe relabels its outer-extension fibers bijectively. -/
@[expose] def outerExtensionRelabel (U I : Finset A) (q : ℕ) (g : Equiv.Perm A)
    (hU : U.map g.toEmbedding=U) :
    OuterExtension U I q ≃ OuterExtension U (I.map g.toEmbedding) q :=
  g.finsetCongr.subtypeEquiv (by
    intro T
    have hTU : T.map g.toEmbedding ⊆ U ↔ T ⊆ U := by
      conv_lhs => rw [←hU]
      exact map_subset_map
    simp only [Equiv.finsetCongr_apply,mem_powersetCard,map_subset_map,card_map,hTU])

lemma uniform_equiv_map {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    [Nonempty Ω] [Nonempty Λ] (e : Ω ≃ Λ) :
    (FiniteEntropy.uniform : FiniteEntropy.Law Ω).map e =
      (FiniteEntropy.uniform : FiniteEntropy.Law Λ) := by
  apply FiniteEntropy.Law.ext_mass
  intro y
  change (FiniteEntropy.uniform : FiniteEntropy.Law Ω).event (fun x => e x=y) = _
  rw [FiniteEntropy.Law.uniform_event_equiv e (fun x => x=y)]
  simp [FiniteEntropy.Law.event]

/-- A fresh uniform outer extension remains fresh and uniform after relabeling. -/
theorem outerExtensionRelabel_uniform (U I : Finset A) (q : ℕ) (g : Equiv.Perm A)
    (hU : U.map g.toEmbedding=U) [Nonempty (OuterExtension U I q)]
    [Nonempty (OuterExtension U (I.map g.toEmbedding) q)] :
    (FiniteEntropy.uniform : FiniteEntropy.Law (OuterExtension U I q)).map
      (outerExtensionRelabel U I q g hU) =
      (FiniteEntropy.uniform : FiniteEntropy.Law (OuterExtension U (I.map g.toEmbedding) q)) :=
  uniform_equiv_map _

omit [Fintype A] in
/-- Relabeling by one transposition increases occupancy of any test set by at most one. -/
theorem swap_inter_card_le (T Γ : Finset A) (a b : A) :
    ((T.map (Equiv.swap a b).toEmbedding) ∩ Γ).card ≤ (T ∩ Γ).card+1 := by
  classical
  have hfix (x : A) (hxa : x≠a) (hxb : x≠b) : Equiv.swap a b x=x :=
    Equiv.swap_apply_of_ne_of_ne hxa hxb
  by_cases ha : a∈T
  · by_cases hb : b∈T
    · have he : T.map (Equiv.swap a b).toEmbedding=T := by
        ext x
        simp only [mem_map,Equiv.toEmbedding_apply]
        constructor
        · rintro ⟨y,hy,rfl⟩
          by_cases hya : y=a
          · subst y; simpa using hb
          by_cases hyb : y=b
          · subst y; simpa using ha
          simpa [hfix y hya hyb] using hy
        · intro hx
          refine ⟨Equiv.swap a b x,?_,by simp⟩
          by_cases hxa : x=a
          · subst x; simpa using hb
          by_cases hxb : x=b
          · subst x; simpa using ha
          simpa [hfix x hxa hxb] using hx
      rw [he]; omega
    · have hsub : T.map (Equiv.swap a b).toEmbedding ⊆ T ∪ {b} := by
        intro x hx
        obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
        by_cases hya : y=a
        · subst y; simp
        have hyb : y≠b := fun he => hb (he ▸ hy)
        simp only [Equiv.toEmbedding_apply,hfix y hya hyb]
        exact mem_union_left _ hy
      exact (card_le_card (inter_subset_inter hsub (Subset.refl Γ))).trans
        (by simpa using prescribed_inter_card_le T {b} Γ)
  · have hsub : T.map (Equiv.swap a b).toEmbedding ⊆ T ∪ {a} := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
      by_cases hyb : y=b
      · subst y; simp
      have hya : y≠a := fun he => ha (he ▸ hy)
      simp only [Equiv.toEmbedding_apply,hfix y hya hyb]
      exact mem_union_left _ hy
    exact (card_le_card (inter_subset_inter hsub (Subset.refl Γ))).trans
      (by simpa using prescribed_inter_card_le T {a} Γ)
end LooseHamilton
