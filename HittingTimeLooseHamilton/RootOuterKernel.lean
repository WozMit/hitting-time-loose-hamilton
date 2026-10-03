module

public import HittingTimeLooseHamilton.RootOuterTransport

public section
noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma outerExtension_nonempty (U I : Finset A) (q : ℕ)
    (hI : I⊆U) (hi : I.card≤q) (hq : q≤U.card) : Nonempty (OuterExtension U I q) := by
  obtain ⟨T,hIT,hTU,hT⟩ := exists_subsuperset_card_eq hI hi hq
  exact ⟨⟨T,hIT,mem_powersetCard.mpr ⟨hTU,hT⟩⟩⟩

/-- Fresh uniform outer completion of a fixed inner b-subset. -/
@[expose] def rootOuterKernel (U : Finset A) (b q : ℕ) (hbq : b≤q) (hq : q≤U.card)
    (I : ↥(U.powersetCard b)) : FiniteEntropy.Law (Finset A) := by
  letI := outerExtension_nonempty U I.val q (mem_powersetCard.mp I.property).1
    (by rw [(mem_powersetCard.mp I.property).2]; exact hbq) hq
  exact (FiniteEntropy.uniform : FiniteEntropy.Law (OuterExtension U I.val q)).map Subtype.val

/-- Relabeling to a specified second inner set, avoiding dependent casts in the target. -/
@[expose] def outerExtensionRelabelTo (U I J : Finset A) (q : ℕ) (g : Equiv.Perm A)
    (hU : U.map g.toEmbedding=U) (hI : I.map g.toEmbedding=J) :
    OuterExtension U I q ≃ OuterExtension U J q :=
  g.finsetCongr.subtypeEquiv (by
    intro T
    have hTU : T.map g.toEmbedding⊆U ↔ T⊆U := by
      conv_lhs => rw [←hU]
      exact map_subset_map
    simp only [Equiv.finsetCongr_apply,mem_powersetCard,card_map]
    rw [←hI,map_subset_map,hTU])

/-- Kernel covariance holds for every universe-preserving relabeling. -/
theorem rootOuterKernel_map (U : Finset A) (b q : ℕ) (hbq : b≤q) (hq : q≤U.card)
    (I J : ↥(U.powersetCard b)) (g : Equiv.Perm A)
    (hU : U.map g.toEmbedding=U) (hI : I.val.map g.toEmbedding=J.val) :
    (rootOuterKernel U b q hbq hq I).map g.finsetCongr =
      rootOuterKernel U b q hbq hq J := by
  letI := outerExtension_nonempty U I.val q (mem_powersetCard.mp I.property).1
    (by rw [(mem_powersetCard.mp I.property).2]; exact hbq) hq
  letI := outerExtension_nonempty U J.val q (mem_powersetCard.mp J.property).1
    (by rw [(mem_powersetCard.mp J.property).2]; exact hbq) hq
  have he := uniform_equiv_map (outerExtensionRelabelTo U I.val J.val q g hU hI)
  have hh := congrArg (fun p : FiniteEntropy.Law (OuterExtension U J.val q) => p.map Subtype.val) he
  have hx := FiniteEntropy.Law.map_map
    (FiniteEntropy.uniform : FiniteEntropy.Law (OuterExtension U I.val q))
    (outerExtensionRelabelTo U I.val J.val q g hU hI)
    (fun x : OuterExtension U J.val q => x.val)
  have hy := FiniteEntropy.Law.map_map
    (FiniteEntropy.uniform : FiniteEntropy.Law (OuterExtension U I.val q))
    (fun x : OuterExtension U I.val q => x.val) g.finsetCongr
  exact hy.trans (hx.symm.trans hh)
end LooseHamilton
