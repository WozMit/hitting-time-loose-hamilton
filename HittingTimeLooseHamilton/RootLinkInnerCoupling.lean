module

public import HittingTimeLooseHamilton.RootLinkInnerReconstruction
public import HittingTimeLooseHamilton.RootLinkReconstructionSwap
public import HittingTimeLooseHamilton.RootFiniteKernels
public import HittingTimeLooseHamilton.RootConditionRefinement

public section

/-! The genuine one-swap coupling of a uniform inner subset with its hit-conditioned law. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The paper's common-orders construction gives both exact marginals and at
most one replacement. The conditional marginal is the actual conditioned law. -/
theorem root_inner_one_swap_coupling (S : Finset A) (b : ℕ)
    [Nonempty (RootInnerState A b)]
    (hE : 0<(FiniteEntropy.uniform : FiniteEntropy.Law (RootInnerState A b)).event
      (fun T=>1≤(T.val∩S).card)) :
    ∃ d : FiniteEntropy.Law (RootInnerState A b × RootInnerState A b),
      d.map Prod.fst=(FiniteEntropy.uniform : FiniteEntropy.Law (RootInnerState A b)) ∧
      d.map Prod.snd=(FiniteEntropy.uniform : FiniteEntropy.Law (RootInnerState A b)).condition
        (fun T=>1≤(T.val∩S).card) hE ∧
      ∀ T U, 0<d.mass (T,U) →
        (T.val\U.val).card≤1 ∧ (U.val\T.val).card≤1 ∧
        (T.val=U.val ∨ ∃x y : A,T.val.image (Equiv.swap x y)=U.val) := by
  classical
  let p : FiniteEntropy.Law (RootInnerState A b) := FiniteEntropy.uniform
  let f := rootIntersectionIndex (univ:Finset A) S b
  let q := p.condition (fun T=>1≤(T.val∩S).card) hE
  let c := rootUniformCountCoupling univ S (subset_univ _) b hE
  have hc₁ : c.map Prod.fst=p.map f := rootUniformCountCoupling_first univ S (subset_univ _) b hE
  have hc₂ : c.map Prod.snd=q.map f := rootUniformCountCoupling_second univ S (subset_univ _) b hE
  have hp (j : Fin (b+1)) (hj : 0<(p.map f).mass j) :
      (rootInnerSeedLaw S).map (rootInnerReconstruct S b j)=p.conditionOr (fun T=>f T=j) :=
    rootInnerReconstruct_law S b j hj
  have hq (j : Fin (b+1)) (hj : 0<(q.map f).mass j) :
      (rootInnerSeedLaw S).map (rootInnerReconstruct S b j)=q.conditionOr (fun T=>f T=j) := by
    have he := root_condition_fiber_refinement p f (fun i : Fin (b+1) => 1 ≤ i.val) hE j hj
    exact (hp j he.1).trans he.2.symm
  apply root_reconstructed_coupling p q f c hc₁ hc₂ (rootInnerSeedLaw S)
    (rootInnerReconstruct S b) hp hq
  intro i j σ hij hσ
  have hpi : 0<(p.map f).mass i := by
    rw [←hc₁]
    exact c.event_pos_of_mass_pos (fun x=>x.1=i) (i,j) rfl hij
  have hqj : 0<(q.map f).mass j := by
    rw [←hc₂]
    exact c.event_pos_of_mass_pos (fun x=>x.2=j) (i,j) rfl hij
  have hpj := (root_condition_fiber_refinement p f (fun i : Fin (b+1) => 1 ≤ i.val) hE j hqj).1
  have hi := rootInnerCount_positive_valid S b i hpi
  have hj := rootInnerCount_positive_valid S b j hpj
  have hstep := rootUniformCountCoupling_support univ S (subset_univ _) b hE (i,j) hij.ne'
  simp only [rootInnerReconstruct_val S b i hi σ,rootInnerReconstruct_val S b j hj σ]
  have hnear := rootCountSet_near S b i.val j.val σ hstep.1 hstep.2 (by omega) hj.1 hi.2
  exact ⟨hnear.1,hnear.2,rootCountSet_swap S b i.val j.val σ hstep.1 hstep.2 (by omega) hj.1 hi.2⟩
end LooseHamilton
