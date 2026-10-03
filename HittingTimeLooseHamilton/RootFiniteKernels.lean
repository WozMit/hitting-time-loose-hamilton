module

public import HittingTimeLooseHamilton.KahnMixtureEntropy

public section

/-! Finite reconstruction and common-randomness coupling, with no analytic measure theory. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {A B I J R : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J] [Fintype R]

/-- Mapping one independent coordinate commutes with the product law. -/
lemma root_map_prod_left (p : FiniteEntropy.Law A) (q : FiniteEntropy.Law R)
    (f : A → I) :
    (p.prod q).map (fun ar => (f ar.1,ar.2)) = (p.map f).prod q := by
  classical
  apply FiniteEntropy.Law.ext_mass
  intro ⟨i,r⟩
  simp only [FiniteEntropy.Law.map,FiniteEntropy.Law.event,FiniteEntropy.Law.prod,
    Fintype.sum_prod_type,Prod.mk.injEq]
  rw [sum_mul]
  apply sum_congr rfl
  intro a _
  by_cases h : f a=i <;> simp [h]

/-- Sampling a fibre with its conditional law reconstructs the original law.
Only positive-mass fibres need the specified reconstruction rule. -/
lemma root_reconstruct_law (p : FiniteEntropy.Law A) (f : A → I)
    (seed : FiniteEntropy.Law R) (g : I → R → A)
    (hg : ∀ i, 0 < (p.map f).mass i →
      seed.map (g i) = p.conditionOr (fun a => f a=i)) :
    ((p.map f).prod seed).map (fun ir => g ir.1 ir.2) = p := by
  classical
  have hk : (p.map f).kernel (fun i => seed.map (g i)) =
      (p.map f).kernel (fun i => p.conditionOr (fun a => f a=i)) := by
    apply FiniteEntropy.Law.ext_mass
    intro ⟨i,a⟩
    change (p.map f).mass i * (seed.map (g i)).mass a =
      (p.map f).mass i * (p.conditionOr (fun a => f a=i)).mass a
    by_cases hi : (p.map f).mass i=0
    · simp [hi]
    · rw [hg i (lt_of_le_of_ne ((p.map f).nonneg i) (Ne.symm hi))]
  have hkeep := (p.map f).map_prod_keep_left seed g
  have h := congrArg (fun t : FiniteEntropy.Law (I×A) => t.map Prod.snd) hkeep
  rw [hk,p.conditional_kernel_eq_map f] at h
  simp only [FiniteEntropy.Law.map_map,Function.comp_def] at h
  exact h.trans p.map_id

/-- The same finite random seed lifts an explicit count coupling to the
reconstructed objects. Both marginals are exact, not just tail bounds. -/
theorem root_reconstructed_coupling (p q : FiniteEntropy.Law A) (f : A → I)
    (c : FiniteEntropy.Law (I×I))
    (hc₁ : c.map Prod.fst=p.map f) (hc₂ : c.map Prod.snd=q.map f)
    (seed : FiniteEntropy.Law R) (g : I → R → A)
    (hp : ∀ i, 0<(p.map f).mass i → seed.map (g i)=p.conditionOr (fun a=>f a=i))
    (hq : ∀ i, 0<(q.map f).mass i → seed.map (g i)=q.conditionOr (fun a=>f a=i))
    (Rel : A → A → Prop)
    (hrel : ∀ i j r, 0<c.mass (i,j) → 0<seed.mass r → Rel (g i r) (g j r)) :
    ∃ d : FiniteEntropy.Law (A×A), d.map Prod.fst=p ∧ d.map Prod.snd=q ∧
      ∀ a b, 0<d.mass (a,b) → Rel a b := by
  classical
  let d := (c.prod seed).map (fun ir => (g ir.1.1 ir.2,g ir.1.2 ir.2))
  refine ⟨d,?_,?_,?_⟩
  · change ((c.prod seed).map _).map Prod.fst=p
    rw [FiniteEntropy.Law.map_map]
    have hm := root_map_prod_left c seed Prod.fst
    have he := congrArg (fun x : FiniteEntropy.Law (I×R) => x.map (fun ir=>g ir.1 ir.2)) hm
    rw [hc₁,root_reconstruct_law p f seed g hp] at he
    simpa only [FiniteEntropy.Law.map_map,Function.comp_def] using he
  · change ((c.prod seed).map _).map Prod.snd=q
    rw [FiniteEntropy.Law.map_map]
    have hm := root_map_prod_left c seed Prod.snd
    have he := congrArg (fun x : FiniteEntropy.Law (I×R) => x.map (fun ir=>g ir.1 ir.2)) hm
    rw [hc₂,root_reconstruct_law q f seed g hq] at he
    simpa only [FiniteEntropy.Law.map_map,Function.comp_def] using he
  · intro a b hab
    simp only [d,FiniteEntropy.Law.map,FiniteEntropy.Law.event,FiniteEntropy.Law.prod] at hab
    have hab' : 0 < ∑ ir : (I×I)×R, if (g ir.1.1 ir.2,g ir.1.2 ir.2)=(a,b)
        then c.mass ir.1*seed.mass ir.2 else 0 := by
      convert hab using 1
      apply Finset.sum_congr rfl
      intro ir _
      split_ifs <;> rfl
    have hex : ∃ ir : (I×I)×R, 0 < (if (g ir.1.1 ir.2,g ir.1.2 ir.2)=(a,b)
        then c.mass ir.1*seed.mass ir.2 else 0) := by
      by_contra hn
      push_neg at hn
      exact not_le_of_gt hab' (sum_nonpos (fun ir _ => hn ir))
    obtain ⟨ir,hir⟩ := hex
    split_ifs at hir with he
    · have hcpos : 0<c.mass ir.1 := (mul_pos_iff.mp hir).elim
        (fun h=>h.1) (fun h=>False.elim (not_lt_of_ge (c.nonneg ir.1) h.1))
      have hrpos : 0<seed.mass ir.2 := (mul_pos_iff.mp hir).elim
        (fun h=>h.2) (fun h=>False.elim (not_lt_of_ge (seed.nonneg ir.2) h.2))
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      exact hrel ir.1.1 ir.1.2 ir.2 hcpos hrpos
    · linarith
end LooseHamilton
