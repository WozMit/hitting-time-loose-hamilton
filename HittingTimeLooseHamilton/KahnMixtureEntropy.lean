module

public import HittingTimeLooseHamilton.KahnConditioning

public section

open scoped BigOperators
noncomputable section
namespace FiniteEntropy.Law
variable {S A B C : Type*} [Fintype S] [Fintype A] [Fintype B] [Fintype C]

/-- Retaining the mixing variable while observing the other coordinate produces a kernel law. -/
lemma map_prod_keep_left (ν : Law S) (p : Law A) (f : S → A → B) :
    (ν.prod p).map (fun sa => (sa.1, f sa.1 sa.2)) =
      ν.kernel (fun s => p.map (f s)) := by
  classical
  apply ext_mass
  intro ⟨s,b⟩
  simp only [map, event, prod, kernel]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single s]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : f s a = b <;> simp [ha]
  · intro t _ ht
    apply Finset.sum_eq_zero
    intro a _
    simp [Prod.mk.injEq, ht]
  · simp

lemma entropy_map_prod_keep_left (ν : Law S) (p : Law A) (f : S → A → B) :
    entropy ((ν.prod p).map (fun sa => (sa.1, f sa.1 sa.2))).mass =
      entropy ν.mass + ∑ s, ν.mass s * entropy (p.map (f s)).mass := by
  rw [ν.map_prod_keep_left p f]
  exact entropy_kernel ν (fun s => p.map (f s))

/-- Conditional entropy with the mixing variable retained is the average of the
conditional entropies in each component. Observables may depend on the mixing variable. -/
lemma conditionalMapEntropy_prod_keep_left (ν : Law S) (p : Law A)
    (X : S → A → B) (E : S → A → C) :
    (ν.prod p).conditionalMapEntropy (fun sa => X sa.1 sa.2)
      (fun sa => (sa.1,E sa.1 sa.2)) =
        ∑ s, ν.mass s * p.conditionalMapEntropy (X s) (E s) := by
  have hc := (ν.prod p).entropy_map_pair (fun sa => X sa.1 sa.2)
    (fun sa => (sa.1,E sa.1 sa.2))
  have ho := ν.entropy_map_prod_keep_left p E
  have hj := ν.entropy_map_prod_keep_left p (fun s a => (X s a,E s a))
  have heq : entropy ((ν.prod p).map (fun sa => (X sa.1 sa.2,(sa.1,E sa.1 sa.2)))).mass =
      entropy ((ν.prod p).map (fun sa => (sa.1,(X sa.1 sa.2,E sa.1 sa.2)))).mass := by
    let swap : B × (S × C) → S × (B × C) := fun t => (t.2.1,(t.1,t.2.2))
    have hi : Function.Injective swap := by
      intro a b h
      apply Prod.ext
      · exact congrArg (fun t => t.2.1) h
      · apply Prod.ext
        · exact congrArg (fun t => t.1) h
        · exact congrArg (fun t => t.2.2) h
    have h := ((ν.prod p).map
      (fun sa => (X sa.1 sa.2,(sa.1,E sa.1 sa.2)))).entropy_map_of_injective swap hi
    rw [map_map] at h
    exact h.symm
  rw [heq, hj, ho] at hc
  have hs : (∑ s, ν.mass s * entropy (p.map (fun a => (X s a,E s a))).mass) =
      (∑ s, ν.mass s * entropy (p.map (E s)).mass) +
      ∑ s, ν.mass s * p.conditionalMapEntropy (X s) (E s) := by
    simp_rw [p.entropy_map_pair, mul_add, Finset.sum_add_distrib]
  linarith

/-- Forgetting the independent mixing variable can only increase conditional entropy. -/
lemma average_conditionalMapEntropy_le (ν : Law S) (p : Law A)
    (X : S → A → B) (E : S → A → C) :
    (∑ s, ν.mass s * p.conditionalMapEntropy (X s) (E s)) ≤
      (ν.prod p).conditionalMapEntropy (fun sa => X sa.1 sa.2)
        (fun sa => E sa.1 sa.2) := by
  rw [← ν.conditionalMapEntropy_prod_keep_left p X E]
  exact (ν.prod p).conditionalMapEntropy_comp_le (fun sa => X sa.1 sa.2)
    (fun sa => (sa.1,E sa.1 sa.2)) Prod.snd

end FiniteEntropy.Law
