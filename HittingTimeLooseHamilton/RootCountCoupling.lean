module

public import HittingTimeLooseHamilton.RootCouplingTails

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators

@[expose] def rootCountCoupling {n : ℕ} (p q : FiniteEntropy.Law (Fin (n+1)))
    (hlo : ∀ k,rootCountTail p k≤rootCountTail q k)
    (hhi : ∀ k,rootCountTail q (k+1)≤rootCountTail p k) :
    FiniteEntropy.Law (Fin (n+1) × Fin (n+1)) :=
  rootFlowCoupling p (rootTailFlow p q) (rootTailFlow_nonneg p q hlo)
    (rootTailFlow_le_mass p q hhi) (rootTailFlow_last p q)

lemma rootCountCoupling_first {n : ℕ} (p q : FiniteEntropy.Law (Fin (n+1)))
    (hlo : ∀ k,rootCountTail p k≤rootCountTail q k)
    (hhi : ∀ k,rootCountTail q (k+1)≤rootCountTail p k) :
    (rootCountCoupling p q hlo hhi).map Prod.fst=p :=
  rootFlowCoupling_first _ _ _ _ _

lemma rootCountCoupling_second {n : ℕ} (p q : FiniteEntropy.Law (Fin (n+1)))
    (hlo : ∀ k,rootCountTail p k≤rootCountTail q k)
    (hhi : ∀ k,rootCountTail q (k+1)≤rootCountTail p k) :
    (rootCountCoupling p q hlo hhi).map Prod.snd=q := by
  classical
  apply FiniteEntropy.Law.ext_mass
  intro j
  simp only [FiniteEntropy.Law.map,FiniteEntropy.Law.event,rootCountCoupling,rootFlowCoupling]
  rw [Fintype.sum_prod_type,sum_comm,sum_eq_single j]
  · simp only [if_true]
    refine Fin.cases ?_ (fun k=>?_) j
    · rw [rootFlowMass_column_zero,rootTailFlow_balance_zero]
    · rw [rootFlowMass_column_succ,rootTailFlow_balance_succ]
  · intro k hk hkj
    simp [hkj]
  · simp

lemma rootCountCoupling_support {n : ℕ} (p q : FiniteEntropy.Law (Fin (n+1)))
    (hlo : ∀ k,rootCountTail p k≤rootCountTail q k)
    (hhi : ∀ k,rootCountTail q (k+1)≤rootCountTail p k)
    (x : Fin (n+1) × Fin (n+1))
    (hx : (rootCountCoupling p q hlo hhi).mass x ≠ 0) :
    x.1.val ≤ x.2.val ∧ x.2.val ≤ x.1.val+1 :=
  rootFlowCoupling_support _ _ _ _ _ x hx

/-- Explicit finite coupling of interlaced count distributions. No coupling
existence or stochastic-order assumption beyond the stated tail inequalities
is hidden in this construction. -/
theorem exists_root_count_coupling {n : ℕ} (p q : FiniteEntropy.Law (Fin (n+1)))
    (hlo : ∀ k,rootCountTail p k≤rootCountTail q k)
    (hhi : ∀ k,rootCountTail q (k+1)≤rootCountTail p k) :
    ∃ π : FiniteEntropy.Law (Fin (n+1) × Fin (n+1)),
      π.map Prod.fst=p ∧ π.map Prod.snd=q ∧
      ∀ x, π.mass x≠0 → x.1.val≤x.2.val ∧ x.2.val≤x.1.val+1 :=
  ⟨rootCountCoupling p q hlo hhi,rootCountCoupling_first p q hlo hhi,
    rootCountCoupling_second p q hlo hhi,rootCountCoupling_support p q hlo hhi⟩

end LooseHamilton
