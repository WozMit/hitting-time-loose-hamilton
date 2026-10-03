module

public import HittingTimeLooseHamilton.RootCouplingFlow

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

@[expose] def rootCountTail {n : ℕ} (p : FiniteEntropy.Law (Fin (n+1))) (k : ℕ) : ℝ :=
  p.event (fun i=>k ≤ i.val)

lemma rootCountTail_zero {n : ℕ} (p : FiniteEntropy.Law (Fin (n+1))) :
    rootCountTail p 0=1 := by simp [rootCountTail,FiniteEntropy.Law.event,p.total]

lemma rootCountTail_end {n : ℕ} (p : FiniteEntropy.Law (Fin (n+1))) :
    rootCountTail p (n+1)=0 := by
  apply p.event_eq_zero_of_false
  intro i hi
  omega

lemma rootCountTail_step {n : ℕ} (p : FiniteEntropy.Law (Fin (n+1))) (i : Fin (n+1)) :
    rootCountTail p i.val = p.mass i+rootCountTail p (i.val+1) := by
  classical
  have he : ∀ j : Fin (n+1), (if i.val≤j.val then p.mass j else 0)=
      (if j=i then p.mass j else 0)+(if i.val+1≤j.val then p.mass j else 0) := by
    intro j
    by_cases hij : j=i
    · subst j; simp
    · have hv : j.val≠i.val := fun h=>hij (Fin.ext h)
      by_cases hlt : i.val<j.val
      · simp [hij,show i.val≤j.val by omega,show i.val+1≤j.val by omega]
      · simp [hij,show ¬i.val≤j.val by omega,show ¬i.val+1≤j.val by omega]
  unfold rootCountTail FiniteEntropy.Law.event
  calc
    _ = ∑ j : Fin (n+1), ((if j=i then p.mass j else 0)+(if i.val+1≤j.val then p.mass j else 0)) := by
      apply sum_congr rfl
      intro j hj
      convert he j using 1 <;> split_ifs <;> rfl
    _ = _ := by
      rw [sum_add_distrib]
      simp only [sum_ite_eq',mem_univ,if_true]
      congr 1
      apply sum_congr rfl
      intro j hj
      split_ifs <;> rfl

@[expose] def rootTailFlow {n : ℕ} (p q : FiniteEntropy.Law (Fin (n+1))) (i : Fin (n+1)) : ℝ :=
  rootCountTail q (i.val+1)-rootCountTail p (i.val+1)

lemma rootTailFlow_nonneg {n : ℕ} (p q : FiniteEntropy.Law (Fin (n+1)))
    (hlo : ∀ k,rootCountTail p k≤rootCountTail q k) (i : Fin (n+1)) :
    0≤rootTailFlow p q i := sub_nonneg.mpr (hlo _)

lemma rootTailFlow_le_mass {n : ℕ} (p q : FiniteEntropy.Law (Fin (n+1)))
    (hhi : ∀ k,rootCountTail q (k+1)≤rootCountTail p k) (i : Fin (n+1)) :
    rootTailFlow p q i≤p.mass i := by
  have hs := rootCountTail_step p i
  have hh := hhi i.val
  unfold rootTailFlow
  linarith

lemma rootTailFlow_last {n : ℕ} (p q : FiniteEntropy.Law (Fin (n+1))) :
    rootTailFlow p q (Fin.last n)=0 := by
  simp [rootTailFlow,rootCountTail_end]

lemma rootTailFlow_balance_zero {n : ℕ} (p q : FiniteEntropy.Law (Fin (n+1))) :
    p.mass 0-rootTailFlow p q 0=q.mass 0 := by
  have hp := rootCountTail_step p 0
  have hq := rootCountTail_step q 0
  simp only [Fin.val_zero,rootCountTail_zero] at hp hq
  unfold rootTailFlow
  simp only [Fin.val_zero]
  linarith

lemma rootTailFlow_balance_succ {n : ℕ} (p q : FiniteEntropy.Law (Fin (n+1))) (j : Fin n) :
    p.mass j.succ-rootTailFlow p q j.succ+rootTailFlow p q j.castSucc=q.mass j.succ := by
  have hp := rootCountTail_step p j.succ
  have hq := rootCountTail_step q j.succ
  unfold rootTailFlow
  simp only [Fin.val_succ,Fin.coe_castSucc] at *
  linarith

end LooseHamilton
