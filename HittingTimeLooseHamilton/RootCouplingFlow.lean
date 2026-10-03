module

public import HittingTimeLooseHamilton.KahnConditioning
public import Mathlib

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators

/-- A unit upward flow on a finite chain. -/
@[expose] def rootFlowMass {n : ℕ} (p : FiniteEntropy.Law (Fin (n+1)))
    (s : Fin (n+1) → ℝ) (i j : Fin (n+1)) : ℝ :=
  (if j=i then p.mass i-s i else 0) + (if j.val=i.val+1 then s i else 0)

lemma rootFlowMass_row {n : ℕ} (p : FiniteEntropy.Law (Fin (n+1)))
    (s : Fin (n+1) → ℝ) (hlast : s (Fin.last n)=0) (i : Fin (n+1)) :
    ∑ j, rootFlowMass p s i j = p.mass i := by
  classical
  unfold rootFlowMass
  rw [sum_add_distrib]
  simp only [sum_ite_eq',mem_univ,if_true]
  by_cases hi : i.val < n
  · have hh : (∑ j : Fin (n+1), if j.val=i.val+1 then s i else 0) = s i := by
      rw [sum_eq_single (⟨i.val+1,by omega⟩ : Fin (n+1))]
      · simp
      · intro j hj hne
        have hn : j.val≠i.val+1 := fun he=>hne (Fin.ext he)
        exact if_neg hn
      · simp
    rw [hh]; ring
  · have he : i=Fin.last n := Fin.ext (by simp; omega)
    subst i
    simp [hlast]

lemma rootFlowMass_column_zero {n : ℕ} (p : FiniteEntropy.Law (Fin (n+1)))
    (s : Fin (n+1) → ℝ) :
    ∑ i, rootFlowMass p s i 0 = p.mass 0-s 0 := by
  classical
  simp [rootFlowMass,sum_add_distrib]

lemma rootFlowMass_column_succ {n : ℕ} (p : FiniteEntropy.Law (Fin (n+1)))
    (s : Fin (n+1) → ℝ) (j : Fin n) :
    ∑ i, rootFlowMass p s i j.succ = p.mass j.succ-s j.succ+s j.castSucc := by
  classical
  unfold rootFlowMass
  rw [sum_add_distrib]
  have hdiag : (∑ i : Fin (n+1), if j.succ=i then p.mass i-s i else 0) =
      p.mass j.succ-s j.succ := by simp
  rw [hdiag]
  congr 1
  rw [sum_eq_single j.castSucc]
  · simp
  · intro i hi hne
    have hn : j.succ.val≠i.val+1 := by
      intro he
      apply hne
      apply Fin.ext
      simp only [Fin.val_succ,Fin.coe_castSucc] at *
      omega
    exact if_neg hn
  · simp

/-- Explicit law on neighboring chain sites. -/
@[expose] def rootFlowCoupling {n : ℕ} (p : FiniteEntropy.Law (Fin (n+1)))
    (s : Fin (n+1) → ℝ) (hs0 : ∀i,0 ≤ s i) (hsp : ∀i,s i ≤ p.mass i)
    (hlast : s (Fin.last n)=0) : FiniteEntropy.Law (Fin (n+1) × Fin (n+1)) where
  mass x := rootFlowMass p s x.1 x.2
  nonneg x := by
    unfold rootFlowMass
    exact add_nonneg (ite_nonneg (sub_nonneg.mpr (hsp _)) (le_refl _))
      (ite_nonneg (hs0 _) (le_refl _))
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [rootFlowMass_row p s hlast]
    exact p.total

lemma rootFlowCoupling_first {n : ℕ} (p : FiniteEntropy.Law (Fin (n+1)))
    (s : Fin (n+1) → ℝ) (hs0 : ∀i,0 ≤ s i) (hsp : ∀i,s i ≤ p.mass i)
    (hlast : s (Fin.last n)=0) :
    (rootFlowCoupling p s hs0 hsp hlast).map Prod.fst = p := by
  classical
  apply FiniteEntropy.Law.ext_mass
  intro i
  simp only [FiniteEntropy.Law.map,FiniteEntropy.Law.event,rootFlowCoupling]
  rw [Fintype.sum_prod_type]
  rw [sum_eq_single i]
  · simpa using rootFlowMass_row p s hlast i
  · intro j hj hji; simp [hji]
  · simp

lemma rootFlowCoupling_support {n : ℕ} (p : FiniteEntropy.Law (Fin (n+1)))
    (s : Fin (n+1) → ℝ) (hs0 : ∀i,0 ≤ s i) (hsp : ∀i,s i ≤ p.mass i)
    (hlast : s (Fin.last n)=0) (x : Fin (n+1) × Fin (n+1))
    (hx : (rootFlowCoupling p s hs0 hsp hlast).mass x ≠ 0) :
    x.1.val  ≤  x.2.val ∧ x.2.val  ≤  x.1.val+1 := by
  change rootFlowMass p s x.1 x.2 ≠ 0 at hx
  by_cases he : x.2=x.1
  · simp [he]
  · have hn : x.2.val=x.1.val+1 := by
      by_contra hh
      simp [rootFlowMass,he,hh] at hx
    omega

end LooseHamilton
