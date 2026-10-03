module

public import HittingTimeLooseHamilton.BootstrapPrivateSurvivingSplit

public section

/-! The collision error uses ambient N and retains the base deletion and all
original ports. Erasing the root from the obstruction set is essential when
the root is itself an original port. -/
noncomputable section
namespace LooseHamilton.BootstrapPrivateLinkGeometry
open Finset BootstrapBases
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M : Finset (Finset V)}

theorem collisions_card_le (hM : IsPairMatching M) (hr : 3 ≤ r) (b : Base M)
    (S q : Finset ↥(active b)) (x t : ↥(active b))
    (hS : S.card = r-3) (hq : q.card = 2) :
    (deletedRootCollisions r x.val ((exclusions b S q t).erase x.val)).card ≤
      (2*M.card+r+1) * (Fintype.card V-2).choose (r-2) := by
  exact (deletedRootCollisions_card_le (by omega) x.val _ (notMem_erase _ _)).trans
    (Nat.mul_le_mul_right _ ((card_erase_le (a := x.val) (s := exclusions b S q t)).trans
      (exclusions_card_le hM hr b S q t hS hq)))

theorem collisions_density_le (hM : IsPairMatching M) (hr : 3 ≤ r)
    (hN : 2 ≤ Fintype.card V) (b : Base M)
    (S q : Finset ↥(active b)) (x t : ↥(active b))
    (hS : S.card = r-3) (hq : q.card = 2) :
    rootLinkDensity r x.val
        (deletedRootCollisions r x.val ((exclusions b S q t).erase x.val)) ≤
      (2*M.card+r+1 : ℕ) * (r-1 : ℕ) / (Fintype.card V-1 : ℕ) := by
  have hc := (card_erase_le (a := x.val) (s := exclusions b S q t)).trans (exclusions_card_le hM hr b S q t hS hq)
  exact (deletedRootCollisions_density_le (by omega) hN x.val _
    (notMem_erase _ _)).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _))

end LooseHamilton.BootstrapPrivateLinkGeometry
