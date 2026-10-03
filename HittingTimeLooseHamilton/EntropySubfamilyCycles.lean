module

public import HittingTimeLooseHamilton.EntropySubfamily
public import HittingTimeLooseHamilton.BiasedRoleStatement

public section

/-! Polynomial subfamilies of the actual connected mixed-cycle space.
The ambient cycle space and the host parameters are unchanged by restriction. -/
noncomputable section
namespace LooseHamilton
namespace BiasedRoleInstance
open FiniteEntropy
variable {r : ℕ}

/-- The same host and rooted matching with the uniform law on a specified
nonempty subfamily of actual connected spanning mixed cycles. -/
@[expose] def withUniformSubfamily (D : BiasedRoleInstance r)
    (S : Finset (BiasedCycleState r D.markers D.host)) (hS : S.Nonempty) :
    BiasedRoleInstance r :=
  { D with cycleLaw := uniformSubfamily S hS }

/-- The finite entropy hypothesis needed for Theorem 6.1 follows from the
original log count and a polynomial relative-size bound. -/
theorem withUniformSubfamily_entropyBound (D : BiasedRoleInstance r)
    (F S : Finset (BiasedCycleState r D.markers D.host))
    (hF : F.Nonempty) (hS : S.Nonempty) (A ξ : ℝ)
    (hN : 0 < D.N)
    (hsize : (D.N : ℝ) ^ (-A) ≤ (S.card : ℝ) / F.card)
    (hbase : (D.k : ℝ) * Real.log (((r : ℝ) - 1) * D.μ) -
      ((r : ℝ) - 1) * D.k - ξ * D.N ≤ Real.log F.card) :
    (D.withUniformSubfamily S hS).entropyBound
      (ξ + A * Real.log D.N / D.N) := by
  exact entropy_uniformSubfamily_lower_bound F S hF hS D.N A
    ((D.k : ℝ) * Real.log (((r : ℝ) - 1) * D.μ) - ((r : ℝ) - 1) * D.k)
    ξ (Nat.cast_pos.mpr hN) hsize hbase

/-- A prescribed finite label class is a subfamily. In applications the label
can record relative directions of boundedly many markers. -/
@[expose] def labelClass {Λ : Type*} [DecidableEq Λ] (D : BiasedRoleInstance r)
    (F : Finset (BiasedCycleState r D.markers D.host))
    (label : BiasedCycleState r D.markers D.host → Λ) (value : Λ) :=
  F.filter (fun C => label C = value)

/-- Prescribing directions has the same entropy cost whenever the retained
class has the stated polynomial relative size. A cardinality condition is
explicit: no equidistribution across arbitrary sparse-host classes is assumed. -/
theorem labelClass_entropyBound {Λ : Type*} [DecidableEq Λ]
    (D : BiasedRoleInstance r)
    (F : Finset (BiasedCycleState r D.markers D.host)) (hF : F.Nonempty)
    (label : BiasedCycleState r D.markers D.host → Λ) (value : Λ)
    (hclass : (D.labelClass F label value).Nonempty) (A ξ : ℝ)
    (hN : 0 < D.N)
    (hsize : (D.N : ℝ) ^ (-A) ≤
      ((D.labelClass F label value).card : ℝ) / F.card)
    (hbase : (D.k : ℝ) * Real.log (((r : ℝ) - 1) * D.μ) -
      ((r : ℝ) - 1) * D.k - ξ * D.N ≤ Real.log F.card) :
    (D.withUniformSubfamily (D.labelClass F label value) hclass).entropyBound
      (ξ + A * Real.log D.N / D.N) :=
  D.withUniformSubfamily_entropyBound F _ hF hclass A ξ hN hsize hbase

end BiasedRoleInstance
end LooseHamilton
