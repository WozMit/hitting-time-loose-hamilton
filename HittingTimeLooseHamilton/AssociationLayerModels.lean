module

public import HittingTimeLooseHamilton.AssociationIncidenceCounting
public import HittingTimeLooseHamilton.AssociationBadChoices
public import HittingTimeLooseHamilton.AssociationSurgeryStatistic

public section

/-! The forward and reverse incidence spaces in the exact association layers. -/
noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def associationLayer (r : ℕ) (d : V → ℕ) (y : V) (B : Finset V) (t : ℕ) :=
  {F : FixedDegreeState V r d // associationStatistic F.val y B = t}

@[expose] instance {r : ℕ} {d : V → ℕ} {y : V} {B : Finset V} {t : ℕ} :
    Fintype (associationLayer r d y B t) := by
  unfold associationLayer
  infer_instance

@[expose] def associationLayerCount (r : ℕ) (d : V → ℕ) (y : V) (B : Finset V) (t : ℕ) : ℕ :=
  Fintype.card (associationLayer r d y B t)

abbrev associationForwardIncidence (r : ℕ) (d : V → ℕ) (y : V) (B : Finset V) (t : ℕ) :=
  Σ F : associationLayer r d y B t,
    Σ s : ↥(associationSources F.val.val y B),
      ↥(associationGoodTargets F.val.val B s.val.1 s.val.2)

abbrev associationReverseIncidence (r : ℕ) (d : V → ℕ) (y : V) (B : Finset V) (t : ℕ) :=
  Σ F : associationLayer r d y B t, ↥(associationReverseLabels F.val.val y B)

end LooseHamilton
