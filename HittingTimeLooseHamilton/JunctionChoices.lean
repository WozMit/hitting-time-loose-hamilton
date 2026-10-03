module

public import HittingTimeLooseHamilton.Setup
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi

public section

/-! # Ordinary junction and marker-direction choices
These are the binomial and power-of-two factors in Proposition 2.2.
-/
noncomputable section
namespace LooseHamilton
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary junctions are chosen outside all marked ports. -/
@[expose] def ordinaryJunctionChoices (markers : Finset (Finset V)) (k : ℕ) :
    Finset (Finset V) :=
  (Finset.univ \ originalPorts markers).powersetCard (k - markers.card)

@[simp] theorem mem_ordinaryJunctionChoices (markers : Finset (Finset V))
    (k : ℕ) (J : Finset V) :
    J ∈ ordinaryJunctionChoices markers k ↔
      J ⊆ Finset.univ \ originalPorts markers ∧ J.card = k - markers.card := by
  simp [ordinaryJunctionChoices]

/-- The binomial factor in the complete-host enumeration. -/
theorem ordinaryJunctionChoices_card {markers : Finset (Finset V)}
    (hM : IsPairMatching markers) (k : ℕ) :
    (ordinaryJunctionChoices markers k).card =
      (Fintype.card V - 2 * markers.card).choose (k - markers.card) := by
  rw [ordinaryJunctionChoices, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hM.ports_card]

/-- After fixing a direction of the root marker, choose a first endpoint of
all remaining markers. A pair has exactly two such choices. -/
@[expose] def MarkerDirections (markers : Finset (Finset V)) (root : Finset V) :=
  ∀ e : ↥(markers.erase root), ↥(e.val)

@[expose] instance {markers : Finset (Finset V)} {root : Finset V} :
    Fintype (MarkerDirections markers root) := by
  unfold MarkerDirections
  infer_instance

/-- The factor 2^(s-1); the root orientation is fixed, not counted. -/
theorem markerDirections_card {markers : Finset (Finset V)} {root : Finset V}
    (hM : IsPairMatching markers) (hroot : root ∈ markers) :
    Fintype.card (MarkerDirections markers root) = 2 ^ (markers.card - 1) := by
  unfold MarkerDirections
  rw [Fintype.card_pi]
  have hpair (e : ↥(markers.erase root)) : Fintype.card ↥(e.val) = 2 := by
    rw [Fintype.card_coe]
    exact hM.1 e.val (Finset.mem_of_mem_erase e.property)
  simp_rw [hpair]
  simp [Finset.card_erase_of_mem hroot]

/-- The unchosen vertices form the private pool of size (r-2)k. -/
theorem privatePool_card {markers : Finset (Finset V)}
    (hM : IsPairMatching markers) {r k : ℕ} (hr : 3 ≤ r)
    (hsk : markers.card ≤ k)
    (hN : Fintype.card V = (r - 1) * k + markers.card)
    {J : Finset V} (hJ : J ∈ ordinaryJunctionChoices markers k) :
    (Finset.univ \ (originalPorts markers ∪ J)).card = (r - 2) * k := by
  obtain ⟨hsub, hc⟩ := (mem_ordinaryJunctionChoices markers k J).mp hJ
  have hd : Disjoint (originalPorts markers) J := by
    apply Finset.disjoint_left.mpr
    intro v hv hj
    exact (Finset.mem_sdiff.mp (hsub hj)).2 hv
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Finset.card_union_of_disjoint hd, hM.ports_card, hc, hN]
  have hr' : r - 1 = (r - 2) + 1 := by omega
  rw [hr', Nat.add_mul, one_mul]
  omega

end LooseHamilton
