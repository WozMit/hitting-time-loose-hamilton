module

public import HittingTimeLooseHamilton.KahnStatement
public import HittingTimeLooseHamilton.KahnRandomOrder
public import HittingTimeLooseHamilton.KahnConditioning
public import HittingTimeLooseHamilton.KahnRevealCard
public import HittingTimeLooseHamilton.KahnMatchingOrder
public import Mathlib.Data.Fintype.Sum

public section

open scoped BigOperators

noncomputable section

namespace Kahn.MatchingLaw

open FiniteEntropy

variable {n r : ℕ} {H : Hypergraph n r}

/-- Tag known companions separately from sets of still-available vertices. -/
@[expose] def tagEvidence (e : Bool × Finset (Fin n)) : Finset (Fin n) ⊕ Finset (Fin n) :=
  if e.1 then Sum.inl e.2 else Sum.inr e.2

lemma tagEvidence_injective : Function.Injective (tagEvidence (n := n)) := by
  rintro ⟨b, Y⟩ ⟨c, Z⟩ h
  cases b <;> cases c <;> simp_all [tagEvidence]

@[expose] def taggedEvidence (σ : Equiv.Perm (Fin n)) (v : Fin n) (M : MatchingIn H) :
    Finset (Fin n) ⊕ Finset (Fin n) :=
  tagEvidence (M.val.evidence σ v)

@[expose] def taggedEvidenceFromPast (r : ℕ) (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (p : Fin n → Option (Finset (Fin n))) : Finset (Fin n) ⊕ Finset (Fin n) :=
  tagEvidence (PerfectMatching.evidenceFromPast r σ v p)

lemma taggedEvidenceFromPast_eq (σ : Equiv.Perm (Fin n)) (v : Fin n) (M : MatchingIn H) :
    taggedEvidenceFromPast r σ v (M.val.past σ v) = taggedEvidence σ v M := by
  simp [taggedEvidenceFromPast, taggedEvidence, PerfectMatching.evidenceFromPast_eq]

lemma taggedEvidence_inl_iff (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (M : MatchingIn H) (Y : Finset (Fin n)) :
    taggedEvidence σ v M = Sum.inl Y ↔
      v ∈ M.val.earlierEdges σ v ∧ M.val.companion v = Y := by
  classical
  by_cases hv : v ∈ M.val.earlierEdges σ v <;>
    simp [taggedEvidence, tagEvidence, PerfectMatching.evidence, hv]

lemma taggedEvidence_inr_iff (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (M : MatchingIn H) (Z : Finset (Fin n)) :
    taggedEvidence σ v M = Sum.inr Z ↔
      v ∉ M.val.earlierEdges σ v ∧ M.val.available σ v = Z := by
  classical
  by_cases hv : v ∈ M.val.earlierEdges σ v <;>
    simp [taggedEvidence, tagEvidence, PerfectMatching.evidence, hv]

/-- The independent uniform vertex order and the arbitrary matching law. -/
@[expose] def orderLaw (μ : Law (MatchingIn H)) : Law (Equiv.Perm (Fin n) × MatchingIn H) :=
  (uniform (A := Equiv.Perm (Fin n))).prod μ

/-- The actual joint law to which the tagged-evidence entropy inequality applies. -/
@[expose] def jointRevealLaw (μ : Law (MatchingIn H)) (v : Fin n) :
    Law (Finset (Fin n) × (Finset (Fin n) ⊕ Finset (Fin n))) :=
  (orderLaw μ).map (fun z => (z.2.val.companion v, taggedEvidence z.1 v z.2))

lemma orderLaw_event (μ : Law (MatchingIn H))
    (E : Equiv.Perm (Fin n) × MatchingIn H → Prop) :
    (orderLaw μ).event E = ∑ M, μ.mass M *
      (uniform (A := Equiv.Perm (Fin n))).event (fun σ => E (σ, M)) := by
  classical
  simp only [orderLaw, Law.prod, Law.event]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : E (σ, M) <;> simp [h, mul_comm]

lemma jointRevealLaw_mass (μ : Law (MatchingIn H)) (v : Fin n)
    (Y : Finset (Fin n)) (e : Finset (Fin n) ⊕ Finset (Fin n)) :
    (jointRevealLaw μ v).mass (Y, e) =
      (orderLaw μ).event (fun z =>
        z.2.val.companion v = Y ∧ taggedEvidence z.1 v z.2 = e) := by
  classical
  simp [jointRevealLaw, Law.map, Law.event, Prod.mk.injEq]
  congr 1
  funext z
  by_cases h : z.2.val.companion v = Y ∧ taggedEvidence z.1 v z.2 = e <;> simp [h]

lemma fst_jointRevealLaw (μ : Law (MatchingIn H)) (v : Fin n) :
    (jointRevealLaw μ v).fst = marginal μ v := by
  classical
  apply Law.ext_mass
  intro Y
  change (∑ e, (jointRevealLaw μ v).mass (Y, e)) = _
  simp_rw [jointRevealLaw_mass, Law.event]
  rw [Finset.sum_comm]
  calc
    _ = (orderLaw μ).event (fun z => z.2.val.companion v = Y) := by
      unfold Law.event
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z.2.val.companion v = Y <;> simp [hz]
    _ = _ := ?_
  change ((uniform (A := Equiv.Perm (Fin n))).prod μ).event
    (fun z => z.2.val.companion v = Y) = _
  rw [Law.event_prod_sum]
  change (∑ σ : Equiv.Perm (Fin n),
    (uniform (A := Equiv.Perm (Fin n))).mass σ * (marginal μ v).mass Y) = _
  rw [← Finset.sum_mul, (uniform (A := Equiv.Perm (Fin n))).total, one_mul]

/-- The known branch determines the companion exactly. -/
lemma jointRevealLaw_known_offdiagonal (μ : Law (MatchingIn H)) (v : Fin n)
    (Y Z : Finset (Fin n)) (hne : Y ≠ Z) :
    (jointRevealLaw μ v).mass (Y, Sum.inl Z) = 0 := by
  rw [jointRevealLaw_mass]
  apply Law.event_eq_zero_of_false
  rintro ⟨σ, M⟩ ⟨hY, hZ⟩
  exact hne (hY.symm.trans ((taggedEvidence_inl_iff σ v M Z).mp hZ).2)

/-- An unknown companion is always a subset of the available vertex set. -/
lemma jointRevealLaw_incompatible (μ : Law (MatchingIn H)) (v : Fin n)
    (Y Z : Finset (Fin n)) (hnot : ¬ Y ⊆ Z) :
    (jointRevealLaw μ v).mass (Y, Sum.inr Z) = 0 := by
  rw [jointRevealLaw_mass]
  apply Law.event_eq_zero_of_false
  rintro ⟨σ, M⟩ ⟨hY, hZ⟩
  obtain ⟨hfirst, hav⟩ := (taggedEvidence_inr_iff σ v M Z).mp hZ
  apply hnot
  rw [← hY, ← hav]
  exact M.val.companion_subset_available σ v hfirst

lemma jointRevealLaw_unknown_row_event (μ : Law (MatchingIn H)) (v : Fin n)
    (Y : Finset (Fin n)) :
    (∑ Z, (jointRevealLaw μ v).mass (Y, Sum.inr Z)) =
      (orderLaw μ).event (fun z => z.2.val.companion v = Y ∧
        v ∉ z.2.val.earlierEdges z.1 v) := by
  classical
  simp_rw [jointRevealLaw_mass, Law.event]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hv : v ∈ z.2.val.earlierEdges z.1 v <;>
    by_cases hY : z.2.val.companion v = Y <;>
      simp [taggedEvidence, tagEvidence, PerfectMatching.evidence, hv, hY]

/-- Group available sets by the number of unexposed blocks, with index zero
corresponding to one unexposed block. The arbitrary modular fallback affects
only sizes that do not arise in the unknown branch. -/
@[expose] def revealGroup (hm : 0 < n / r) (Z : Finset (Fin n)) : Fin (n / r) :=
  ⟨((Z.card + 1) / r - 1) % (n / r), Nat.mod_lt _ hm⟩

lemma matching_card_eq_div (M : PerfectMatching n r) (hr : 0 < r) :
    M.val.card = n / r := by
  calc
    M.val.card = (M.val.card * r) / r := (Nat.mul_div_left _ hr).symm
    _ = n / r := congrArg (fun a : ℕ => a / r) M.card_blocks_mul.symm

lemma revealGroup_available_val (hr : 0 < r) (hm : 0 < n / r)
    (M : PerfectMatching n r) (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (hu : v ∉ M.earlierEdges σ v) :
    (revealGroup hm (M.available σ v)).val = (M.lateBlocks σ v).card - 1 := by
  have ht := M.lateBlocks_card_pos σ v hu
  have hle := M.lateBlocks_card_le σ v
  rw [matching_card_eq_div M hr] at hle
  have hprod : 0 < (M.lateBlocks σ v).card * r := Nat.mul_pos ht hr
  change (((M.available σ v).card + 1) / r - 1) % (n / r) = _
  rw [M.available_card σ v hu, Nat.sub_add_cancel hprod, Nat.mul_div_left _ hr]
  apply Nat.mod_eq_of_lt
  omega

lemma revealGroup_available_iff (hr : 0 < r) (hm : 0 < n / r)
    (M : PerfectMatching n r) (σ : Equiv.Perm (Fin n)) (v : Fin n)
    (hu : v ∉ M.earlierEdges σ v) (i : Fin (n / r)) :
    revealGroup hm (M.available σ v) = i ↔ (M.lateBlocks σ v).card = i.val + 1 := by
  rw [Fin.ext_iff, revealGroup_available_val hr hm M σ v hu]
  have ht := M.lateBlocks_card_pos σ v hu
  omega

lemma jointRevealLaw_unknown_group_event (μ : Law (MatchingIn H)) (v : Fin n)
    (hm : 0 < n / r) (Y : Finset (Fin n)) (i : Fin (n / r)) :
    (∑ Z, if revealGroup hm Z = i then (jointRevealLaw μ v).mass (Y, Sum.inr Z) else 0) =
      (orderLaw μ).event (fun z => z.2.val.companion v = Y ∧
        (v ∉ z.2.val.earlierEdges z.1 v ∧ revealGroup hm (z.2.val.available z.1 v) = i)) := by
  classical
  rw [← Finset.sum_filter]
  simp_rw [jointRevealLaw_mass, Law.event]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hv : v ∈ z.2.val.earlierEdges z.1 v <;>
    by_cases hY : z.2.val.companion v = Y <;>
      simp [taggedEvidence, tagEvidence, PerfectMatching.evidence, hv, hY,
        Finset.sum_filter]

lemma uniform_group_probability (hr : 0 < r) (hm : 0 < n / r)
    (M : PerfectMatching n r) (v : Fin n) (i : Fin (n / r)) :
    (uniform (A := Equiv.Perm (Fin n))).event (fun σ =>
      v ∉ M.earlierEdges σ v ∧ revealGroup hm (M.available σ v) = i) = 1 / (n : ℝ) := by
  classical
  letI : NeZero r := ⟨hr.ne'⟩
  have hc : Fintype.card M.Block = n / r := by
    simpa using matching_card_eq_div M hr
  let k : Fin (Fintype.card M.Block) := ⟨n / r - 1 - i.val, by rw [hc]; omega⟩
  have hk : Fintype.card M.Block - k.val = i.val + 1 := by dsimp [k]; omega
  rw [Law.uniform_event]
  have hp := M.unknown_card_probability v k
  rw [hk] at hp
  refine Eq.trans ?_ hp
  apply congrArg (fun T : Finset (Equiv.Perm (Fin n)) =>
    (T.card : ℝ) / Fintype.card (Equiv.Perm (Fin n)))
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hu, hg⟩
    exact ⟨hu, (revealGroup_available_iff hr hm M σ v hu i).mp hg⟩
  · rintro ⟨hu, hg⟩
    exact ⟨hu, (revealGroup_available_iff hr hm M σ v hu i).mpr hg⟩

lemma uniform_group_survival_probability (hr : 0 < r) (hm : 0 < n / r)
    (M : PerfectMatching n r) (v : Fin n) (i : Fin (n / r))
    (Y : Finset (Fin n)) (hvY : v ∉ Y) :
    (uniform (A := Equiv.Perm (Fin n))).event (fun σ =>
      (v ∉ M.earlierEdges σ v ∧ revealGroup hm (M.available σ v) = i) ∧
        Y ⊆ M.available σ v) =
      (1 / (n : ℝ)) * (i.val.descFactorial (M.tau v Y) : ℝ) /
        (n / r - 1).descFactorial (M.tau v Y) := by
  classical
  letI : NeZero r := ⟨hr.ne'⟩
  have hc : Fintype.card M.Block = n / r := by
    simpa using matching_card_eq_div M hr
  let k : Fin (Fintype.card M.Block) := ⟨n / r - 1 - i.val, by rw [hc]; omega⟩
  have hk : Fintype.card M.Block - k.val = i.val + 1 := by dsimp [k]; omega
  have hk' : Fintype.card M.Block - 1 - k.val = i.val := by dsimp [k]; omega
  rw [Law.uniform_event]
  have hp := M.unknown_card_survival_probability v k Y hvY
  rw [hk, hk', hc] at hp
  refine Eq.trans ?_ hp
  apply congrArg (fun T : Finset (Equiv.Perm (Fin n)) =>
    (T.card : ℝ) / Fintype.card (Equiv.Perm (Fin n)))
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hu, hg⟩, hY⟩
    exact ⟨⟨hu, (revealGroup_available_iff hr hm M σ v hu i).mp hg⟩, hY⟩
  · rintro ⟨⟨hu, hg⟩, hY⟩
    exact ⟨⟨hu, (revealGroup_available_iff hr hm M σ v hu i).mpr hg⟩, hY⟩

lemma jointRevealLaw_unknown_group (μ : Law (MatchingIn H))
    (hr : 0 < r) (hm : 0 < n / r) (v : Fin n)
    (Y : Finset (Fin n)) (i : Fin (n / r)) :
    (∑ Z, if revealGroup hm Z = i then (jointRevealLaw μ v).mass (Y, Sum.inr Z) else 0) =
      (marginal μ v).mass Y * (1 / (n : ℝ)) := by
  classical
  rw [jointRevealLaw_unknown_group_event, orderLaw_event]
  simp only [Law.event_const_and, uniform_group_probability hr hm]
  unfold marginal Law.map Law.event
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro M _
  by_cases h : M.val.companion v = Y <;> simp [h]

end Kahn.MatchingLaw
