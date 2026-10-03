module

public import HittingTimeLooseHamilton.EndpointCutModels
public import HittingTimeLooseHamilton.EndpointCutBounds

public section

noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def endpointCutMate (M : Finset (Finset V)) (fallback u : V) : V :=
  if h : ∃ v, u ≠ v ∧ ({u, v} : Finset V) ∈ M then h.choose else fallback

theorem endpointCutMate_eq {M : Finset (Finset V)}
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) (fallback u v : V)
    (huv : u ≠ v) (hm : ({u, v} : Finset V) ∈ M) :
    endpointCutMate M fallback u = v := by
  have hex : ∃ w, u ≠ w ∧ ({u, w} : Finset V) ∈ M := ⟨v, huv, hm⟩
  unfold endpointCutMate
  rw [dif_pos hex]
  have hc := hex.choose_spec
  have heq : ({u, hex.choose} : Finset V) = {u, v} := by
    by_contra hne
    have hd := hM hc.2 hm hne
    have hu1 : u ∈ ({u, hex.choose} : Finset V) := by simp
    exact disjoint_left.mp hd hu1 (by simp)
  have hv : hex.choose ∈ ({u, v} : Finset V) := heq ▸ (by simp)
  simpa [Ne.symm hc.1] using hv

private theorem privateBlock_recover {B R : Finset V} (h : Disjoint R B) :
    (B ∪ R) \ B = R := by
  ext v
  simp only [mem_sdiff, mem_union]
  constructor
  · rintro ⟨hmem, hn⟩
    exact hmem.resolve_left hn
  · intro hv
    exact ⟨Or.inr hv, fun hb => disjoint_left.mp h hv hb⟩

theorem endpointCutLabelsI_card_le {r : ℕ} {M G H : Finset (Finset V)}
    {P : Finset V} {y z : V} (hG : G ⊆ H) :
    (endpointCutLabelsI r M G P y z).card ≤ (endpointCutFirstLabels H y).card := by
  apply card_le_card_of_injOn (fun l => (l.edge y, l.1))
  · intro l hl
    have h := (mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hl
    apply mem_endpointCutFirstLabels.mpr
    refine ⟨hG h.edge_mem, ?_, ?_, ?_⟩
    · simp [EndpointCutLabelI.edge]
    · simp [EndpointCutLabelI.edge]
    · intro heq
      exact h.endpoint_fresh (by simp [heq])
  · intro l hl k hk heq
    have h := (mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hl
    have h' := (mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hk
    have ha : l.1 = k.1 := congrArg Prod.snd heq
    have hd : Disjoint l.2 ({y, l.1} : Finset V) :=
      h.private_disjoint.mono_right (by intro v hv; simp only [mem_insert, mem_singleton] at hv; rcases hv with rfl | rfl <;> simp)
    have hd' : Disjoint k.2 ({y, k.1} : Finset V) :=
      h'.private_disjoint.mono_right (by intro v hv; simp only [mem_insert, mem_singleton] at hv; rcases hv with rfl | rfl <;> simp)
    apply Prod.ext ha
    have he : l.edge y = k.edge y := congrArg Prod.fst heq
    rw [← privateBlock_recover hd, ← privateBlock_recover hd']
    change l.edge y \ {y, l.1} = k.edge y \ {y, k.1}
    rw [he, ha]

theorem endpointCutLabelsII_card_le {r : ℕ} {M G H : Finset (Finset V)}
    {P : Finset V} {y z : V} (hG : G ⊆ H)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) (hy : y ∉ originalPorts M) :
    (endpointCutLabelsII r M G P y z).card ≤
      (endpointCutSecondLabels H y (endpointCutMate M y)).card := by
  have ports : ∀ l, EndpointCutLegalII r M G P y z l →
      l.1 ∈ originalPorts M ∧ l.2.1 ∈ originalPorts M := by
    intro l h
    constructor <;> apply mem_biUnion.mpr <;>
      exact ⟨l.oldMarker, h.oldMarker_mem, by simp [EndpointCutLabelII.oldMarker]⟩
  have mate_eq : ∀ l, EndpointCutLegalII r M G P y z l →
      endpointCutMate M y l.1 = l.2.1 := by
    intro l h
    exact endpointCutMate_eq hM y l.1 l.2.1 h.ports_ne h.oldMarker_mem
  apply card_le_card_of_injOn
    (fun l => ((l.firstEdge y, l.1), (l.secondEdge, l.2.2.1)))
  · intro l hl
    have h := (mem_endpointCutLabelsII _ _ _ _ _ _ _).mp hl
    apply mem_endpointCutSecondLabels.mpr
    constructor
    · apply mem_endpointCutFirstLabels.mpr
      refine ⟨hG h.firstEdge_mem, ?_, ?_, ?_⟩
      · simp [EndpointCutLabelII.firstEdge]
      · simp [EndpointCutLabelII.firstEdge]
      · intro heq
        exact hy (heq ▸ (ports l h).1)
    · rw [mate_eq l h]
      apply mem_endpointCutFirstLabels.mpr
      refine ⟨hG h.secondEdge_mem, ?_, ?_, ?_⟩
      · simp [EndpointCutLabelII.secondEdge]
      · simp [EndpointCutLabelII.secondEdge]
      · intro heq
        apply h.endpoint_fresh
        have hp := (ports l h).2
        simp [heq, hp]
  · intro l hl k hk heq
    have h := (mem_endpointCutLabelsII _ _ _ _ _ _ _).mp hl
    have h' := (mem_endpointCutLabelsII _ _ _ _ _ _ _).mp hk
    have hu : l.1 = k.1 := congrArg (fun a => a.1.2) heq
    have ha : l.2.2.1 = k.2.2.1 := congrArg (fun a => a.2.2) heq
    have hv : l.2.1 = k.2.1 := by rw [← mate_eq l h, ← mate_eq k h', hu]
    have recover : ∀ j, EndpointCutLegalII r M G P y z j →
        j.firstEdge y \ {y, j.1} = j.2.2.2.1 ∧
        j.secondEdge \ {j.2.1, j.2.2.1} = j.2.2.2.2 := by
      intro j hj
      have hp := ports j hj
      constructor
      · apply privateBlock_recover
        apply hj.first_private_disjoint.mono_right
        intro a ha
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl
        · simp
        · simp [hp.1]
      · apply privateBlock_recover
        apply hj.second_private_disjoint.mono_right
        intro a ha
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl
        · simp [hp.2]
        · simp
    have he1 : l.firstEdge y = k.firstEdge y := congrArg (fun a => a.1.1) heq
    have he2 : l.secondEdge = k.secondEdge := congrArg (fun a => a.2.1) heq
    have hR : l.2.2.2.1 = k.2.2.2.1 := by
      rw [← (recover l h).1, ← (recover k h').1, hu,
        he1]
    have hT : l.2.2.2.2 = k.2.2.2.2 := by
      rw [← (recover l h).2, ← (recover k h').2, hv, ha,
        he2]
    exact Prod.ext hu (Prod.ext hv (Prod.ext ha (Prod.ext hR hT)))

theorem legalEndpointCutLabels_card_le {r Δ : ℕ} {M G H : Finset (Finset V)}
    {P : Finset V} {y z : V} (hG : G ⊆ H) (hH : H ⊆ completeEdges V r)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) (hy : y ∉ originalPorts M)
    (hΔ : ∀ v, vertexDegree H v ≤ Δ) :
    (endpointCutLabelsI r M G P y z).card + (endpointCutLabelsII r M G P y z).card ≤
      (r - 1) * vertexDegree H y + (r - 1)^2 * vertexDegree H y * Δ :=
  (Nat.add_le_add (endpointCutLabelsI_card_le hG)
    (endpointCutLabelsII_card_le hG hM hy)).trans
    (endpointCutLabels_card_le hH hΔ y (endpointCutMate M y))

theorem legalEndpointCutLabels_card_le_polynomial {r : ℕ} {M G H : Finset (Finset V)}
    {P : Finset V} {y z : V} (hr : 1 ≤ r) (hG : G ⊆ H) (hH : H ⊆ completeEdges V r)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) (hy : y ∉ originalPorts M) :
    (endpointCutLabelsI r M G P y z).card + (endpointCutLabelsII r M G P y z).card ≤
      endpointCutConstant r * (Fintype.card V) ^ (2 * r - 2) :=
  (Nat.add_le_add (endpointCutLabelsI_card_le hG)
    (endpointCutLabelsII_card_le hG hM hy)).trans
    (endpointCutLabels_card_le_polynomial hr hH y (endpointCutMate M y))

end LooseHamilton
