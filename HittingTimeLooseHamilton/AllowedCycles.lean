module

public import HittingTimeLooseHamilton.CompleteHostDecode
public import HittingTimeLooseHamilton.Models

public section
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r k : ℕ} {markers : Finset (Finset V)} {root : Finset V}

omit [Fintype V] in
theorem pair_private_allowed_iff (ports P : Finset V) (x y : V)
    (hP : Disjoint P ports) (hxy : x ≠ y) :
    (({x,y} ∪ P) ∩ ports).card ≤ 1 ↔ ¬ (x ∈ ports ∧ y ∈ ports) := by
  rw [union_inter_distrib_right, disjoint_iff_inter_eq_empty.mp hP, union_empty]
  by_cases hx : x ∈ ports <;> by_cases hy : y ∈ ports <;>
    simp [insert_inter_of_mem, insert_inter_of_notMem, hx, hy, hxy]

/-- Last junction of a contracted block; its first junction is labelled `inl b`. -/
@[expose] def blockLast {M J : Type*} : M ⊕ J → (M ⊕ J) ⊕ M
  | .inl m => .inr m
  | .inr j => .inl (.inr j)

theorem codeJunction_first_mem_ports (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (dir : MarkerDirections markers root) (J : ↥(ordinaryJunctionChoices markers k))
    (b : ↥markers ⊕ ↥J.val) :
    codeJunction hM hroot dir J (.inl b) ∈ originalPorts markers ↔
      ∃ m, b = Sum.inl m := by
  cases b with
  | inl m =>
    constructor
    · intro _; exact ⟨m, rfl⟩
    · intro _
      change (markerFirst hM root hroot dir m).val ∈ originalPorts markers
      exact mem_biUnion.mpr ⟨m.val, m.property, (markerFirst hM root hroot dir m).property⟩
  | inr v =>
    have hv := (mem_sdiff.mp (((mem_ordinaryJunctionChoices _ _ _).mp J.property).1 v.property)).2
    change v.val ∈ originalPorts markers ↔ ∃ m, Sum.inr v = Sum.inl m
    simp [hv]

theorem codeJunction_last_mem_ports (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (dir : MarkerDirections markers root) (J : ↥(ordinaryJunctionChoices markers k))
    (b : ↥markers ⊕ ↥J.val) :
    codeJunction hM hroot dir J (blockLast b) ∈ originalPorts markers ↔
      ∃ m, b = Sum.inl m := by
  cases b with
  | inl m =>
    constructor
    · intro _; exact ⟨m, rfl⟩
    · intro _
      change (markerLast hM root hroot dir m).val ∈ originalPorts markers
      exact mem_biUnion.mpr ⟨m.val, m.property, (markerLast hM root hroot dir m).property⟩
  | inr v => exact codeJunction_first_mem_ports hM hroot dir J (.inr v)


theorem blockLast_successor {M T : Type*} (σ : Equiv.Perm (M ⊕ T)) (a : M ⊕ T) :
    BlockEnumeration.gapPermutation σ ⟨Sum.inl, Sum.inl_injective⟩ (blockLast a) = .inl (σ a) := by
  cases a with
  | inl m => rfl
  | inr v => simp [blockLast, BlockEnumeration.gapPermutation, BlockEnumeration.gapNext]

theorem decodeBlockData_edge (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (J : ↥(ordinaryJunctionChoices markers k)) (dir : MarkerDirections markers root)
    (b : (↥markers ⊕ ↥J.val) ≃ Fin k)
    (σ : Equiv.Perm (↥markers ⊕ ↥J.val)) (hσ : σ.IsCycleOn Set.univ)
    (hcard : 3 ≤ Fintype.card (BlockJunctions markers ↥J.val))
    (P : Allocation.Blocks (PrivatePool markers J.val) k (r - 2))
    (a : ↥markers ⊕ ↥J.val) :
    (decodeBlockData hM hroot J dir b σ hσ hcard P).expanded.edge a =
      {codeJunction hM hroot dir J (blockLast a), codeJunction hM hroot dir J (.inl (σ a))} ∪
        Allocation.liftBlocks P ⟨Subtype.val, Subtype.val_injective⟩ b a := by
  rw [PermutationCycleData.expanded_edge]
  have hs : (blockSlot markers ↥J.val).symm (.inr a) = blockLast a := by cases a <;> rfl
  change {codeJunction hM hroot dir J ((blockSlot markers ↥J.val).symm (.inr a)),
    codeJunction hM hroot dir J (BlockEnumeration.gapPermutation σ (markerEmbedding markers ↥J.val)
      ((blockSlot markers ↥J.val).symm (.inr a)))} ∪ _ = _
  rw [hs]
  change {_, codeJunction hM hroot dir J (BlockEnumeration.gapPermutation σ ⟨Sum.inl, Sum.inl_injective⟩ (blockLast a))} ∪ _ = _
  rw [blockLast_successor]
  rfl


/-- The actual port prohibition is precisely separation of the marked blocks. -/
theorem decodeBlockData_allowed_iff (hr : 3 ≤ r)
    (hM : IsPairMatching markers) (hroot : root ∈ markers)
    (J : ↥(ordinaryJunctionChoices markers k)) (dir : MarkerDirections markers root)
    (b : (↥markers ⊕ ↥J.val) ≃ Fin k)
    (σ : Equiv.Perm (↥markers ⊕ ↥J.val)) (hσ : σ.IsCycleOn Set.univ)
    (hcard : 3 ≤ Fintype.card (BlockJunctions markers ↥J.val))
    (P : Allocation.Blocks (PrivatePool markers J.val) k (r - 2)) :
    (decodeBlockData hM hroot J dir b σ hσ hcard P).expanded.edges ⊆
      allowedEdges r (originalPorts markers) ↔
        ∀ m : ↥markers, ∃ v : ↥J.val, σ (.inl m) = .inr v := by
  let D := decodeBlockData hM hroot J dir b σ hσ hcard P
  have he (a : ↥markers ⊕ ↥J.val) : D.expanded.edge a ∈ D.expanded.edges :=
    mem_image_of_mem _ (mem_univ _)
  have hc (a : ↥markers ⊕ ↥J.val) : (D.expanded.edge a).card = r :=
    (D.isMixedCycle hr).uniform hr _ (he a)
  have hp (a : ↥markers ⊕ ↥J.val) :
      Disjoint (Allocation.liftBlocks P ⟨Subtype.val, Subtype.val_injective⟩ b a)
        (originalPorts markers) := by
    have h := (D.junction_private_disjoint a).symm
    change Disjoint (Allocation.liftBlocks P ⟨Subtype.val, Subtype.val_injective⟩ b a)
      (univ.image (codeJunction hM hroot dir J)) at h
    rw [codeJunction_image] at h
    exact h.mono_right subset_union_left
  have hn (a : ↥markers ⊕ ↥J.val) :
      codeJunction hM hroot dir J (blockLast a) ≠
        codeJunction hM hroot dir J (.inl (σ a)) := by
    have ht : (Set.univ : Set (BlockJunctions markers ↥J.val)).Nontrivial := by
      rw [Set.nontrivial_univ_iff]
      exact Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hn := D.cyclic.apply_ne ht (Set.mem_univ (D.slot.symm (.inr a)))
    have hs : D.slot.symm (.inr a) = blockLast a := by cases a <;> rfl
    have hh : D.successor (blockLast a) = .inl (σ a) := blockLast_successor σ a
    intro h
    apply hn
    rw [hs, hh]
    exact (codeJunction hM hroot dir J).injective h.symm
  have ha (a : ↥markers ⊕ ↥J.val) :
      D.expanded.edge a ∈ allowedEdges r (originalPorts markers) ↔
        ¬ ((∃ m, a = Sum.inl m) ∧ (∃ m, σ a = Sum.inl m)) := by
    rw [mem_allowedEdges, hc, eq_self, true_and]
    change (((decodeBlockData hM hroot J dir b σ hσ hcard P).expanded.edge a) ∩ _).card ≤ 1 ↔ _
    rw [decodeBlockData_edge, pair_private_allowed_iff _ _ _ _ (hp a) (hn a),
      codeJunction_last_mem_ports, codeJunction_first_mem_ports]
  constructor
  · intro h m
    have hn := (ha (.inl m)).mp (h (he (.inl m)))
    cases hh : σ (.inl m) with
    | inl t => exact False.elim (hn ⟨⟨m,rfl⟩, ⟨t,hh⟩⟩)
    | inr v => exact ⟨v,rfl⟩
  · intro h e he'
    obtain ⟨a, _, rfl⟩ := mem_image.mp he'
    apply (ha a).mpr
    rintro ⟨⟨m,rfl⟩,t,ht⟩
    obtain ⟨v,hv⟩ := h m
    rw [hv] at ht
    cases ht


/-- Translate the two sum conventions used for marked-block separation. -/
theorem separated_swap_iff {M T : Type*} (σ : Equiv.Perm (M ⊕ T)) :
    BlockEnumeration.Separated (permutationTransport (Equiv.sumComm M T) σ) ↔
      ∀ m : M, ∃ v : T, σ (.inl m) = .inr v := by
  constructor
  · intro h m
    obtain ⟨v,hv⟩ := h m
    refine ⟨v, ?_⟩
    have hh := congrArg (Equiv.sumComm T M) hv
    simpa using hh
  · intro h m
    obtain ⟨v,hv⟩ := h m
    exact ⟨v, by simp [hv]⟩

namespace CompleteHostCode
/-- The actual permutation on blocks used by the decoder. -/
@[expose] def blockOrder (hsk : markers.card ≤ k) (hk : 0 < k)
    (c : CompleteHostCode r k markers root) : Equiv.Perm (↥markers ⊕ ↥c.1.val) :=
  permutationTransport (codeBlockLabels markers k hsk c.1).symm
    (rootedOrderCycleEquiv k hk c.2.2.1).val

/-- The restriction on enumeration codes that corresponds to the fixed original-port prohibition. -/
@[expose] def HasSeparatedMarkers (hsk : markers.card ≤ k) (hk : 0 < k)
    (c : CompleteHostCode r k markers root) : Prop :=
  ∀ m : ↥markers, ∃ v : ↥c.1.val, blockOrder hsk hk c (.inl m) = .inr v

theorem decodeEdges_allowed_iff (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (hroot : root ∈ markers) (hk : 3 ≤ k) (hsk : markers.card ≤ k)
    (c : CompleteHostCode r k markers root) :
    decodeEdges hM hroot hk hsk c ⊆ allowedEdges r (originalPorts markers) ↔
      HasSeparatedMarkers hsk (by omega) c := by
  unfold decodeEdges decodeData HasSeparatedMarkers blockOrder
  dsimp only
  apply decodeBlockData_allowed_iff hr
end CompleteHostCode
end LooseHamilton
