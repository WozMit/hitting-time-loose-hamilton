module

public import HittingTimeLooseHamilton.EndpointSurgerySlots

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace MixedCycleOnWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

@[expose] def prefixActive (C : MixedCycleOnWitness r S markers edges)
    (m k : ℕ) (hlen : C.length = m+k) : Finset V :=
  univ.image (C.junction ∘ C.prefixKeep m k hlen) ∪
    univ.biUnion (fun e : ↥(C.prefixEdges k) =>
      C.privateBlock ⟨e.val, C.prefixEdges_subset k e.property⟩)

theorem prefixKeep_rotate (C : MixedCycleOnWitness r S markers edges)
    (m k : ℕ) (hm : 2 ≤ m) (hlen : C.length = m+k) (i : Fin m)
    (hi : i.val ≠ 0) :
    C.prefixKeep m k hlen (finRotate m i) = finRotate C.length (C.prefixKeep m k hlen i) := by
  apply Fin.ext
  simp only [prefixKeep_val, finRotate_val_eq C.length (by omega),
    finRotate_val_eq m (by omega)]
  split_ifs <;> omega


/-- Contract a normalized initial path to a single fresh marker. The remaining
edge slots and private blocks are retained verbatim. -/
@[expose] def contractPrefix (C : MixedCycleOnWitness r S markers edges)
    (m k : ℕ) (hm : 3 ≤ m) (hlen : C.length = m+k)
    (q : Finset V) (hq : q ∉ markers)
    (hmatch : ((insert q (C.prefixMarkers k) : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id)
    (hqedge : q = {C.junction (C.prefixKeep m k hlen ⟨0, by omega⟩),
      C.junction (C.prefixKeep m k hlen (finRotate m ⟨0, by omega⟩))}) :
    MixedCycleOnWitness r (C.prefixActive m k hlen)
      (insert q (C.prefixMarkers k)) (C.prefixEdges k) := by
  refine C.compress m hm (C.prefixKeep m k hlen) (C.prefixEdges_subset k)
    (C.prefixSlotEquiv m k (by omega) hlen q hq) hmatch rfl ?_
  intro i
  rw [prefixSlotEquiv_apply]
  by_cases hi : i.val = 0
  · have hiz : i = ⟨0, by omega⟩ := Fin.ext hi
    simp only [prefixSlotMap, dif_pos hi]
    simpa only [hiz] using hqedge
  · have hsedge := C.slot_edge (C.prefixKeep m k hlen i)
    rw [← C.prefixKeep_rotate m k (by omega) hlen i hi] at hsedge
    simp only [prefixSlotMap, dif_neg hi]
    split
    · rename_i e hs
      split at hs
      · rename_i f hf
        have he := Sum.inl.inj hs
        have hv := congrArg Subtype.val he
        simpa only [hf, ← hv] using hsedge
      · contradiction
    · rename_i e hs
      split at hs
      · contradiction
      · rename_i f hf
        have he := Sum.inr.inj hs
        have hv := congrArg Subtype.val he
        have hsub : (⟨e.val, C.prefixEdges_subset k e.property⟩ : ↥edges) = f :=
          Subtype.ext hv.symm
        simp only [hf] at hsedge
        rw [hsub]
        exact hv ▸ hsedge
end MixedCycleOnWitness
end LooseHamilton
