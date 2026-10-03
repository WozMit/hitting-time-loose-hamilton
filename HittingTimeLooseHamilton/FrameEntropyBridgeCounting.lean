module

public import HittingTimeLooseHamilton.FrameEntropyBridgeRoles
public import HittingTimeLooseHamilton.EntropySubfamily
public import HittingTimeLooseHamilton.KahnRandomOrder

public section

/-! The actual directed completion-to-role bijection and its exact probability. -/
noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
local instance : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- Erasing the specified ordinary edge is a bijection, even after simultaneously
prescribing every frame direction. The underlying objects are actual edge sets. -/
theorem roleFamily_card (F : Frame r original) (hr : 3 ≤ r)
    (H : Finset (Finset V)) {c : Finset V × V × V}
    (hc : F.LegalCandidate c) (hedge : c.1 ∪ {c.2.1,c.2.2} ∈ F.rawHost H) :
    (F.roleFamily H c).card = F.completionCount H c := by
  apply Finset.card_bij (fun E _ => E.erase (c.1 ∪ {c.2.1,c.2.2}))
  · intro E hE
    exact F.role_contract hc (mem_filter.mp hE).1 (mem_filter.mp hE).2
  · intro E hE E' hE' heq
    have he : c.1 ∪ {c.2.1,c.2.2} ∈ E := by
      obtain ⟨_,_,he,_⟩ := (mem_filter.mp hE).2
      exact he
    have he' : c.1 ∪ {c.2.1,c.2.2} ∈ E' := by
      obtain ⟨_,_,he,_⟩ := (mem_filter.mp hE').2
      exact he
    have := congrArg (insert (c.1 ∪ {c.2.1,c.2.2})) heq
    simpa only [insert_erase he,insert_erase he'] using this
  · intro E hE
    refine ⟨insert (c.1 ∪ {c.2.1,c.2.2}) E,
      F.completion_expand hr hc hedge hE,?_⟩
    exact erase_insert (F.completion_edge_absent hr hc hE)

/-- The law is uniform on the whole actual simultaneous-direction family. -/
@[expose] def cycleLaw (F : Frame r original) (H : Finset (Finset V))
    (hX : (F.cycleFamily H).Nonempty) :
    FiniteEntropy.Law (Finset (Finset V)) :=
  FiniteEntropy.uniformSubfamily (F.cycleFamily H) hX

/-- Exact finite role probability, with the genuine completion/cycle counts. -/
theorem cycleLaw_role (F : Frame r original) (hr : 3 ≤ r)
    (H : Finset (Finset V)) (hX : (F.cycleFamily H).Nonempty)
    {c : Finset V × V × V} (hc : F.LegalCandidate c)
    (hedge : c.1 ∪ {c.2.1,c.2.2} ∈ F.rawHost H) :
    (F.cycleLaw H hX).event (fun E => F.Role E c) =
      (F.completionCount H c : ℝ) / F.cycleCount H := by
  letI : Nonempty ↥(F.cycleFamily H) := ⟨⟨hX.choose,hX.choose_spec⟩⟩
  change (FiniteEntropy.uniform.map (Subtype.val : ↥(F.cycleFamily H) → _)).event _ = _
  rw [FiniteEntropy.Law.event_map,FiniteEntropy.Law.uniform_event]
  have heq : (univ.filter (fun E : ↥(F.cycleFamily H) => F.Role E.val c)).card =
      (F.roleFamily H c).card := by
    apply Finset.card_bij (fun E _ => E.val)
    · intro E hE
      exact mem_filter.mpr ⟨E.property,(mem_filter.mp hE).2⟩
    · intro E _ E' _ h
      exact Subtype.ext h
    · intro E hE
      exact ⟨⟨E,(mem_filter.mp hE).1⟩,
        mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hE).2⟩,rfl⟩
  rw [heq,F.roleFamily_card hr H hc hedge]
  simp only [Fintype.card_coe,cycleCount]

/-- Imposing directions incurs exactly the log of this family's cardinality;
no lower bound for a direction class or equidistribution is assumed. -/
theorem cycleLaw_entropy (F : Frame r original) (H : Finset (Finset V))
    (hX : (F.cycleFamily H).Nonempty) :
    FiniteEntropy.entropy (F.cycleLaw H hX).mass = Real.log (F.cycleCount H) :=
  FiniteEntropy.entropy_uniformSubfamily _ _

end LooseHamilton.AuxiliaryFrame.Frame
