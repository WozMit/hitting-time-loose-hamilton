module

public import HittingTimeLooseHamilton.EndpointSurgeryPrefix

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace MixedCycleOnWitness
variable {r : ℕ} {S : Finset V} {markers edges : Finset (Finset V)}

@[expose] def prefixInterior (C : MixedCycleOnWitness r S markers edges) (k : ℕ) : Finset V :=
  (univ.filter fun i : Fin C.length => 0 < i.val ∧ i.val ≤ k).image C.junction

@[expose] def prefixRemovedPrivate (C : MixedCycleOnWitness r S markers edges) (k : ℕ) : Finset V :=
  (univ.filter fun e : ↥edges => (C.slot.symm (.inr e)).val ≤ k).biUnion C.privateBlock

theorem mem_prefixInterior (C : MixedCycleOnWitness r S markers edges) (k : ℕ) (v : V) :
    v ∈ C.prefixInterior k ↔ ∃ i : Fin C.length,
      0 < i.val ∧ i.val ≤ k ∧ C.junction i = v := by
  simp only [prefixInterior, mem_image, mem_filter, mem_univ, true_and]
  aesop

theorem mem_prefixRemovedPrivate (C : MixedCycleOnWitness r S markers edges) (k : ℕ) (v : V) :
    v ∈ C.prefixRemovedPrivate k ↔ ∃ e : ↥edges,
      (C.slot.symm (.inr e)).val ≤ k ∧ v ∈ C.privateBlock e := by
  simp only [prefixRemovedPrivate, mem_biUnion, mem_filter, mem_univ, true_and]

theorem prefix_junctions (C : MixedCycleOnWitness r S markers edges)
    (m k : ℕ) (hm : 0 < m) (hlen : C.length = m+k) :
    univ.image (C.junction ∘ C.prefixKeep m k hlen) =
      univ.image C.junction \ C.prefixInterior k := by
  ext v
  simp only [mem_image, mem_univ, true_and, mem_sdiff, Function.comp_apply,
    C.mem_prefixInterior]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨⟨C.prefixKeep m k hlen i, rfl⟩, ?_⟩
    rintro ⟨j, hj0, hjk, hj⟩
    have he := congrArg Fin.val (C.junction_injective hj)
    simp only [C.prefixKeep_val] at he
    split_ifs at he <;> omega
  · rintro ⟨⟨j, rfl⟩, hn⟩
    have hj : j.val = 0 ∨ k < j.val := by
      by_contra hh
      push_neg at hh
      exact hn ⟨j, by omega, by omega, rfl⟩
    rcases hj with hj | hj
    · refine ⟨⟨0,hm⟩, congrArg C.junction (Fin.ext ?_)⟩
      simpa using hj.symm
    · let i : Fin m := ⟨j.val-k, by have := j.isLt; omega⟩
      refine ⟨i, congrArg C.junction (Fin.ext ?_)⟩
      have hi : i.val ≠ 0 := by dsimp [i]; omega
      simp only [prefixKeep_val, hi, ↓reduceIte]
      dsimp [i]; omega

theorem prefix_private_union (C : MixedCycleOnWitness r S markers edges) (k : ℕ) :
    univ.biUnion (fun e : ↥(C.prefixEdges k) =>
      C.privateBlock ⟨e.val, C.prefixEdges_subset k e.property⟩) =
    univ.biUnion C.privateBlock \ C.prefixRemovedPrivate k := by
  ext v
  simp only [mem_biUnion, mem_univ, true_and, mem_sdiff, C.mem_prefixRemovedPrivate]
  constructor
  · rintro ⟨e, he⟩
    let e' : ↥edges := ⟨e.val, C.prefixEdges_subset k e.property⟩
    refine ⟨⟨e',he⟩, ?_⟩
    rintro ⟨f, hf, hv⟩
    have hne : e' ≠ f := by
      intro heq
      have hhigh := (C.mem_prefixEdges k e.val).mp e.property |>.choose_spec
      change k < (C.slot.symm (.inr e')).val at hhigh
      rw [heq] at hhigh
      omega
    exact disjoint_left.mp (C.private_disjoint hne) he hv
  · rintro ⟨⟨e, he⟩, hn⟩
    have hh : k < (C.slot.symm (.inr e)).val := by
      by_contra hh
      exact hn ⟨e, by omega, he⟩
    refine ⟨⟨e.val, (C.mem_prefixEdges k e.val).mpr ⟨e.property, hh⟩⟩, ?_⟩
    exact he

theorem prefixActive_eq_sdiff (C : MixedCycleOnWitness r S markers edges)
    (m k : ℕ) (hm : 0 < m) (hlen : C.length = m+k) :
    C.prefixActive m k hlen = S \ (C.prefixInterior k ∪ C.prefixRemovedPrivate k) := by
  rw [prefixActive, C.prefix_junctions m k hm hlen, C.prefix_private_union k]
  have hc := congrArg (fun T : Finset V => T \ (C.prefixInterior k ∪ C.prefixRemovedPrivate k)) C.cover
  rw [hc]
  have hi : Disjoint (C.prefixInterior k) (univ.biUnion C.privateBlock) := by
    apply disjoint_left.mpr
    intro v hv hp
    obtain ⟨i, _, _, rfl⟩ := (C.mem_prefixInterior k v).mp hv
    obtain ⟨e, _, he⟩ := mem_biUnion.mp hp
    exact disjoint_left.mp (C.junction_private_disjoint e)
      (mem_image_of_mem _ (mem_univ i)) he
  have hb : Disjoint (univ.image C.junction) (C.prefixRemovedPrivate k) := by
    apply disjoint_left.mpr
    intro v hv hp
    obtain ⟨e, _, he⟩ := (C.mem_prefixRemovedPrivate k v).mp hp
    exact disjoint_left.mp (C.junction_private_disjoint e) hv he
  ext v
  have h1 : v ∈ C.prefixInterior k → v ∈ univ.biUnion C.privateBlock → False :=
    fun hv hp => disjoint_left.mp hi hv hp
  have h2 : v ∈ univ.image C.junction → v ∈ C.prefixRemovedPrivate k → False :=
    fun hv hp => disjoint_left.mp hb hv hp
  simp only [mem_union, mem_sdiff]
  tauto
end MixedCycleOnWitness
end LooseHamilton
