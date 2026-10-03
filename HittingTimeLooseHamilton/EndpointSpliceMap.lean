module

public import HittingTimeLooseHamilton.EndpointSpliceCounting
public import HittingTimeLooseHamilton.EndpointSpliceInjection

public section

/-! # Joint injection of the full endpoint-splicing domain -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {P : Finset V} {y z t : V}

theorem endpointSpliceMap_injective (hr : 3 ≤ r)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) (hy : y ∉ originalPorts M)
    (h : EndpointSpliceImageProperties r M G P y z t) :
    Function.Injective (endpointSpliceMap h) := by
  intro a b hab
  have heq := congrArg Subtype.val hab
  cases a with
  | inl a =>
    have I := endpointSpliceImageOfI h a
    obtain ⟨⟨l,hl⟩,⟨⟨c,hc⟩,⟨F,hF⟩⟩⟩ := a
    have hl := (mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hl
    have hc := (mem_endpointSpliceLabelsI _ _ _ _ _ _ _ _ _).mp hc
    cases b with
    | inl b =>
      have J := endpointSpliceImageOfI h b
      obtain ⟨⟨k,hk⟩,⟨⟨d,hd⟩,⟨F',hF'⟩⟩⟩ := b
      have hk := (mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hk
      have hd := (mem_endpointSpliceLabelsI _ _ _ _ _ _ _ _ _).mp hd
      change endpointSpliceOutputI y l c F = endpointSpliceOutputI y k d F' at heq
      obtain ⟨rfl,rfl,rfl⟩ := endpointSpliceI_joint_injective hr hl hk hc hd hF hF' I J heq
      rfl
    | inr b =>
      have J := endpointSpliceImageOfII h b
      obtain ⟨⟨k,hk⟩,⟨⟨d,hd⟩,⟨F',hF'⟩⟩⟩ := b
      have hk := (mem_endpointCutLabelsII _ _ _ _ _ _ _).mp hk
      change endpointSpliceOutputI y l c F = endpointSpliceOutputII y k d F' at heq
      exact False.elim (endpointSplice_types_disjoint hr hl hk I J heq)
  | inr a =>
    have I := endpointSpliceImageOfII h a
    obtain ⟨⟨l,hl⟩,⟨⟨c,hc⟩,⟨F,hF⟩⟩⟩ := a
    have hl := (mem_endpointCutLabelsII _ _ _ _ _ _ _).mp hl
    have hc := (mem_endpointSpliceLabelsII _ _ _ _ _ _ _ _ _).mp hc
    cases b with
    | inl b =>
      have J := endpointSpliceImageOfI h b
      obtain ⟨⟨k,hk⟩,⟨⟨d,hd⟩,⟨F',hF'⟩⟩⟩ := b
      have hk := (mem_endpointCutLabelsI _ _ _ _ _ _ _).mp hk
      change endpointSpliceOutputII y l c F = endpointSpliceOutputI y k d F' at heq
      exact False.elim (endpointSplice_types_disjoint hr hk hl J I heq.symm)
    | inr b =>
      have J := endpointSpliceImageOfII h b
      obtain ⟨⟨k,hk⟩,⟨⟨d,hd⟩,⟨F',hF'⟩⟩⟩ := b
      have hk := (mem_endpointCutLabelsII _ _ _ _ _ _ _).mp hk
      have hd := (mem_endpointSpliceLabelsII _ _ _ _ _ _ _ _ _).mp hd
      change endpointSpliceOutputII y l c F = endpointSpliceOutputII y k d F' at heq
      obtain ⟨rfl,rfl,rfl⟩ := endpointSpliceII_joint_injective hr hM hy hl hk hc hd hF hF' I J heq
      rfl

theorem endpointSplice_count_le_of_images (hr : 3 ≤ r)
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) (hy : y ∉ originalPorts M)
    (h : EndpointSpliceImageProperties r M G P y z t) :
    (∑ l ∈ endpointCutLabelsI r M G P y z,
      ∑ b ∈ endpointSpliceLabelsI r M G P y z t l,
        (endpointSpliceInputFamilyI r M G P y z t l b).card) +
    (∑ l ∈ endpointCutLabelsII r M G P y z,
      ∑ b ∈ endpointSpliceLabelsII r M G P y z t l,
        (endpointSpliceInputFamilyII r M G P y z t l b).card) ≤
      completionCount r M G P {t,z} := by
  classical
  have hc := Fintype.card_le_of_injective _ (endpointSpliceMap_injective hr hM hy h)
  rw [endpointSpliceDomain_card, Fintype.card_coe] at hc
  exact hc

end LooseHamilton
