module

public import HittingTimeLooseHamilton.Models
public import Mathlib.Tactic

public section

/-! Finite-set identities behind the exact reverse reconstruction. -/
namespace LooseHamilton
open Finset
variable {α : Type*} [DecidableEq α]

lemma batch_terminal_reconstruct (Fstar T : Finset α) :
    Fstar\T ∪ (T∩Fstar)=Fstar := by
  rw [inter_comm]
  exact sdiff_union_inter Fstar T

lemma batch_terminal_inter_card (Fstar T : Finset α) :
    (T∩Fstar).card=Fstar.card-(Fstar\T).card := by
  have hd : Disjoint (Fstar\T) (T∩Fstar) := by
    apply disjoint_left.mpr
    intro e he ht
    exact (mem_sdiff.mp he).2 (mem_inter.mp ht).1
  have hc := card_union_of_disjoint hd
  rw [batch_terminal_reconstruct] at hc
  omega

lemma batch_remainder_disjoint {H T : Finset α} : Disjoint (H\T) T :=
  disjoint_sdiff_self_left

lemma batch_restore_terminal_remainder {F0 T0 T : Finset α}
    (h0 : Disjoint F0 T) (hT : T0⊆T) : (F0∪T0)\T=F0 := by
  ext e
  simp only [mem_sdiff,mem_union]
  constructor
  · rintro ⟨he,hn⟩
    exact he.resolve_right (fun he => hn (hT he))
  · intro he
    exact ⟨Or.inl he,fun ht => disjoint_left.mp h0 he ht⟩

lemma batch_restore_terminal_inter {F0 T0 T : Finset α}
    (h0 : Disjoint F0 T) (hT : T0⊆T) : T∩(F0∪T0)=T0 := by
  ext e
  simp only [mem_inter,mem_union]
  constructor
  · rintro ⟨ht,he⟩
    exact he.resolve_left (fun he => disjoint_left.mp h0 he ht)
  · intro he
    exact ⟨hT he,Or.inr he⟩
end LooseHamilton
