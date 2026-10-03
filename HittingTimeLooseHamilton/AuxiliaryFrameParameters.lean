module

public import HittingTimeLooseHamilton.AuxiliaryFrameCycles
public import HittingTimeLooseHamilton.CompletionParameters

public section

noncomputable section
namespace LooseHamilton.AuxiliaryFrame.Frame
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

theorem n_add_deleted (F : Frame r original) :
    F.n + F.val.deleted.card = Fintype.card V := by
  exact card_sdiff_add_card_eq_card (subset_univ _)
theorem n_lower (F : Frame r original) : Fintype.card V - 4*r ≤ F.n := by
  have := F.n_add_deleted
  have := F.val.deleted_card_le
  omega
theorem twice_s_le_n (F : Frame r original) : 2*F.s ≤ F.n := by
  have hh : originalPorts F.markers ⊆ F.active := by
    intro x hx
    obtain ⟨e,he,hx⟩ := mem_biUnion.mp hx
    exact F.property.retained e he hx
  have hc := card_le_card hh
  have he : (originalPorts F.markers).card = 2*F.markers.card := F.property.matching.ports_card
  rw [he] at hc
  exact hc

theorem edge_card (F : Frame r original) (hr : 3 ≤ r)
    {host E : Finset (Finset V)} (hE : E ∈ F.cycleFamily host) : E.card = F.k := by
  obtain ⟨_,C,_⟩ := (F.mem_cycleFamily host E).mp hE
  have hc := C.vertex_card hr
  unfold k n s
  rw [hc, Nat.add_sub_cancel, Nat.mul_div_right _ (by omega : 0 < r-1)]

theorem vertex_identity (F : Frame r original) (hr : 3 ≤ r)
    {host : Finset (Finset V)} (h : (F.cycleFamily host).Nonempty) :
    F.n = (r-1)*F.k+F.s := by
  obtain ⟨E,hE⟩ := h
  obtain ⟨_,C,_⟩ := (F.mem_cycleFamily host E).mp hE
  have hc := C.vertex_card hr
  rw [F.edge_card hr hE] at hc
  exact hc

theorem k_pos (F : Frame r original) (hr : 3 ≤ r)
    {host : Finset (Finset V)} (h : (F.cycleFamily host).Nonempty) : 0 < F.k := by
  have hi := F.vertex_identity hr h
  have hs : 0 < F.s := card_pos.mpr F.markers_nonempty
  have hn := F.twice_s_le_n
  by_contra hk
  have he : F.k = 0 := by omega
  rw [he,mul_zero,zero_add] at hi
  omega

theorem k_le_n (F : Frame r original) : F.k ≤ F.n :=
  (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

@[simp] theorem mem_completionFamily (F : Frame r original)
    (host : Finset (Finset V)) (c : Finset V × V × V) (E : Finset (Finset V)) :
    E ∈ F.completionFamily host c ↔ E ⊆ F.rawHost host ∧
    ∃ C : MixedCycleOnWitness r (F.active \ c.1) (insert {c.2.1,c.2.2} F.markers) E,
      F.Directed C ∧ Starts C c.2 := by
  classical
  simp [completionFamily]

theorem completion_edge_card (F : Frame r original) (hr : 3 ≤ r)
    {host : Finset (Finset V)} (h : (F.cycleFamily host).Nonempty)
    {c : Finset V × V × V} (hc : F.LegalCandidate c)
    {E : Finset (Finset V)} (hE : E ∈ F.completionFamily host c) :
    E.card = F.k-1 := by
  obtain ⟨_,C,_⟩ := (F.mem_completionFamily host c E).mp hE
  have hv := C.vertex_card hr
  have hp : c.1 ⊆ F.active := (subset_union_left).trans hc.2.1
  rw [card_sdiff_of_subset hp, hc.1.private_card, hc.1.augmented_card] at hv
  have hi := F.vertex_identity hr h
  have hpa : r-2 ≤ F.n := by
    rw [← hc.1.private_card]
    exact card_le_card hp
  have hactive : F.n = (r-1)*E.card + (F.s+1)+(r-2) := by
    change F.n-(r-2)=(r-1)*E.card+(F.s+1) at hv
    omega
  have hm : (r-1)*F.k = (r-1)*(E.card+1) := by
    rw [mul_add,mul_one]
    omega
  have he := Nat.eq_of_mul_eq_mul_left (by omega : 0 < r-1) hm
  omega
end LooseHamilton.AuxiliaryFrame.Frame
