module

public import HittingTimeLooseHamilton.FrameRestrictedSupportsDegree
public import HittingTimeLooseHamilton.CandidateExperiment

public section

noncomputable section
open Finset
namespace LooseHamilton

/-- A vertex boundary meets at most twice its size many ordinary cycle edges. -/
theorem cycle_boundary_edges_card_le {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {S : Finset V} {M E : Finset (Finset V)}
    (C : MixedCycleOnWitness r S M E) (D : Finset V) :
    (E.filter (fun e => ¬Disjoint e D)).card ≤ 2*D.card := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert v D hv ih =>
    have he : E.filter (fun e => ¬Disjoint e (insert v D)) =
        E.filter (fun e => v ∈ e) ∪ E.filter (fun e => ¬Disjoint e D) := by
      ext e
      simp only [mem_filter, mem_union, disjoint_insert_right]
      tauto
    rw [he, card_insert_of_notMem hv]
    have hc := card_union_le (E.filter (fun e => v ∈ e)) (E.filter (fun e => ¬Disjoint e D))
    have hi := C.incident_card_le_two v
    omega

/-- Restricting support preserves avoidance whenever the batch lies in the sampling host. -/
theorem disjoint_restricted_support_iff {α : Type*} [DecidableEq α]
    (E U T : Finset α) (hT : T ⊆ U) : Disjoint (E ∩ U) T ↔ Disjoint E T := by
  constructor
  · intro h
    apply disjoint_left.mpr
    intro e he ht
    exact disjoint_left.mp h (mem_inter.mpr ⟨he,hT ht⟩) ht
  · intro h
    exact h.mono_left inter_subset_left

namespace CandidateBalance
open AuxiliaryFrame
variable {V : Type} [Fintype V] [DecidableEq V]
variable {r : ℕ} {original : Finset (Finset V)}

/-- On the actual raw host, sampled support is precisely the edges avoiding the boundary. -/
theorem restricted_support_eq_filter (f : Frame r original) (D : Finset V)
    (H E : SimpleHypergraph V) (hE : E ⊆ f.rawHost H) :
    E ∩ unexposed f D H = E.filter (fun e => Disjoint e D) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨he,hu⟩ := mem_inter.mp he
    exact mem_filter.mpr ⟨he,(mem_filter.mp (mem_inter.mp hu).2).2⟩
  · intro he
    obtain ⟨he,hd⟩ := mem_filter.mp he
    have hr := hE he
    rw [rawHost_eq_inter] at hr
    exact mem_inter.mpr ⟨he,mem_inter.mpr ⟨(mem_inter.mp hr).1,
      mem_filter.mpr ⟨(mem_inter.mp hr).2,hd⟩⟩⟩

/-- The original family remains the label set; only its sampled edge support shrinks. -/
theorem restricted_support_card_bounds (f : Frame r original) (D : Finset V)
    (H E : SimpleHypergraph V) (hE : E ⊆ f.rawHost H)
    {S : Finset V} {M : Finset (Finset V)} (C : MixedCycleOnWitness r S M E) :
    E.card-2*D.card ≤ (E ∩ unexposed f D H).card ∧
    (E ∩ unexposed f D H).card ≤ E.card := by
  classical
  constructor
  · rw [restricted_support_eq_filter f D H E hE]
    have hc := cycle_boundary_edges_card_le C D
    have hs := card_filter_add_card_filter_not (s := E) (p := fun e => Disjoint e D)
    omega
  · exact card_le_card inter_subset_left

/-- Cycle sampled supports lie in `[k-2|D|,k]`, with no assumption that `D` was deleted. -/
theorem cycle_restricted_support_card (f : Frame r original) (hr : 3 ≤ r)
    (D : Finset V) (H E : SimpleHypergraph V) (hE : E ∈ f.cycleFamily H) :
    f.k-2*D.card ≤ (E ∩ unexposed f D H).card ∧
    (E ∩ unexposed f D H).card ≤ f.k := by
  obtain ⟨hsub,C,_⟩ := (f.mem_cycleFamily H E).mp hE
  simpa only [f.edge_card hr hE] using restricted_support_card_bounds f D H E hsub C

/-- Completion sampled supports lie in `[k-1-2|D|,k-1]`, retaining the original labels. -/
theorem completion_restricted_support_card (f : Frame r original) (hr : 3 ≤ r)
    (D : Finset V) (H E : SimpleHypergraph V)
    (hNonempty : (f.cycleFamily H).Nonempty)
    (c : Finset V × V × V) (hc : f.LegalCandidate c)
    (hE : E ∈ f.completionFamily H c) :
    (f.k-1)-2*D.card ≤ (E ∩ unexposed f D H).card ∧
    (E ∩ unexposed f D H).card ≤ f.k-1 := by
  obtain ⟨hsub,C,_⟩ := (f.mem_completionFamily H c E).mp hE
  simpa only [f.completion_edge_card hr hNonempty hc hE] using
    restricted_support_card_bounds f D H E hsub C

end CandidateBalance
end LooseHamilton
