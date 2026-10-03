module

public import HittingTimeLooseHamilton.PrivateCandidateFrameLegality
public import HittingTimeLooseHamilton.AuxiliaryFrameParameters
public import HittingTimeLooseHamilton.PathRegularityModels

public section

/-! Forgetting the auxiliary frame's directions bounds its actual candidate
count by the unrestricted `X` summand used by private migration. -/
noncomputable section
namespace LooseHamilton
open Finset AuxiliaryFrame
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem private_frame_completion_le {r : ℕ} (hr : 3 ≤ r)
    {markers original H : SimpleHypergraph V} {S q A R : Finset V} {x t u v : V}
    (h : PrivateRootSplitLegal r markers (allowedEdges r (originalPorts original))
      S q x t A R {u,v})
    (f : Frame r original)
    (hactive : f.active = univ \ insert x S) (hmarkers : f.markers = insert q markers) :
    f.completionCount H (insert t R,u,v) ≤
      privateCandidateCompletionCount r markers (fixedPortHost H (originalPorts original))
        S q x (insert t R,u,v) := by
  let active := univ \ (insert t S ∪ insert x R)
  have hset : f.active \ insert t R = active := by
    rw [hactive]
    ext w
    simp only [active, mem_sdiff, mem_univ, true_and, mem_insert, mem_union]
    tauto
  have hcount : (cycleOnFamily r active (insert {u,v} (insert q markers))
      (fixedPortHost H (originalPorts original))).card =
      privateCandidateCompletionCount r markers (fixedPortHost H (originalPorts original))
        S q x (insert t R,u,v) := by
    rw [privateCandidateCompletionCount_eq_summand]
    exact cycleOnCount_eq_unrestricted hr active _ _
      (privateMigration_markers_survive h.target_legal h.split_legal)
  rw [← hcount]
  apply card_le_card
  intro E hE
  obtain ⟨hhost,C,hdir,hstarts⟩ := (f.mem_completionFamily H _ E).mp hE
  apply (mem_cycleOnFamily _ _ _ _ _).mpr
  constructor
  · have hc : IsMixedCycleOn r (f.active \ insert t R)
        (insert {u,v} f.markers) E := ⟨C⟩
    simpa only [hset,hmarkers] using hc
  · intro e he
    have hh := mem_filter.mp (hhost he)
    have hhH := mem_inter.mp hh.1
    exact mem_filter.mpr ⟨hhH.1, ((mem_allowedEdges _ _ _).mp hhH.2).2⟩

end LooseHamilton
