module

public import HittingTimeLooseHamilton.SequentialCompletionStates

public section

/-! Actual one-step transitions obtained from the proved mobility conclusions. -/
noncomputable section
namespace LooseHamilton.SequentialCompletion
open Finset BootstrapBases
variable {N r : ℕ} {original : Finset (Finset (Fin N))}

/-- Private mobility changes one coordinate of a genuine ordered completion. -/
theorem private_move (hr : 3 ≤ r) (hM : IsPairMatching original)
    (b : Base original) (H : SimpleHypergraph (Fin N))
    (s : State ↥(active b) (r-2)) (c : ℝ)
    (hs : s.Valid (r := r) (restrictEdges (active b) (markers hM b)))
    (i : Fin (r-2))
    (hmob : BootstrapPrivateMobility.Mobility (r := r) hM b H
      (s.remainder i) {s.first,s.second} (s.coords i) c) :
    ∃ E : Finset (Fin N), deleted b ⊆ E ∧
      (E.card:ℝ) ≤ (Real.sqrt (r-2:ℕ)+1)*Real.sqrt (FrameScales.alpha N)*N ∧
      ∀ t : ↥(active b), t.val ∉ E →
        (s.replacePrivate i t).Valid (r := r) (restrictEdges (active b) (markers hM b)) ∧
        BootstrapConstants.privateFactor r c *
          (s.weight r (restrictEdges (active b) (markers hM b))
            (fixedPortHost (inducedHost (active b) H) (fixedPorts b)):ℝ) ≤
          (s.replacePrivate i t).weight r (restrictEdges (active b) (markers hM b))
            (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) := by
  obtain ⟨E,hD,hE,ht⟩ := hmob
  refine ⟨E,hD,hE,?_⟩
  intro t hte
  have hh := ht t hte
  refine ⟨replacePrivate_valid hr s _ hs i t hh.1,?_⟩
  change BootstrapConstants.privateFactor r c *
    (completionCount r _ _ s.block {s.first,s.second}:ℝ) ≤
    completionCount r _ _ (s.replacePrivate i t).block {s.first,s.second}
  rw [block_eq_insert s i,replacePrivate_block]
  exact hh.2

/-- Endpoint targets are discarded only for the previously proved mobility
exception or a literal collision with fixed ports and the source labels. -/
theorem first_move (hM : IsPairMatching original)
    (b : Base original) (H : SimpleHypergraph (Fin N))
    (s : State ↥(active b) (r-2)) (c : ℝ)
    (hs : s.Valid (r := r) (restrictEdges (active b) (markers hM b)))
    (hp : EndpointSourcePorts (fixedPorts b) (restrictEdges (active b) (markers hM b))
      s.first s.second)
    (hmob : BootstrapEndpointMobility.Mobility (r := r) hM b H s.block s.first s.second c) :
    ∃ E : Finset (Fin N),
      (E.card:ℝ) ≤ Real.sqrt 2*(FrameScales.alpha N)^(1/4:ℝ)*N +
        (r-2:ℕ) + (fixedPorts b).card + 1 ∧
      ∀ t : ↥(active b), t.val ∉ E →
        (s.replaceFirst t).Valid (r := r) (restrictEdges (active b) (markers hM b)) ∧
        EndpointSourcePorts (fixedPorts b) (restrictEdges (active b) (markers hM b)) t s.second ∧
        BootstrapConstants.endpointFactor r c *
          (s.weight r (restrictEdges (active b) (markers hM b))
            (fixedPortHost (inducedHost (active b) H) (fixedPorts b)):ℝ) ≤
          (s.replaceFirst t).weight r (restrictEdges (active b) (markers hM b))
            (fixedPortHost (inducedHost (active b) H) (fixedPorts b)) := by
  obtain ⟨E,hE,ht⟩ := hmob
  let F := s.block ∪ fixedPorts b ∪ {s.second}
  let F' := F.map (Function.Embedding.subtype _)
  refine ⟨E ∪ F',?_,?_⟩
  · have hF : F.card ≤ (r-2)+(fixedPorts b).card+1 := by
      have hh := card_union_le (s.block ∪ fixedPorts b) {s.second}
      have hu := card_union_le s.block (fixedPorts b)
      rw [hs.2.private_card] at hu
      simp only [card_singleton] at hh
      dsimp [F]
      omega
    have hc : ((E ∪ F').card:ℝ) ≤ (E.card:ℝ)+((r-2:ℕ):ℝ)+(fixedPorts b).card+1 := by
      have hh := (card_union_le E F').trans (Nat.add_le_add_left
        (show F'.card ≤ (r-2)+(fixedPorts b).card+1 by simpa [F'] using hF) E.card)
      push_cast at hh ⊢
      exact_mod_cast (show (E ∪ F').card ≤ E.card+(r-2)+(fixedPorts b).card+1 by omega)
    linarith
  intro t hte
  have htE : t.val ∉ E := fun h => hte (mem_union_left _ h)
  have htF : t ∉ F := by
    intro h
    apply hte
    exact mem_union_right _ (mem_map.mpr ⟨t,h,rfl⟩)
  have htp : t ∉ fixedPorts b := fun h => htF (mem_union_left _ (mem_union_right _ h))
  have htc : t ∉ s.block ∪ originalPorts (restrictEdges (active b) (markers hM b)) ∪ {s.second} := by
    intro h
    apply htF
    rcases mem_union.mp h with h | h
    · rcases mem_union.mp h with h | h
      · exact mem_union_left _ (mem_union_left _ h)
      · exact mem_union_left _ (mem_union_right _ (hp.old_ports h))
    · exact mem_union_right _ h
  exact ⟨replaceFirst_valid s _ hs t htc,⟨hp.old_ports,hp.surviving_ports,htp⟩,ht t htE⟩

end LooseHamilton.SequentialCompletion
