module

public import HittingTimeLooseHamilton.OneVertexSwitchingBasic

public section

noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def degreeLayer (r m : ℕ) (ell : V → ℕ) (v : V) (t : ℕ) :=
  {F : TerminalState V r m ell // vertexDegree F.val v = t}

@[expose] instance {r m : ℕ} {ell : V → ℕ} {v : V} {t : ℕ} :
    Fintype (degreeLayer r m ell v t) := by unfold degreeLayer; infer_instance

@[expose] def layerCount (r m : ℕ) (ell : V → ℕ) (v : V) (t : ℕ) : ℕ :=
  Fintype.card (degreeLayer r m ell v t)

theorem switchGraph_uniform {F : SimpleHypergraph V} {e : Finset V} {v w : V} {r : ℕ}
    (hF : F ⊆ completeEdges V r) (he : e ∈ F) (hv : v ∈ e) (hw : w ∉ e) :
    switchGraph F e v w ⊆ completeEdges V r := by
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · rw [mem_completeEdges, switchedEdge_card hv hw]
    exact mem_completeEdges _ _ |>.mp (hF he)
  · exact hF (Finset.mem_of_mem_erase ha)

@[expose] def switchedTerminal {r m : ℕ} {ell : V → ℕ} (F : TerminalState V r m ell)
    (e : Finset V) (v w : V) (he : e ∈ F.val) (hv : v ∈ e) (hw : w ∉ e)
    (ha : switchedEdge e v w ∉ F.val) (hl : ell v < vertexDegree F.val v) :
    TerminalState V r m ell :=
  ⟨switchGraph F.val e v w, switchGraph_uniform F.property.1 he hv hw,
    (switchGraph_card he ha).trans F.property.2.1, by
      intro x
      by_cases hx : x = v
      · subst x
        rw [switchGraph_degree_source he hv hw ha]
        omega
      · exact (F.property.2.2 x).trans (switchGraph_degree_other he hv hw ha hx)⟩

@[expose] def switchedLayer {r m t : ℕ} {ell : V → ℕ} {v : V}
    (F : degreeLayer r m ell v t) (e : Finset V) (w : V)
    (he : e ∈ F.val.val) (hv : v ∈ e) (hw : w ∉ e)
    (ha : switchedEdge e v w ∉ F.val.val) (hl : ell v < t) :
    degreeLayer r m ell v (t-1) :=
  ⟨switchedTerminal F.val e v w he hv hw ha (by rw [F.property]; exact hl), by
    change vertexDegree (switchGraph F.val.val e v w) v = t-1
    rw [switchGraph_degree_source he hv hw ha, F.property]⟩

/-- An incidence of an edge and one of its vertices, in a degree layer. -/
abbrev layerIncidence (r m : ℕ) (ell : V → ℕ) (v : V) (t : ℕ) :=
  Σ F : degreeLayer r m ell v t, Σ e : ↥F.val.val, ↥e.val

/-- All candidate switches, before discarding blocked replacements. -/
abbrev layerCandidates (r m : ℕ) (ell : V → ℕ) (v : V) (t : ℕ) :=
  Σ F : degreeLayer r m ell v t, ↥(F.val.val.filter (fun e => v ∈ e)) × V

open scoped BigOperators

theorem card_layerIncidence (r m : ℕ) (ell : V → ℕ) (v : V) (t : ℕ) :
    Fintype.card (layerIncidence r m ell v t) = layerCount r m ell v t * (m*r) := by
  rw [Fintype.card_sigma]
  have h : ∀ F : degreeLayer r m ell v t,
      Fintype.card (Σ e : ↥F.val.val, ↥e.val) = m*r := by
    intro F
    rw [Fintype.card_sigma]
    have he : ∀ e : ↥F.val.val, Fintype.card ↥e.val = r := by
      intro e
      rw [Fintype.card_coe]
      exact mem_completeEdges _ _ |>.mp (F.val.property.1 e.property)
    simp_rw [he]
    simp [F.val.property.2.1]
  simp_rw [h]
  simp [layerCount]

theorem card_layerCandidates (r m : ℕ) (ell : V → ℕ) (v : V) (t : ℕ) :
    Fintype.card (layerCandidates r m ell v t) = layerCount r m ell v t * (t*Fintype.card V) := by
  rw [Fintype.card_sigma]
  have h : ∀ F : degreeLayer r m ell v t,
      Fintype.card (↥(F.val.val.filter (fun e => v ∈ e)) × V) = t*Fintype.card V := by
    intro F
    rw [Fintype.card_prod, Fintype.card_coe]
    exact congrArg (fun n => n*Fintype.card V) F.property
  simp_rw [h]
  simp [layerCount]

end LooseHamilton
