module

public import HittingTimeLooseHamilton.OneVertexSwitchingModel

public section

noncomputable section
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def encodeSwitch {r m t : ℕ} {ell : V → ℕ} {v : V} (hl : ell v < t)
    (x : layerCandidates r m ell v t) :
    layerIncidence r m ell v t ⊕ layerIncidence r m ell v (t-1) :=
  let F := x.1
  let e := x.2.1.val
  let w := x.2.2
  have he : e ∈ F.val.val := (Finset.mem_filter.mp x.2.1.property).1
  have hv : v ∈ e := (Finset.mem_filter.mp x.2.1.property).2
  if hw : w ∈ e then
    Sum.inl ⟨F, ⟨e, he⟩, ⟨w, hw⟩⟩
  else if ha : switchedEdge e v w ∈ F.val.val then
    Sum.inl ⟨F, ⟨switchedEdge e v w, ha⟩, ⟨w, by simp⟩⟩
  else
    Sum.inr ⟨switchedLayer F e w he hv hw ha hl,
      ⟨switchedEdge e v w, Finset.mem_insert_self _ _⟩, ⟨w, by simp⟩⟩

@[expose] def candidateData {r m t : ℕ} {ell : V → ℕ} {v : V}
    (x : layerCandidates r m ell v t) : SimpleHypergraph V × Finset V × V :=
  (x.1.val.val, x.2.1.val, x.2.2)

@[expose] def decodeSwitch {r m t : ℕ} {ell : V → ℕ} {v : V}
    (y : layerIncidence r m ell v t ⊕ layerIncidence r m ell v (t-1)) :
    SimpleHypergraph V × Finset V × V :=
  match y with
  | Sum.inl y => (y.1.val.val,
      if v ∈ y.2.1.val then y.2.1.val else switchedEdge y.2.1.val y.2.2.val v,
      y.2.2.val)
  | Sum.inr y => (switchGraph y.1.val.val y.2.1.val y.2.2.val v,
      switchedEdge y.2.1.val y.2.2.val v, y.2.2.val)

theorem decode_encodeSwitch {r m t : ℕ} {ell : V → ℕ} {v : V}
    (hl : ell v < t) (x : layerCandidates r m ell v t) :
    decodeSwitch (encodeSwitch hl x) = candidateData x := by
  obtain ⟨F, ⟨e, he⟩, w⟩ := x
  obtain ⟨he, hv⟩ := Finset.mem_filter.mp he
  by_cases hw : w ∈ e
  · simp [encodeSwitch, decodeSwitch, candidateData, hw, hv]
  · by_cases ha : switchedEdge e v w ∈ F.val.val
    · simp [encodeSwitch, decodeSwitch, candidateData, hw, ha,
        switchedEdge_not_mem hv hw, switchedEdge_reverse hv hw]
    · simp [encodeSwitch, decodeSwitch, candidateData, hw, ha,
        switchedLayer, switchedTerminal, switchedEdge_reverse hv hw,
        switchGraph_reverse he hv hw ha]

theorem candidateData_injective {r m t : ℕ} {ell : V → ℕ} {v : V} :
    Function.Injective (@candidateData V _ _ r m t ell v) := by
  rintro ⟨F, ⟨e, he⟩, w⟩ ⟨G, ⟨a, ha⟩, z⟩ h
  have hFG : F = G := Subtype.ext (Subtype.ext (congrArg Prod.fst h))
  subst G
  have hea : e = a := congrArg (fun x => x.2.1) h
  have hwz : w = z := congrArg (fun x => x.2.2) h
  subst a
  subst z
  rfl

theorem encodeSwitch_injective {r m t : ℕ} {ell : V → ℕ} {v : V}
    (hl : ell v < t) : Function.Injective (@encodeSwitch V _ _ r m t ell v hl) := by
  intro x y h
  apply candidateData_injective
  rw [← decode_encodeSwitch hl x, ← decode_encodeSwitch hl y, h]

/-- Exact finite layer recurrence obtained by an injective one-vertex switching.
Blocked candidates use at most the incidences in the original layer, while
successful candidates use incidences in the preceding layer. -/
theorem oneVertex_layer_recurrence {r m t : ℕ} {ell : V → ℕ} {v : V}
    (hl : ell v < t) :
    Fintype.card V * t * layerCount r m ell v t ≤
      r*m*(layerCount r m ell v t + layerCount r m ell v (t-1)) := by
  have h := Fintype.card_le_of_injective _ (encodeSwitch_injective (r := r) (m := m) hl)
  rw [card_layerCandidates, Fintype.card_sum, card_layerIncidence,
    card_layerIncidence] at h
  nlinarith

end LooseHamilton
