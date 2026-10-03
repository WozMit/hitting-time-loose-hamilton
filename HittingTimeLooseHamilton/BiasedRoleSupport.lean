module

public import HittingTimeLooseHamilton.BiasedCloneEntropy
public import HittingTimeLooseHamilton.IntrinsicRoles

public section

/-! Exact finite role-support bound, with the root direction counted once. -/
noncomputable section
namespace LooseHamilton
open Finset FiniteEntropy
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace ConnectedCloneCycle
variable {r : ℕ} {markers : SimpleHypergraph V}

abbrev Configuration (r : ℕ) (markers : SimpleHypergraph V) (root : ↥markers) :=
  ↥(ordinaryJunctionChoices markers (ordinaryEdgeCount r markers)) ×
    MarkerDirections markers root.val

@[expose] def configuration (hr : 3 ≤ r) (root : ↥markers) (a : ↥root.val)
    (C : ConnectedCloneCycle r markers) : Configuration r markers root :=
  (⟨(C.directedWitness root a).ordinaryJunctionChoice.val, by
    have h := (C.directedWitness root a).ordinaryJunctionChoice.property
    have hc : C.val.card=ordinaryEdgeCount r markers := C.property.edge_card hr
    change _ ∈ ordinaryJunctionChoices markers (ordinaryEdgeCount r markers)
    simpa only [MixedCycleWitness.ordinaryJunctionChoice, hc] using h⟩, (C.directedWitness root a).markerDirections root.val)

@[expose] def configurationRole (root : ↥markers) (a : ↥root.val)
    (c : Configuration r markers root) : Finset V × (↥markers → V) :=
  (c.1.val, fun e => if h : e.val=root.val then a.val else
    (c.2 ⟨e.val,mem_erase.mpr ⟨h,e.property⟩⟩).val)

lemma configurationRole_eq (hr : 3 ≤ r) (root : ↥markers) (a : ↥root.val)
    (C : ConnectedCloneCycle r markers) :
    configurationRole root a (configuration hr root a C)=role root a C := by
  apply Prod.ext
  · rfl
  · funext e
    dsimp only [configurationRole, configuration, role]
    split_ifs with h
    · have he : e=root := Subtype.ext h
      subst e
      exact (congrArg Subtype.val (C.property.some.normalize_markerStart root a)).symm
    · rfl

lemma role_entropy_le_configuration (hr : 3 ≤ r) (root : ↥markers) (a : ↥root.val)
    (p : Law (ConnectedCloneCycle r markers)) :
    entropy (p.map (role root a)).mass ≤
      entropy (p.map (configuration hr root a)).mass := by
  have h := (p.map (configuration hr root a)).entropy_map_le (configurationRole root a)
  rw [Law.map_map] at h
  simpa only [Function.comp_def, configurationRole_eq] using h

/-- S_R is the logarithm of the binomial factor times 2^(s-1), exactly. -/
theorem role_entropy_le_log_support (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (root : ↥markers) (a : ↥root.val) (p : Law (ConnectedCloneCycle r markers)) :
    entropy (p.map (role root a)).mass ≤
      Real.log (((Fintype.card V-2*markers.card).choose
        (ordinaryEdgeCount r markers-markers.card):ℝ)*2^(markers.card-1)) := by
  have hp : Nonempty (ConnectedCloneCycle r markers) := by
    by_contra h
    haveI : IsEmpty (ConnectedCloneCycle r markers) := not_nonempty_iff.mp h
    have ht := p.total
    simp at ht
  letI := hp
  letI : Nonempty (Configuration r markers root) :=
    ⟨configuration hr root a (Classical.choice hp)⟩
  have h := entropy_le_log_card (p.map (configuration hr root a))
  have hc : Fintype.card (Configuration r markers root) =
      (Fintype.card V-2*markers.card).choose (ordinaryEdgeCount r markers-markers.card)*
        2^(markers.card-1) := by
    rw [Fintype.card_prod,Fintype.card_coe,ordinaryJunctionChoices_card hM,
      markerDirections_card hM root.property]
  rw [hc,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at h
  exact (role_entropy_le_configuration hr root a p).trans h
/-- Forgetting marker directions loses at most (s-1) log 2 entropy. -/
theorem role_entropy_le_junction_entropy (hr : 3 ≤ r) (hM : IsPairMatching markers)
    (root : ↥markers) (a : ↥root.val) (p : Law (ConnectedCloneCycle r markers)) :
    entropy (p.map (role root a)).mass ≤
      entropy (p.map (fun C => (role root a C).1)).mass +
        ((markers.card-1:ℕ):ℝ)*Real.log 2 := by
  have hp : Nonempty (ConnectedCloneCycle r markers) := by
    by_contra h
    haveI := not_nonempty_iff.mp h
    have ht := p.total
    simp at ht
  letI := hp
  letI : Nonempty (MarkerDirections markers root.val) :=
    ⟨(configuration hr root a (Classical.choice hp)).2⟩
  let J := fun C => (configuration hr root a C).1
  let T := fun C => (configuration hr root a C).2
  have hb := p.entropy_map_pair_le J T
  have he : entropy (p.map J).mass =
      entropy (p.map (fun C => (role root a C).1)).mass := by
    have hi := (p.map J).entropy_map_of_injective Subtype.val Subtype.val_injective
    rw [Law.map_map] at hi
    exact hi.symm
  have hd := entropy_le_log_card (p.map T)
  rw [markerDirections_card hM root.property, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow] at hd
  have hconf : (fun C => (J C,T C))=configuration hr root a := rfl
  rw [hconf,he] at hb
  exact (role_entropy_le_configuration hr root a p).trans (hb.trans (add_le_add_right hd _))

end ConnectedCloneCycle
end LooseHamilton
