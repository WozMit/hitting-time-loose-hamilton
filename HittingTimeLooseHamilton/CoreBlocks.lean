module

public import HittingTimeLooseHamilton.Setup
public import HittingTimeLooseHamilton.ExceptionalSetModels

public section

/-! Trace-measurable selection of disjoint exceptional edges, their two ports,
and the private vertices removed when forming the marked core. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All exposed edges incident with an exceptional vertex. -/
@[expose] def exceptionalTrace (B : Finset V) (F : SimpleHypergraph V) : SimpleHypergraph V :=
  F.filter (fun e => ∃ v ∈ B, v ∈ e)

omit [Fintype V] in
@[simp] lemma mem_exceptionalTrace {B : Finset V} {F : SimpleHypergraph V} {e : Finset V} :
    e ∈ exceptionalTrace B F ↔ e ∈ F ∧ ∃ v ∈ B, v ∈ e := by simp [exceptionalTrace]

lemma exceptionalTrace_incident_nonempty {B : Finset V} {F : SimpleHypergraph V}
    (v : ↥B) (hv : 0 < vertexDegree F v.val) :
    ((exceptionalTrace B F).filter (fun e => v.val ∈ e)).Nonempty := by
  obtain ⟨e,he'⟩ := card_pos.mp hv
  obtain ⟨he,hve⟩ := mem_filter.mp he'
  exact ⟨e,mem_filter.mpr ⟨mem_exceptionalTrace.mpr ⟨he,v.val,v.property,hve⟩,hve⟩⟩

/-- The choice uses only the exposed trace, not the remaining unexposed host. -/
@[expose] def traceSelectedEdge (T : SimpleHypergraph V) (v : V)
    (h : (T.filter (fun e => v ∈ e)).Nonempty) : Finset V := h.choose

omit [Fintype V] in
lemma traceSelectedEdge_spec (T : SimpleHypergraph V) (v : V)
    (h : (T.filter (fun e => v ∈ e)).Nonempty) :
    traceSelectedEdge T v h ∈ T ∧ v ∈ traceSelectedEdge T v h :=
  mem_filter.mp h.choose_spec

/-- Selected edges as a function of the exposed trace and its anchor incidences. -/
@[expose] def exceptionalSelectedEdges (F : SimpleHypergraph V) (B : Finset V)
    (hpos : ∀ v ∈ B, 0 < vertexDegree F v) (v : ↥B) : Finset V :=
  traceSelectedEdge (exceptionalTrace B F) v.val
    (exceptionalTrace_incident_nonempty v (hpos v.val v.property))

lemma exceptionalSelectedEdges_spec (F : SimpleHypergraph V) (B : Finset V)
    (hpos : ∀ v ∈ B, 0 < vertexDegree F v) (v : ↥B) :
    exceptionalSelectedEdges F B hpos v ∈ F ∧ v.val ∈ exceptionalSelectedEdges F B hpos v := by
  have h := traceSelectedEdge_spec (exceptionalTrace B F) v.val
    (exceptionalTrace_incident_nonempty v (hpos v.val v.property))
  exact ⟨(mem_exceptionalTrace.mp h.1).1,h.2⟩

lemma exceptionalSelectedEdges_eq_of_trace_eq {F G : SimpleHypergraph V} (B : Finset V)
    (hF : ∀ v ∈ B, 0 < vertexDegree F v) (hG : ∀ v ∈ B, 0 < vertexDegree G v)
    (htrace : exceptionalTrace B F = exceptionalTrace B G) :
    exceptionalSelectedEdges F B hF = exceptionalSelectedEdges G B hG := by
  funext v
  unfold exceptionalSelectedEdges
  congr 1

/-- A disjoint exceptional edge with two retained ports at each anchor. -/
structure CoreBlockFamily (r : ℕ) (F : SimpleHypergraph V) (B : Finset V) where
  edge : ↥B → Finset V
  edge_mem : ∀ v, edge v ∈ F
  edge_card : ∀ v, (edge v).card = r
  anchor_mem : ∀ v, v.val ∈ edge v
  edge_disjoint : Pairwise (fun u v => Disjoint (edge u) (edge v))
  ports : ↥B → Finset V
  ports_card : ∀ v, (ports v).card = 2
  ports_subset : ∀ v, ports v ⊆ edge v
  anchor_not_ports : ∀ v, v.val ∉ ports v

namespace CoreBlockFamily
variable {r : ℕ} {F : SimpleHypergraph V} {B : Finset V}

@[expose] def privateBlock (C : CoreBlockFamily r F B) (v : ↥B) : Finset V := C.edge v \ C.ports v

@[expose] def deleted (C : CoreBlockFamily r F B) : Finset V := univ.biUnion C.privateBlock

@[expose] def coreVertices (C : CoreBlockFamily r F B) : Finset V := univ \ C.deleted

@[expose] def markers (C : CoreBlockFamily r F B) : Finset (Finset V) := univ.image C.ports

omit [Fintype V] in
lemma privateBlock_subset (C : CoreBlockFamily r F B) (v : ↥B) :
    C.privateBlock v ⊆ C.edge v := sdiff_subset

omit [Fintype V] in
@[simp] lemma privateBlock_card (C : CoreBlockFamily r F B) (v : ↥B) :
    (C.privateBlock v).card = r-2 := by
  rw [privateBlock,card_sdiff_of_subset (C.ports_subset v),C.edge_card,C.ports_card]

omit [Fintype V] in
lemma anchor_private (C : CoreBlockFamily r F B) (v : ↥B) : v.val ∈ C.privateBlock v :=
  mem_sdiff.mpr ⟨C.anchor_mem v,C.anchor_not_ports v⟩

lemma private_disjoint (C : CoreBlockFamily r F B) :
    Pairwise (fun u v => Disjoint (C.privateBlock u) (C.privateBlock v)) := by
  intro u v huv
  exact (C.edge_disjoint huv).mono (C.privateBlock_subset u) (C.privateBlock_subset v)

omit [Fintype V] [DecidableEq V] in
lemma ports_disjoint (C : CoreBlockFamily r F B) :
    Pairwise (fun u v => Disjoint (C.ports u) (C.ports v)) := by
  intro u v huv
  exact (C.edge_disjoint huv).mono (C.ports_subset u) (C.ports_subset v)

lemma ports_injective (C : CoreBlockFamily r F B) : Function.Injective C.ports := by
  intro u v huv
  by_contra hne
  have hd := C.ports_disjoint hne
  change Disjoint (C.ports u) (C.ports v) at hd
  rw [huv] at hd
  have he : C.ports v = ∅ := disjoint_self.mp hd
  have hc := C.ports_card v
  rw [he,card_empty] at hc
  omega

@[simp] lemma markers_card (C : CoreBlockFamily r F B) : C.markers.card = B.card := by
  rw [markers,card_image_of_injective _ C.ports_injective,card_univ,Fintype.card_coe]

lemma markers_matching (C : CoreBlockFamily r F B) : IsPairMatching C.markers := by
  constructor
  · intro e he
    obtain ⟨v,_,rfl⟩ := mem_image.mp he
    exact C.ports_card v
  · intro e he f hf hef
    obtain ⟨u,_,rfl⟩ := mem_image.mp he
    obtain ⟨v,_,rfl⟩ := mem_image.mp hf
    exact C.ports_disjoint (fun h => hef (congrArg C.ports h))

@[simp] lemma deleted_card (C : CoreBlockFamily r F B) : C.deleted.card = (r-2)*B.card := by
  rw [deleted,card_biUnion (by intro u _ v _ huv; exact C.private_disjoint huv)]
  simp [Nat.mul_comm]

@[simp] lemma coreVertices_card (C : CoreBlockFamily r F B) :
    C.coreVertices.card = Fintype.card V - (r-2)*B.card := by
  rw [coreVertices,card_sdiff_of_subset (subset_univ _),card_univ,C.deleted_card]

lemma anchors_deleted (C : CoreBlockFamily r F B) : B ⊆ C.deleted := by
  intro v hv
  exact mem_biUnion.mpr ⟨⟨v,hv⟩,mem_univ _,C.anchor_private _⟩

lemma ports_private_disjoint (C : CoreBlockFamily r F B) (u v : ↥B) :
    Disjoint (C.ports u) (C.privateBlock v) := by
  by_cases h : u=v
  · subst v
    exact disjoint_sdiff_self_right
  · exact (C.edge_disjoint h).mono (C.ports_subset _) (C.privateBlock_subset _)

lemma ports_core (C : CoreBlockFamily r F B) (v : ↥B) : C.ports v ⊆ C.coreVertices := by
  intro x hx
  refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
  intro hd
  obtain ⟨u,_,hu⟩ := mem_biUnion.mp hd
  exact disjoint_left.mp (C.ports_private_disjoint v u) hx hu

lemma core_size_identity (C : CoreBlockFamily r F B) (hr : 2 ≤ r) :
    C.coreVertices.card - C.markers.card = Fintype.card V - (r-1)*B.card := by
  rw [C.coreVertices_card,C.markers_card,Nat.sub_sub]
  congr 1
  have h : r-2+1=r-1 := by omega
  calc
    (r-2)*B.card+B.card = (r-2+1)*B.card := by ring
    _ = (r-1)*B.card := by rw [h]

lemma core_divisibility (C : CoreBlockFamily r F B) (hr : 2 ≤ r)
    (hdiv : r-1 ∣ Fintype.card V) : r-1 ∣ C.coreVertices.card-C.markers.card := by
  rw [C.core_size_identity hr]
  exact Nat.dvd_sub hdiv (dvd_mul_right _ _)

/-- Choose the two retained ports from each edge after excluding its anchor. -/
@[expose] def ofDisjointEdges {r : ℕ} (hr : 3 ≤ r) {F : SimpleHypergraph V} {B : Finset V}
    (edge : ↥B → Finset V) (hmem : ∀ v, edge v ∈ F)
    (hcard : ∀ v, (edge v).card=r) (hanchor : ∀ v, v.val ∈ edge v)
    (hdisj : Pairwise (fun u v => Disjoint (edge u) (edge v))) : CoreBlockFamily r F B := by
  have hex (v : ↥B) : ∃ P ⊆ (edge v).erase v.val, P.card=2 := by
    apply exists_subset_card_eq
    rw [card_erase_of_mem (hanchor v),hcard v]
    omega
  let ports := fun v => (hex v).choose
  exact ⟨edge,hmem,hcard,hanchor,hdisj,ports,
    fun v => (hex v).choose_spec.2,
    fun v => ((hex v).choose_spec.1).trans (erase_subset _ _),
    fun v hv => (notMem_erase v.val (edge v)) ((hex v).choose_spec.1 hv)⟩

omit [Fintype V] in
@[simp] lemma ofDisjointEdges_edge {r : ℕ} (hr : 3 ≤ r) {F : SimpleHypergraph V} {B : Finset V}
    (edge : ↥B → Finset V) (hmem : ∀ v, edge v ∈ F)
    (hcard : ∀ v, (edge v).card=r) (hanchor : ∀ v, v.val ∈ edge v)
    (hdisj : Pairwise (fun u v => Disjoint (edge u) (edge v))) :
    (ofDisjointEdges hr edge hmem hcard hanchor hdisj).edge = edge := rfl

/-- All choices of selected edges and ports are determined by the exposed trace. -/
@[expose] def ofTrace {r : ℕ} (hr : 3 ≤ r) {F : SimpleHypergraph V} {B : Finset V}
    (hF : F ⊆ completeEdges V r) (hpos : ∀ v ∈ B, 0 < vertexDegree F v)
    (hdisj : Pairwise (fun u v => Disjoint (exceptionalSelectedEdges F B hpos u)
      (exceptionalSelectedEdges F B hpos v))) : CoreBlockFamily r F B :=
  ofDisjointEdges hr (exceptionalSelectedEdges F B hpos)
    (fun v => (exceptionalSelectedEdges_spec F B hpos v).1)
    (fun v => (mem_completeEdges r _).mp (hF (exceptionalSelectedEdges_spec F B hpos v).1))
    (fun v => (exceptionalSelectedEdges_spec F B hpos v).2) hdisj

omit [Fintype V] in
lemma ofDisjointEdges_ports_eq {r : ℕ} (hr : 3 ≤ r) {F G : SimpleHypergraph V}
    {B : Finset V} (edge edge' : ↥B → Finset V) (he : edge=edge')
    (hmem : ∀ v, edge v ∈ F) (hcard : ∀ v, (edge v).card=r)
    (hanchor : ∀ v, v.val ∈ edge v)
    (hdisj : Pairwise (fun u v => Disjoint (edge u) (edge v)))
    (hmem' : ∀ v, edge' v ∈ G) (hcard' : ∀ v, (edge' v).card=r)
    (hanchor' : ∀ v, v.val ∈ edge' v)
    (hdisj' : Pairwise (fun u v => Disjoint (edge' u) (edge' v))) :
    (ofDisjointEdges hr edge hmem hcard hanchor hdisj).ports =
      (ofDisjointEdges hr edge' hmem' hcard' hanchor' hdisj').ports := by
  subst edge'
  rfl

/-- Even the retained port choices are unchanged when the exposed traces agree. -/
lemma ofTrace_ports_eq_of_trace_eq {r : ℕ} (hr : 3 ≤ r) {F G : SimpleHypergraph V}
    {B : Finset V} (hF : F ⊆ completeEdges V r) (hG : G ⊆ completeEdges V r)
    (hpos : ∀ v ∈ B, 0 < vertexDegree F v) (hpos' : ∀ v ∈ B, 0 < vertexDegree G v)
    (hdisj : Pairwise (fun u v => Disjoint (exceptionalSelectedEdges F B hpos u)
      (exceptionalSelectedEdges F B hpos v)))
    (hdisj' : Pairwise (fun u v => Disjoint (exceptionalSelectedEdges G B hpos' u)
      (exceptionalSelectedEdges G B hpos' v)))
    (htrace : exceptionalTrace B F=exceptionalTrace B G) :
    (ofTrace hr hF hpos hdisj).ports = (ofTrace hr hG hpos' hdisj').ports := by
  apply ofDisjointEdges_ports_eq
  exact exceptionalSelectedEdges_eq_of_trace_eq B hpos hpos' htrace

/-- The entire deleted set is determined by the exposed exceptional trace. -/
lemma ofTrace_deleted_eq_of_trace_eq {r : ℕ} (hr : 3 ≤ r) {F G : SimpleHypergraph V}
    {B : Finset V} (hF : F ⊆ completeEdges V r) (hG : G ⊆ completeEdges V r)
    (hpos : ∀ v ∈ B, 0 < vertexDegree F v) (hpos' : ∀ v ∈ B, 0 < vertexDegree G v)
    (hdisj : Pairwise (fun u v => Disjoint (exceptionalSelectedEdges F B hpos u)
      (exceptionalSelectedEdges F B hpos v)))
    (hdisj' : Pairwise (fun u v => Disjoint (exceptionalSelectedEdges G B hpos' u)
      (exceptionalSelectedEdges G B hpos' v)))
    (htrace : exceptionalTrace B F=exceptionalTrace B G) :
    (ofTrace hr hF hpos hdisj).deleted = (ofTrace hr hG hpos' hdisj').deleted := by
  have hp := ofTrace_ports_eq_of_trace_eq hr hF hG hpos hpos' hdisj hdisj' htrace
  have he := exceptionalSelectedEdges_eq_of_trace_eq B hpos hpos' htrace
  apply Finset.biUnion_congr rfl
  intro v _
  unfold privateBlock
  rw [hp]
  exact congrArg (fun E => E \ (ofTrace hr hG hpos' hdisj').ports v) (congrFun he v)

/-- Marker pairs carry the same labels as the exceptional anchors. -/
@[expose] def portsEquiv (C : CoreBlockFamily r F B) : ↥B ≃ ↥C.markers :=
  Equiv.ofBijective (fun v => ⟨C.ports v,mem_image.mpr ⟨v,mem_univ _,rfl⟩⟩) (by
    constructor
    · intro u v h
      exact C.ports_injective (congrArg Subtype.val h)
    · intro p
      obtain ⟨v,_,hv⟩ := mem_image.mp p.property
      exact ⟨v,Subtype.ext hv⟩)

/-- Private vertices indexed by marker pairs, with the empty value off the marker set. -/
@[expose] def markerPrivate (C : CoreBlockFamily r F B) (p : Finset V) : Finset V :=
  if hp : p ∈ C.markers then C.privateBlock (C.portsEquiv.symm ⟨p,hp⟩) else ∅

@[simp] lemma markerPrivate_ports (C : CoreBlockFamily r F B) (v : ↥B) :
    C.markerPrivate (C.ports v) = C.privateBlock v := by
  have hp : C.ports v ∈ C.markers := mem_image.mpr ⟨v,mem_univ _,rfl⟩
  rw [markerPrivate,dif_pos hp]
  congr 1
  exact C.portsEquiv.symm_apply_apply v

lemma markerPrivate_card (C : CoreBlockFamily r F B) {p : Finset V} (hp : p ∈ C.markers) :
    (C.markerPrivate p).card=r-2 := by
  obtain ⟨v,_,rfl⟩ := mem_image.mp hp
  rw [C.markerPrivate_ports,C.privateBlock_card]

lemma markerPrivate_disjoint (C : CoreBlockFamily r F B) :
    (C.markers : Set (Finset V)).Pairwise (fun p q => Disjoint (C.markerPrivate p) (C.markerPrivate q)) := by
  intro p hp q hq hpq
  obtain ⟨u,_,rfl⟩ := mem_image.mp hp
  obtain ⟨v,_,rfl⟩ := mem_image.mp hq
  rw [C.markerPrivate_ports,C.markerPrivate_ports]
  exact C.private_disjoint (fun h => hpq (congrArg C.ports h))

lemma markerPrivate_outside (C : CoreBlockFamily r F B) (p : Finset V) :
    Disjoint C.coreVertices (C.markerPrivate p) := by
  by_cases hp : p ∈ C.markers
  · obtain ⟨v,_,rfl⟩ := mem_image.mp hp
    rw [C.markerPrivate_ports]
    apply disjoint_left.mpr
    intro x hx hxv
    exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨v,mem_univ _,hxv⟩)
  · simp [markerPrivate,hp]

lemma markerPrivate_union (C : CoreBlockFamily r F B) :
    C.markers.biUnion C.markerPrivate = C.deleted := by
  ext x
  simp only [markers,mem_biUnion,mem_image,mem_univ,exists_true_left,true_and]
  constructor
  · rintro ⟨p,⟨v,rfl⟩,hx⟩
    exact mem_biUnion.mpr ⟨v,mem_univ _,by simpa using hx⟩
  · intro hx
    obtain ⟨v,_,hv⟩ := mem_biUnion.mp hx
    exact ⟨C.ports v,⟨v,rfl⟩,by simpa using hv⟩

lemma markerPrivate_cover (C : CoreBlockFamily r F B) :
    C.coreVertices ∪ C.markers.biUnion C.markerPrivate = univ := by
  rw [C.markerPrivate_union,coreVertices,sdiff_union_of_subset (subset_univ _)]

lemma expanded_marker_mem (C : CoreBlockFamily r F B) {p : Finset V} (hp : p ∈ C.markers) :
    p ∪ C.markerPrivate p ∈ F := by
  obtain ⟨v,_,rfl⟩ := mem_image.mp hp
  rw [C.markerPrivate_ports,privateBlock,union_sdiff_of_subset (C.ports_subset v)]
  exact C.edge_mem v

end CoreBlockFamily
end LooseHamilton
