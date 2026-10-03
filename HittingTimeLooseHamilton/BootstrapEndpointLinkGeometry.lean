module

public import HittingTimeLooseHamilton.EndpointBadRootCounting
public import HittingTimeLooseHamilton.DeletedRootCollision

public section

noncomputable section
namespace LooseHamilton.BootstrapEndpointLinkGeometry
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def cutDeleted (y : V) : RootFreeEndpointLabel V → Finset V
  | .inl l => l.deleted y
  | .inr l => l.deleted y

@[expose] def cutEndpoint : RootFreeEndpointLabel V → V
  | .inl l => l.1
  | .inr l => l.2.2.1

/-- All fixed labels a fresh inner edge must avoid, apart from its root. -/
@[expose] def exclusions (M : Finset (Finset V)) (P U : Finset V) (y z t : V)
    (l : RootFreeEndpointLabel V) : Finset V :=
  (P ∪ cutDeleted y l ∪ originalPorts M ∪ {y,z,cutEndpoint l,t} ∪ U).erase y

private theorem split_general {r : ℕ} (hr : 2 ≤ r)
    (M G : Finset (Finset V)) (P D U : Finset V) (y z a t : V)
    (ht : t ∉ P ∪ D ∪ originalPorts M ∪ {y,z,a})
    (e : Finset V) (he : e ∈ rootEdgeUniverse r y)
    (hd : Disjoint (e.erase y) (P ∪ D ∪ originalPorts M ∪ {y,z,a,t} ∪ U)) :
    e ∈ allowedEdges r U ∧ ∃ Q v, {y,v} ∪ Q = e ∧
      EndpointSpliceLegal r M (insert e (rootFreeEdges y G)) P D y z a t Q v := by
  obtain ⟨hecard,hye⟩ := (mem_rootEdgeUniverse r y e).mp he
  have hAc : (e.erase y).card = r-1 := by rw [card_erase_of_mem hye,hecard]
  have hAn : (e.erase y).Nonempty := card_pos.mp (by omega)
  obtain ⟨v,hv⟩ := hAn
  let Q := (e.erase y).erase v
  have hvfresh : v ∉ P ∪ D ∪ originalPorts M ∪ {y,z,a,t} :=
    fun h => disjoint_left.mp hd hv (mem_union_left _ h)
  have hQ : Disjoint Q (P ∪ D ∪ originalPorts M ∪ {a,z,v,t}) := by
    apply disjoint_left.mpr
    intro w hw hwF
    have hwA := (mem_erase.mp hw).2
    have hwv := (mem_erase.mp hw).1
    apply disjoint_left.mp hd hwA
    simp only [mem_union,mem_insert,mem_singleton] at hwF ⊢
    rcases hwF with ((hP | hD) | hM) | ha | hz | hv' | ht'
    · tauto
    · tauto
    · tauto
    · tauto
    · tauto
    · exact False.elim (hwv hv')
    · tauto
  have hrec : {y,v} ∪ Q = e := by
    ext w
    simp only [Q,mem_union,mem_insert,mem_singleton,mem_erase]
    have hvE := (mem_erase.mp hv).2
    constructor
    · rintro ((rfl | rfl) | ⟨_,_,hw⟩) <;> assumption
    · intro hw
      by_cases hy : w = y
      · exact Or.inl (Or.inl hy)
      by_cases hv' : w = v
      · exact Or.inl (Or.inr hv')
      exact Or.inr ⟨hv',hy,hw⟩
  have hall : e ∈ allowedEdges r U := by
    apply (mem_allowedEdges r U e).mpr
    refine ⟨hecard, (card_le_card (show e ∩ U ⊆ {y} from ?_)).trans (by simp)⟩
    intro w hw
    by_cases hwy : w = y
    · simp [hwy]
    · exact False.elim (disjoint_left.mp hd
        (mem_erase.mpr ⟨hwy,(mem_inter.mp hw).1⟩)
        (mem_union_right _ (mem_inter.mp hw).2))
  refine ⟨hall,Q,v,hrec,?_,hvfresh,ht,hQ,?_⟩
  · dsimp [Q]
    rw [card_erase_of_mem hv,hAc]
    omega
  · rw [hrec]
    exact mem_insert_self _ _

/-- A noncolliding root edge has a counterfactual legal split for either cut type.
The host is consulted only through its root-free restriction. -/
theorem split_of_not_collision {r : ℕ} (hr : 2 ≤ r)
    (M G : Finset (Finset V)) (P U : Finset V) (y z t : V)
    (l : RootFreeEndpointLabel V)
    (ht : t ∉ P ∪ cutDeleted y l ∪ originalPorts M ∪ {y,z,cutEndpoint l})
    (e : Finset V) (he : e ∈ rootEdgeUniverse r y)
    (hc : e ∉ deletedRootCollisions r y (exclusions M P U y z t l)) :
    e ∈ allowedEdges r U ∧ ∃ q, RootFreeEndpointSplit r M G P y z t e l q := by
  have hs : e ⊆ univ \ exclusions M P U y z t l := by
    simpa only [deletedRootCollisions,mem_filter,he,true_and,not_not] using hc
  have hd : Disjoint (e.erase y)
      (P ∪ cutDeleted y l ∪ originalPorts M ∪ {y,z,cutEndpoint l,t} ∪ U) := by
    apply disjoint_left.mpr
    intro v hv hvF
    exact (mem_sdiff.mp (hs (mem_erase.mp hv).2)).2
      (mem_erase.mpr ⟨(mem_erase.mp hv).1,hvF⟩)
  obtain ⟨hall,Q,v,hrec,hsplit⟩ := split_general hr M G P (cutDeleted y l) U
    y z (cutEndpoint l) t ht e he hd
  refine ⟨hall,(Q,v),?_⟩
  cases l <;> exact ⟨hrec,hsplit⟩

theorem invalid_subset_collisions {r : ℕ} (hr : 2 ≤ r)
    (M G : Finset (Finset V)) (P U : Finset V) (y z t : V)
    (l : RootFreeEndpointLabel V)
    (ht : t ∉ P ∪ cutDeleted y l ∪ originalPorts M ∪ {y,z,cutEndpoint l}) :
    endpointRootInvalidEdges r M G P U y z t l ⊆
      deletedRootCollisions r y (exclusions M P U y z t l) := by
  classical
  intro e he
  obtain ⟨he,hbad⟩ := mem_filter.mp he
  by_contra hc
  obtain ⟨hall,hq⟩ := split_of_not_collision hr M G P U y z t l ht e he hc
  exact hbad.elim (fun h => h hall) (fun h => h hq)

theorem invalid_card_le {r : ℕ} (hr : 2 ≤ r)
    (M G : Finset (Finset V)) (P U : Finset V) (y z t : V)
    (l : RootFreeEndpointLabel V)
    (ht : t ∉ P ∪ cutDeleted y l ∪ originalPorts M ∪ {y,z,cutEndpoint l}) :
    (endpointRootInvalidEdges r M G P U y z t l).card ≤
      (exclusions M P U y z t l).card * (Fintype.card V-2).choose (r-2) :=
  (card_le_card (invalid_subset_collisions hr M G P U y z t l ht)).trans
    (deletedRootCollisions_card_le hr y _ (notMem_erase _ _))


theorem cutDeleted_card_I {r : ℕ} (M G : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelI V)
    (hl : EndpointCutLegalI r M G P y z l) :
    (cutDeleted y (.inl l)).card ≤ r-2+1 := by
  simpa only [cutDeleted,EndpointCutLabelI.deleted,hl.private_card] using
    card_insert_le y l.2

theorem cutDeleted_card_II {r : ℕ} (M G : Finset (Finset V)) (P : Finset V)
    (y z : V) (l : EndpointCutLabelII V)
    (hl : EndpointCutLegalII r M G P y z l) :
    (cutDeleted y (.inr l)).card ≤ 2*(r-2)+3 := by
  have h0 : ({y,l.1,l.2.1} : Finset V).card ≤ 3 := by
    exact (card_insert_le _ _).trans (by have := card_insert_le l.1 {l.2.1}; simp only [card_singleton] at this; omega)
  have h1 := card_union_le ({y,l.1,l.2.1} : Finset V) l.2.2.2.1
  have h2 := card_union_le (({y,l.1,l.2.1} : Finset V) ∪ l.2.2.2.1) l.2.2.2.2
  simp only [hl.first_private_card,hl.second_private_card] at h1 h2
  change (({y,l.1,l.2.1} ∪ l.2.2.2.1) ∪ l.2.2.2.2).card ≤ _
  omega

theorem exclusions_card_le (M : Finset (Finset V)) (P U : Finset V)
    (y z t : V) (l : RootFreeEndpointLabel V) :
    (exclusions M P U y z t l).card ≤
      P.card + (cutDeleted y l).card + (originalPorts M).card + 4 + U.card := by
  have h0 : ({y,z,cutEndpoint l,t} : Finset V).card ≤ 4 := by
    have h1 := card_insert_le y {z,cutEndpoint l,t}
    have h2 := card_insert_le z {cutEndpoint l,t}
    have h3 := card_insert_le (cutEndpoint l) {t}
    simp only [card_singleton] at h3
    omega
  have h1 := card_union_le P (cutDeleted y l)
  have h2 := card_union_le (P ∪ cutDeleted y l) (originalPorts M)
  have h3 := card_union_le (P ∪ cutDeleted y l ∪ originalPorts M) {y,z,cutEndpoint l,t}
  have h4 := card_union_le (P ∪ cutDeleted y l ∪ originalPorts M ∪ {y,z,cutEndpoint l,t}) U
  have h5 : ((P ∪ cutDeleted y l ∪ originalPorts M ∪ {y,z,cutEndpoint l,t} ∪ U).erase y).card ≤
      (P ∪ cutDeleted y l ∪ originalPorts M ∪ {y,z,cutEndpoint l,t} ∪ U).card := card_erase_le
  unfold exclusions
  omega


/-- Fixed original ports already cover all residual marker ports, so they are
counted only once. -/
theorem exclusions_card_le_of_ports_subset (M : Finset (Finset V)) (P U : Finset V)
    (y z t : V) (l : RootFreeEndpointLabel V) (hports : originalPorts M ⊆ U) :
    (exclusions M P U y z t l).card ≤
      P.card + (cutDeleted y l).card + 4 + U.card := by
  have hsub : exclusions M P U y z t l ⊆ P ∪ cutDeleted y l ∪ {y,z,cutEndpoint l,t} ∪ U := by
    intro v hv
    have hv' := (mem_erase.mp hv).2
    simp only [mem_union] at hv' ⊢
    rcases hv' with (((hP | hD) | hM) | hn) | hU
    · tauto
    · tauto
    · exact Or.inr (hports hM)
    · tauto
    · tauto
  have h0 : ({y,z,cutEndpoint l,t} : Finset V).card ≤ 4 := by
    have h1 := card_insert_le y {z,cutEndpoint l,t}
    have h2 := card_insert_le z {cutEndpoint l,t}
    have h3 := card_insert_le (cutEndpoint l) {t}
    simp only [card_singleton] at h3
    omega
  have h1 := card_union_le P (cutDeleted y l)
  have h2 := card_union_le (P ∪ cutDeleted y l) {y,z,cutEndpoint l,t}
  have h3 := card_union_le (P ∪ cutDeleted y l ∪ {y,z,cutEndpoint l,t}) U
  have h4 := card_le_card hsub
  omega

theorem invalid_density_le {r : ℕ} (hr : 2 ≤ r) (hN : 2 ≤ Fintype.card V)
    (M G : Finset (Finset V)) (P U : Finset V) (y z t : V)
    (l : RootFreeEndpointLabel V)
    (ht : t ∉ P ∪ cutDeleted y l ∪ originalPorts M ∪ {y,z,cutEndpoint l}) :
    rootLinkDensity r y (endpointRootInvalidEdges r M G P U y z t l) ≤
      ((exclusions M P U y z t l).card : ℝ) * (r-1:ℕ) / (Fintype.card V-1:ℕ) := by
  have hc := card_le_card (invalid_subset_collisions hr M G P U y z t l ht)
  calc
    _ ≤ rootLinkDensity r y (deletedRootCollisions r y (exclusions M P U y z t l)) := by
      unfold rootLinkDensity
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) (by positivity)
    _ ≤ _ := deletedRootCollisions_density_le hr hN y _ (notMem_erase _ _)

end LooseHamilton.BootstrapEndpointLinkGeometry
