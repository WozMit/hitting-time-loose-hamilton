module

public import HittingTimeLooseHamilton.PortContractionOriginal
public import HittingTimeLooseHamilton.CompletionMarginalCap

public section

/-! Conversion of the actual original-port contraction counts into true-edge
marginal bounds. A harmless `choose r 2` upper bound avoids needing a separate
optimization of the number of possible other junctions. -/
noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every nonempty endpoint-role class of an edge at an original port is one
of the genuine original-port contraction classes. -/
theorem port_edgeRole_le {r : ℕ} (hr : 3 ≤ r)
    (M₀ G : Finset (Finset V)) (y z : V) (hyz : y ≠ z)
    (hm : {y,z} ∈ M₀) (hM : (M₀ : Set (Finset V)).PairwiseDisjoint id)
    (hG : G ⊆ allowedEdges r (originalPorts M₀))
    (hsize : 5*(r-1) < Fintype.card V) (e q : Finset V) (hye : y ∈ e)
    (T : ℝ) (hT : 0 ≤ T)
    (hb : ∀ l : EndpointCutLabelI V,
      EndpointCutLegalI r (M₀.erase {y,z}) G ∅ y z l → l.edge y = e →
      (rootFreePortCompletion r M₀ G y z l.2 {l.1,z}:ℝ) ≤ T) :
    ((edgeRoleFamily r M₀ G e q).card:ℝ) ≤ T := by
  classical
  by_cases hn : (edgeRoleFamily r M₀ G e q).Nonempty
  · obtain ⟨E,hE⟩ := hn
    obtain ⟨hC,hEG,heE,hq⟩ := (mem_edgeRoleFamily _ _ _ _ _ _ hr).mp hE
    have hsource : E ∈ completionFamily r (M₀.erase {y,z}) G ∅ {y,z} := by
      apply (mem_completionFamily _ _ _ _ _ _).mpr
      simp only [sdiff_empty,insert_erase hm,isMixedCycleOn_univ_iff]
      exact ⟨hC,hEG⟩
    obtain ⟨⟨C⟩,_⟩ := (mem_completionFamily _ _ _ _ _ _).mp hsource
    have hd := port_pair_disjoint_remainder M₀ y z hM hm
    have hy : y ∈ originalPorts M₀ := mem_biUnion.mpr ⟨{y,z},hm,by simp⟩
    have hp : originalPorts (M₀.erase {y,z}) ⊆ originalPorts M₀ := by
      intro v hv
      obtain ⟨m,hm',hv⟩ := mem_biUnion.mp hv
      exact mem_biUnion.mpr ⟨m,(mem_erase.mp hm').2,hv⟩
    have hM' : ((M₀.erase {y,z} : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id :=
      by
        intro m hm' n hn' hmn
        exact hM (mem_erase.mp hm').2 (mem_erase.mp hn').2 hmn
    rcases portCut_contraction hr hyz hd hy hp hG hsize E hsource with
      ⟨l,hl,F,hF,hFE⟩ | ⟨l,hl,_⟩
    · have hleE : l.edge y ∈ E := by rw [←hFE]; simp
      have hle : l.edge y = e := congrArg Subtype.val
        (C.ordinary_incident_marked_unique ⟨{y,z},by simp⟩
          ⟨l.edge y,hleE⟩ ⟨e,heE⟩ (by simp)
          (by simp [EndpointCutLabelI.edge]) hye)
      have hlq : edgeEndpointPair M₀ E e = {y,l.1} := by
        have hh := (portCut_expand_I hr hyz hd hM' hl hF).2
        rw [hFE,insert_erase hm,hle] at hh
        exact hh
      have hq' : q = {y,l.1} := hq.symm.trans hlq
      have hsub : edgeRoleFamily r M₀ G e q ⊆
          portIncidentFamily r (M₀.erase {y,z}) G y z l := by
        intro E' hE'
        obtain ⟨hC',hEG',heE',hqE'⟩ := (mem_edgeRoleFamily _ _ _ _ _ _ hr).mp hE'
        apply mem_filter.mpr
        refine ⟨?_,?_,?_⟩
        · apply (mem_completionFamily _ _ _ _ _ _).mpr
          simp only [sdiff_empty,insert_erase hm,isMixedCycleOn_univ_iff]
          exact ⟨hC',hEG'⟩
        · simpa only [hle] using heE'
        · simpa only [insert_erase hm,hle,hq'] using hqE'
      have hc := card_le_card hsub
      rw [original_port_incident_count hr M₀ G y z hyz hm hM hG hsize l hl] at hc
      exact (Nat.cast_le.mpr hc).trans (hb l hl hle)
    · exact False.elim (portCut_no_typeII hy hp hG hd l hl)
  · simpa only [not_nonempty_iff_eq_empty.mp hn,card_empty,Nat.cast_zero] using hT

/-- A uniform cap for all actual port contractions bounds every true edge
through that port, via the intrinsic endpoint-pair partition. -/
theorem port_edge_incidence_le {r : ℕ} (hr : 3 ≤ r)
    (M₀ G : Finset (Finset V)) (y z : V) (hyz : y ≠ z)
    (hm : {y,z} ∈ M₀) (hM : (M₀ : Set (Finset V)).PairwiseDisjoint id)
    (hG : G ⊆ allowedEdges r (originalPorts M₀))
    (hsize : 5*(r-1) < Fintype.card V) (e : Finset V) (he : e.card = r) (hye : y ∈ e)
    (T : ℝ) (hT : 0 ≤ T)
    (hb : ∀ l : EndpointCutLabelI V,
      EndpointCutLegalI r (M₀.erase {y,z}) G ∅ y z l → l.edge y = e →
      (rootFreePortCompletion r M₀ G y z l.2 {l.1,z}:ℝ) ≤ T) :
    (FiniteFamily.incidenceCount (unrestrictedCycleFamily r M₀ G) e:ℝ) ≤
      (r.choose 2:ℝ)*T := by
  rw [edge_incidence_partition _ _ _ _ hr,Nat.cast_sum]
  calc
    _ ≤ ∑ _q ∈ e.powersetCard 2, T := sum_le_sum (fun q _ =>
      port_edgeRole_le hr M₀ G y z hyz hm hM hG hsize e q hye T hT hb)
    _ = _ := by simp [he]

/-- Dividing the true incidence bound by the actual cycle count gives the
original-port edge marginal bound. -/
theorem port_edge_marginal_le {r : ℕ} (hr : 3 ≤ r)
    (M₀ G : Finset (Finset V)) (y z : V) (hyz : y ≠ z)
    (hm : {y,z} ∈ M₀) (hM : (M₀ : Set (Finset V)).PairwiseDisjoint id)
    (hG : G ⊆ allowedEdges r (originalPorts M₀))
    (hsize : 5*(r-1) < Fintype.card V) (e : Finset V) (he : e.card = r) (hye : y ∈ e)
    (D μ : ℝ) (hD : 0 ≤ D) (hμ : 0 < μ)
    (hX : 0 < unrestrictedCycleCount r M₀ G)
    (hb : ∀ l : EndpointCutLabelI V,
      EndpointCutLegalI r (M₀.erase {y,z}) G ∅ y z l → l.edge y = e →
      (rootFreePortCompletion r M₀ G y z l.2 {l.1,z}:ℝ) ≤
        D*(unrestrictedCycleCount r M₀ G:ℝ)/μ) :
    FiniteFamily.marginal (unrestrictedCycleFamily r M₀ G) e ≤
      (r.choose 2:ℝ)*D/μ := by
  have hp : (0:ℝ)<unrestrictedCycleCount r M₀ G := Nat.cast_pos.mpr hX
  change (_:ℝ)/(unrestrictedCycleCount r M₀ G:ℝ) ≤ _
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ (r.choose 2:ℝ)*(D*(unrestrictedCycleCount r M₀ G:ℝ)/μ) :=
      port_edge_incidence_le hr M₀ G y z hyz hm hM hG hsize e he hye _
        (by positivity) hb
    _ = _ := by ring

end LooseHamilton
