module

public import HittingTimeLooseHamilton.DirectedSpliceExchange
public import HittingTimeLooseHamilton.EndpointSpliceLegal

public section
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The label conditions discharge every freshness condition of the cycle exchange. -/
theorem endpointSplice_exchange {r : ℕ} {M N G F : Finset (Finset V)}
    {P D Q : Finset V} {y z a t v : V}
    (hr : 3 ≤ r) (hs : LegalPrivateCompletion r M P {y,z})
    (hM : (M : Set (Finset V)).PairwiseDisjoint id) (hNsub : N ⊆ M)
    (ha : a ∉ P ∪ originalPorts M ∪ {y,z})
    (hb : EndpointSpliceLegal r M G P D y z a t Q v)
    (h : rootedDirectedCycleOn r (univ \ (P ∪ D ∪ Q))
      (insert {v,t} (insert {a,z} N)) F
      ⟨{a,z},mem_insert_of_mem (mem_insert_self _ _)⟩
      ⟨{v,t},mem_insert_self _ _⟩ a v) :
    ∃ C : MixedCycleOnWitness r (univ \ (P ∪ D ∪ Q)) (insert {v,a} (insert {t,z} N)) F,
      C.slot ⟨0,by have := C.length_ge; omega⟩ = .inl ⟨{v,a},mem_insert_self _ _⟩ ∧
      C.junction ⟨0,by have := C.length_ge; omega⟩ = v ∧
      C.junction ⟨1,by have := C.length_ge; omega⟩ = a ∧
      C.junction (C.slot.symm (.inl ⟨{t,z},mem_insert_of_mem (mem_insert_self _ _)⟩)) = t := by
  have port_mono : originalPorts N ⊆ originalPorts M := by
    intro w hw
    obtain ⟨m,hm,hw⟩ := mem_biUnion.mp hw
    exact mem_biUnion.mpr ⟨m,hNsub hm,hw⟩
  have haM : a ∉ originalPorts M := fun hh => ha (by simp only [mem_union]; tauto)
  have hzM : z ∉ originalPorts M := fun hh =>
    disjoint_left.mp hs.ports_disjoint (by simp) hh
  have haz : a ≠ z := by intro hh; exact ha (by simp [hh])
  have hat : a ≠ t := Ne.symm hb.target_ne_a
  have hav : a ≠ v := Ne.symm hb.newEndpoint_ne_a
  have hazN : ({a,z} : Finset V) ∉ N := fun hh =>
    haM (port_mono (mem_biUnion.mpr ⟨{a,z},hh,by simp⟩))
  have hvtN : ({v,t} : Finset V) ∉ N := fun hh =>
    hb.newEndpoint_not_ports (port_mono (mem_biUnion.mpr ⟨{v,t},hh,by simp⟩))
  have hztN : ({z,t} : Finset V) ∉ N := fun hh =>
    hb.target_not_ports (port_mono (mem_biUnion.mpr ⟨{z,t},hh,by simp⟩))
  have hp : ({a,z} : Finset V) ∉ insert {v,t} N := by
    intro hh
    rcases mem_insert.mp hh with he | hh
    · have hh : a ∈ ({v,t} : Finset V) := he ▸ (by simp)
      simpa [hav,hat] using hh
    · exact hazN hh
  have hp' : ({a,v} : Finset V) ∉ insert {z,t} N := by
    intro hh
    rcases mem_insert.mp hh with he | hh
    · have hh : v ∈ ({z,t} : Finset V) := he ▸ (by simp)
      simpa [hb.newEndpoint_ne_z,hb.newEndpoint_ne_t] using hh
    · exact hb.newEndpoint_not_ports (port_mono (mem_biUnion.mpr ⟨{a,v},hh,by simp⟩))
  have hN : (N : Set (Finset V)).PairwiseDisjoint id :=
    fun _ hm _ hn hmn => hM (hNsub hm) (hNsub hn) hmn
  have hmatch : ((insert ({a,v} : Finset V) (insert {z,t} N) : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
    apply insert_two_markers_matching hN
    · apply disjoint_left.mpr
      intro w hw hm
      rcases mem_insert.mp hw with rfl | hw
      · exact haM (port_mono hm)
      · exact hb.newEndpoint_not_ports (port_mono (mem_singleton.mp hw ▸ hm))
    · apply disjoint_left.mpr
      intro w hw hm
      rcases mem_insert.mp hw with rfl | hw
      · exact hzM (port_mono hm)
      · exact hb.target_not_ports (port_mono (mem_singleton.mp hw ▸ hm))
    · simp only [disjoint_left,mem_insert,mem_singleton]
      intro w hw hw'
      rcases hw with rfl | rfl <;> rcases hw' with hh | hh
      · exact haz hh
      · exact hat hh
      · exact hb.newEndpoint_ne_z hh
      · exact hb.newEndpoint_ne_t hh
  have h' : rootedDirectedCycleOn r (univ \ (P ∪ D ∪ Q))
      (insert {a,z} (insert {v,t} N)) F
      ⟨{a,z},mem_insert_self _ _⟩
      ⟨{v,t},mem_insert_of_mem (mem_insert_self _ _)⟩ a v :=
    (rootedDirectedCycleOn_congr (insert_comm ({v,t} : Finset V) {a,z} N) (rfl : F = F)
      ⟨{a,z},mem_insert_of_mem (mem_insert_self _ _)⟩ ⟨{v,t},mem_insert_self _ _⟩
      ⟨{a,z},mem_insert_self _ _⟩ ⟨{v,t},mem_insert_of_mem (mem_insert_self _ _)⟩
      rfl rfl a v).mp h
  exact directed_marker_exchange_normalized hr haz hb.newEndpoint_ne_t hb.newEndpoint_ne_a
    hp hvtN hp' hztN hmatch h'
end LooseHamilton
