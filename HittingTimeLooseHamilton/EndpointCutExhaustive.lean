module

public import HittingTimeLooseHamilton.EndpointCutBijection
public import HittingTimeLooseHamilton.EndpointCutContractionFamily
public import HittingTimeLooseHamilton.EndpointCutSelection
public import HittingTimeLooseHamilton.ActiveCycleSize

public section

/-! # Every source cycle contracts to exactly one of the labelled core types -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r : ℕ} {M G : Finset (Finset V)} {P U : Finset V} {y z : V}

theorem endpointCut_contraction_exhaustive (hr : 3 ≤ r)
    (hs : LegalPrivateCompletion r M P {y,z})
    (hports : EndpointSourcePorts U M y z) (hG : G ⊆ allowedEdges r U)
    (hsize : 5 * (r - 1) < (univ \ P).card) :
    EndpointCutContractionProperty r M G P y z := by
  intro F hF
  obtain ⟨⟨C⟩,hFG⟩ := (mem_completionFamily _ _ _ _ _ _).mp hF
  have hzy : z ≠ y := by
    intro he
    have hc := hs.pair_card
    simp [he] at hc
  obtain ⟨D,h₀,hz,hy⟩ := C.exists_rooted ⟨{y,z}, mem_insert_self _ _⟩ z y
    (by simp [pair_comm]) hzy
  have hn := D.six_le_length_of_active_card hr hsize
  obtain ⟨e,he,hcases⟩ := D.select_endpoint_cut hn U G hports hG hFG h₀ hz hy
  have heval : e.val = {y,D.junction ⟨2,by omega⟩} ∪ D.privateBlock e := by
    have hh := D.slot_edge ⟨1,by omega⟩
    rw [he] at hh
    simpa only [MixedCycleOnWitness.rotate_mk_succ (n := D.length) (k := 1) (by omega), hy] using hh
  rcases hcases with hI | ⟨m,f,hm,hf,hII⟩
  · left
    refine ⟨(D.junction ⟨2,by omega⟩, D.privateBlock e), hI,
      F.erase e.val, D.endpointCut_coreI hn e h₀ he hz hy hs hFG hI, ?_⟩
    change insert ({y,D.junction ⟨2,by omega⟩} ∪ D.privateBlock e) (F.erase e.val) = F
    rw [← heval]
    exact insert_erase e.property
  · right
    have hfval : f.val = {D.junction ⟨3,by omega⟩,D.junction ⟨4,by omega⟩} ∪ D.privateBlock f := by
      have hh := D.slot_edge ⟨3,by omega⟩
      rw [hf] at hh
      simpa only [MixedCycleOnWitness.rotate_mk_succ (n := D.length) (k := 3) (by omega)] using hh
    have hne : f.val ≠ e.val := by
      intro h
      have hef : e = f := Subtype.ext h.symm
      have hi := D.slot.injective (he.trans (congrArg Sum.inr hef) |>.trans hf.symm)
      have hv : (1 : ℕ) = 3 := congrArg Fin.val hi
      omega
    refine ⟨(D.junction ⟨2,by omega⟩,D.junction ⟨3,by omega⟩,
      D.junction ⟨4,by omega⟩,D.privateBlock e,D.privateBlock f),hII,
      (F.erase e.val).erase f.val,
      D.endpointCut_coreII hn m e f h₀ he hm hf hz hy hs hFG hII,?_⟩
    change insert ({y,D.junction ⟨2,by omega⟩} ∪ D.privateBlock e)
      (insert ({D.junction ⟨3,by omega⟩,D.junction ⟨4,by omega⟩} ∪ D.privateBlock f)
        ((F.erase e.val).erase f.val)) = F
    rw [← heval, ← hfval, insert_erase (mem_erase.mpr ⟨hne,f.property⟩), insert_erase e.property]

end LooseHamilton
