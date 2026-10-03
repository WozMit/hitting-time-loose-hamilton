module

public import HittingTimeLooseHamilton.HittingTimeExposureAverage
public import HittingTimeLooseHamilton.HittingTimeExposureUniform
public import HittingTimeLooseHamilton.HittingTimeSelectionObservation
public import HittingTimeLooseHamilton.HittingTimeGoodEvent
public import HittingTimeLooseHamilton.HittingTimeExpansion
public import HittingTimeLooseHamilton.HittingTimeCoreExistence

public section

/-! Finite averaging of the uniform core theorem over the actual stopped
observation. The global good event only certifies fibres and is never inserted
into their conditional law. -/
noncomputable section
namespace LooseHamilton.HittingTimeConclusion
open Finset HittingTimeSelection

/-- A single uniform core error bounds the conditional error on all favourable
exposure fibres, and hence costs no factor for their number. -/
theorem finite_probability_bound (r n N₀ : ℕ) (hr : 3 ≤ r) (hn : 0 < n)
    (hdiv : r-1 ∣ n) (hbase : 1 ≤ lowerDegreeBase (Fin n))
    (hsize : r*N₀ ≤ n) (ε : ℝ) (hε : 0 ≤ ε)
    (hcore : ∀ (V : Type) [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
      ∀ (m : ℕ) (ell : V → ℕ) (markers : Finset (Finset V))
        (hadm : CoreAdmissible r m ell markers ((2*(r-2) : ℕ)+2)),
      letI : Nonempty (TerminalState V r m ell) := hadm.feasible
      (terminalLaw r m ell).event (fun F =>
        ¬ 0 < cycleCount r markers F.val (originalPorts markers)) ≤ ε) :
    (processLaw (Fin n) r).event (fun σ => ¬ hittingTimeEvent σ) ≤
      (processLaw (Fin n) r).event (fun σ => ¬ Good σ) + ε := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let p := processLaw (Fin n) r
  let favourable : Observation (Fin n) r → Prop := fun a =>
    ∃ σ, observe σ = a ∧ Good σ
  have hcond : ∀ a, favourable a → ∀ ha : 0 < p.event (fun σ => observe σ = a),
      (p.condition (fun σ => observe σ = a) ha).event (fun σ => ¬ hittingTimeEvent σ) ≤ ε := by
    intro a ha hpos
    obtain ⟨σ₀,hobs₀,hgood⟩ := ha
    obtain ⟨t,ht,hex,hparams⟩ := hgood.2
    let F₀ := processState σ₀ t
    let B := lowDegreeVertices F₀
    have hv : Valid r B (traceOn B F₀) :=
      ⟨restrictTrace (Classical.choice hex)⟩
    let C := selected hv
    let D := C.deleted
    let T := traceOn D F₀
    have hBD : B ⊆ D := C.anchors_deleted
    have hstate := firstTime_spec (completeEdges (Fin n) r).card (processState σ₀) NoIsolated (t:=t) ht
    let ti : TimeIndex (Fin n) r := ⟨t,by omega⟩
    let data : ExposureData (Fin n) := (B,D,T)
    have hdata : stateData σ₀ t = data := by
      change (B,chooseD r B (traceOn B F₀),traceOn (chooseD r B (traceOn B F₀)) F₀) = (B,D,T)
      rw [← selected_deleted hv]
    have hob : observe σ₀ = some (ti,data) :=
      (observe_eq_some σ₀ ti data).mpr ⟨ht,hdata⟩
    have hcomp : Compatible r data := compatible_of_observed σ₀ ti data hob
    have hevent : (fun σ : EdgeOrder (Fin n) r => observe σ=a) =
        coreExposureEvent r t B D T := by
      funext σ
      rw [← hobs₀,hob]
      exact propext (fibre_eq_exposure ti data hcomp σ)
    have hE : 0 < p.event (coreExposureEvent r t B D T) := by
      rw [← hevent]
      exact hpos
    have hadm := hparams C hdiv
    letI : Nonempty (TerminalState ↥(univ \ D) r (t-T.card)
      (fun w => coreLowerBound D T w.val)) := hadm.feasible
    have hlarge : N₀ ≤ Fintype.card ↥C.coreVertices := by
      simpa only [Fintype.card_coe] using
        C.core_card_ge_of_ambient_large hr N₀ (by simpa only [Fintype.card_fin] using hsize)
    have hc := hcore ↥C.coreVertices hlarge (t-T.card)
      (fun w => coreLowerBound D T w.val) (restrictEdges C.coreVertices C.markers) hadm
    let BadCore : SimpleHypergraph ↥(univ \ D) → Prop := fun H =>
      ¬ 0 < cycleCount r (restrictEdges C.coreVertices C.markers) H
        (originalPorts (restrictEdges C.coreVertices C.markers))
    have huniform := HittingTimeExposure.conditional_host_event hbase hBD hE BadCore
    have hdom : (p.condition (coreExposureEvent r t B D T) hE).event
        (fun σ => ¬ hittingTimeEvent σ) ≤
        (p.condition (coreExposureEvent r t B D T) hE).event
          (fun σ => BadCore (inducedHost (univ \ D) (processState σ t))) := by
      rw [condition_event_eq_joint,condition_event_eq_joint]
      apply div_le_div_of_nonneg_right _ hE.le
      apply p.event_mono
      intro σ ⟨he,hbad⟩
      refine ⟨he,?_⟩
      intro hcount
      have htrace : traceOn B (processState σ t) = traceOn B F₀ := by
        rw [← traceOn_trace hBD (processState σ t),he.2.2]
        exact traceOn_trace hBD F₀
      have hsub : traceOn B F₀ ⊆ processState σ t := by
        rw [← htrace]
        exact filter_subset _ _
      let Cσ := enlarge (blocks hv) hsub
      apply hbad
      exact hittingTimeEvent_of_core_count hr σ he.1 Cσ
        (originalPorts (restrictEdges C.coreVertices C.markers)) hcount
    have hh := hdom.trans (huniform.le.trans hc)
    simpa only [hevent] using hh
  have hav := HittingTimeExposure.average_failure p observe favourable
    (fun σ => ¬ hittingTimeEvent σ) ε hε hcond
  apply hav.trans
  apply add_le_add_left
  exact p.event_mono (fun σ hbad hgood => hbad ⟨σ,rfl,hgood⟩)

end LooseHamilton.HittingTimeConclusion
