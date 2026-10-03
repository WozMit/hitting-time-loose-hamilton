module

public import HittingTimeLooseHamilton.HittingTimeSelection

public section

/-! A finite stopped observation with exactly the original exposure fibres. -/
noncomputable section
namespace LooseHamilton.HittingTimeSelection
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev TimeIndex (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :=
  Fin ((completeEdges V r).card+1)
abbrev ExposureData (V : Type*) [Fintype V] [DecidableEq V] :=
  Finset V × Finset V × SimpleHypergraph V
abbrev Observation (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :=
  Option (TimeIndex V r × ExposureData V)

@[expose] def stoppedIndex {r : ℕ} (σ : EdgeOrder V r) : Option (TimeIndex V r) := by
  classical
  exact if h : ∃ t : TimeIndex V r, tauOne σ = (t.val : WithTop ℕ) then some h.choose else none

theorem stoppedIndex_eq_some {r : ℕ} (σ : EdgeOrder V r) (t : TimeIndex V r) :
    stoppedIndex σ = some t ↔ tauOne σ = (t.val : WithTop ℕ) := by
  classical
  unfold stoppedIndex
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · intro he; simpa only [he] using h.choose_spec
    · intro ht
      apply Fin.ext
      exact WithTop.coe_injective (h.choose_spec.symm.trans ht)
  · simp only [reduceCtorEq,false_iff]
    exact fun ht => h ⟨t,ht⟩

@[expose] def stateData {r : ℕ} (σ : EdgeOrder V r) (m : ℕ) : ExposureData V :=
  let F := processState σ m
  let B := lowDegreeVertices F
  let D := chooseD r B (traceOn B F)
  (B,D,traceOn D F)

@[expose] def observe {r : ℕ} (σ : EdgeOrder V r) : Observation V r :=
  (stoppedIndex σ).map (fun t => (t,stateData σ t.val))

theorem observe_eq_some {r : ℕ} (σ : EdgeOrder V r) (t : TimeIndex V r)
    (a : ExposureData V) :
    observe σ = some (t,a) ↔ tauOne σ = (t.val : WithTop ℕ) ∧ stateData σ t.val = a := by
  classical
  unfold observe
  cases hs : stoppedIndex σ with
  | none =>
    constructor
    · intro h; cases h
    · rintro ⟨ht,_⟩
      have hh := (stoppedIndex_eq_some σ t).mpr ht
      rw [hs] at hh
      cases hh
  | some q =>
    constructor
    · intro h
      have hh : (q,stateData σ q.val) = (t,a) := Option.some.inj h
      obtain ⟨hqt,hdata⟩ := Prod.mk.inj hh
      subst q
      exact ⟨(stoppedIndex_eq_some σ t).mp hs,hdata⟩
    · rintro ⟨ht,hdata⟩
      have hqt : q=t := Option.some.inj (hs.symm.trans ((stoppedIndex_eq_some σ t).mpr ht))
      subst q
      exact congrArg (fun x => some (t,x)) hdata

/-- Compatibility conditions depend only on the finite exposed observation. -/
@[expose] def Compatible (r : ℕ) (a : ExposureData V) : Prop :=
  a.1 ⊆ a.2.1 ∧ chooseD r a.1 (traceOn a.1 a.2.2) = a.2.1

theorem stateData_compatible {r : ℕ} (σ : EdgeOrder V r) (m : ℕ) :
    Compatible r (stateData σ m) := by
  dsimp [Compatible,stateData]
  have h := subset_chooseD r (lowDegreeVertices (processState σ m))
    (traceOn (lowDegreeVertices (processState σ m)) (processState σ m))
  exact ⟨h,by rw [traceOn_trace h]⟩

/-- No separation or global goodness event is inserted into an exposure fibre. -/
theorem fibre_eq_exposure {r : ℕ} (t : TimeIndex V r) (a : ExposureData V)
    (ha : Compatible r a) (σ : EdgeOrder V r) :
    observe σ = some (t,a) ↔ coreExposureEvent r t.val a.1 a.2.1 a.2.2 σ := by
  rw [observe_eq_some]
  constructor
  · rintro ⟨ht,hdata⟩
    have hB := congrArg Prod.fst hdata
    have hD := congrArg (fun a : ExposureData V => a.2.1) hdata
    have hT := congrArg (fun a : ExposureData V => a.2.2) hdata
    dsimp [stateData] at hB hD hT
    exact ⟨ht,hB,by simpa only [hD] using hT⟩
  · intro h
    refine ⟨h.1,?_⟩
    have hD := choice_on_exposure ha.1 ha.2 σ h
    dsimp [stateData]
    rw [h.2.1,hD,h.2.2]

/-- Every actually observed finite value satisfies compatibility. -/
theorem compatible_of_observed {r : ℕ} (σ : EdgeOrder V r) (t : TimeIndex V r)
    (a : ExposureData V) (h : observe σ = some (t,a)) : Compatible r a := by
  rw [← (observe_eq_some σ t a).mp h |>.2]
  exact stateData_compatible σ t.val

/-- A finite stopped time always gives a finite observation. -/
theorem observe_at_time {r m : ℕ} (σ : EdgeOrder V r)
    (ht : tauOne σ = (m : WithTop ℕ)) :
    ∃ t : TimeIndex V r, t.val = m ∧ observe σ = some (t,stateData σ m) := by
  have hb := (firstTime_spec (completeEdges V r).card (processState σ) NoIsolated (t := m) ht).1
  let t : TimeIndex V r := ⟨m,by omega⟩
  exact ⟨t,rfl,(observe_eq_some σ t _).mpr ⟨ht,rfl⟩⟩

/-- Recover the smaller exceptional trace from any full exposure. -/
theorem initial_trace_of_observed {r : ℕ} (σ : EdgeOrder V r)
    (t : TimeIndex V r) (a : ExposureData V) (h : observe σ = some (t,a)) :
    traceOn a.1 (processState σ t.val) = traceOn a.1 a.2.2 := by
  have ha := compatible_of_observed σ t a h
  have he := (fibre_eq_exposure t a ha σ).mp h
  rw [← traceOn_trace ha.1 (processState σ t.val),he.2.2]

/-- All choices of deleted blocks and ports remain fixed on an observed fibre. -/
theorem initial_trace_eq_of_same_observation {r : ℕ} (σ τ : EdgeOrder V r)
    (t : TimeIndex V r) (a : ExposureData V)
    (hσ : observe σ = some (t,a)) (hτ : observe τ = some (t,a)) :
    traceOn a.1 (processState σ t.val) = traceOn a.1 (processState τ t.val) := by
  rw [initial_trace_of_observed σ t a hσ,initial_trace_of_observed τ t a hτ]

end LooseHamilton.HittingTimeSelection
