module

public import HittingTimeLooseHamilton.RestrictedNoDeficitEstimate
public import HittingTimeLooseHamilton.NoDeficitBoundarySlack
public import HittingTimeLooseHamilton.EdgeComplementModels

public section

/-! Original-terminal regularity controls arbitrary restricted-host sampling.
No adjusted offset assumption is introduced after complement exposure. -/
noncomputable section
namespace LooseHamilton
open Finset Filter
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- This terminal estimate is uniform over every sampling host on the original
vertex set, hence over all fixed complement records and allowed universes. -/
theorem eventually_restricted_terminal_no_deficit {C K : ℝ}
    (hC : 0<C) (hK : 0<K) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type*) [Fintype V] [DecidableEq V],
      Fintype.card V=n → ∀ (r M : ℕ) (ell : V→ℕ) (markers : Finset (Finset V)),
      CoreAdmissible r M ell markers B → ∀ F : TerminalState V r M ell,
      TerminalRegular C F.val → ∀ J0 : SimpleHypergraph V,
      ∀ (k : ℕ) (ν : ℝ), (n:ℝ) ≤ K*k → 1≤ν → ν≤Real.log n →
        NoDeficitEstimate (C*K) (epsilon/8) F.val J0 ell k ν := by
  filter_upwards [eventually_restricted_no_deficit_estimate (C:=C) (K:=K) (L:=1)
    hC hK (by norm_num), eventually_no_deficit_slack B 0] with n he hl
  intro V _ _ hV r M ell markers hadm F hF J0 k ν hk hν hνlog
  have he' := he V hV F.val J0 ell (terminalLowVertices F.val)
  simp only [one_mul] at he'
  apply he' F.property.2.2
  · simpa only [hV,one_mul] using hF.low_set
  · intro v
    simpa only [hV] using hF.maximum_degree v
  · intro v hv
    have hv' : 3*epsilon*Real.log (n:ℝ) < vertexDegree F.val v := by
      simpa only [mem_terminalLowVertices,hV,not_le] using hv
    have hb := hl (ell v) (by simpa only [lowerDegreeBase,hV] using hadm.offsets v)
    simp only [mul_zero,add_zero] at hb
    exact_mod_cast hb.trans hv'.le
  · exact hk
  · exact hν
  · exact hνlog

/-- The exposed terminal complement is never sampled. -/
lemma restricted_terminal_remainder (F U T : SimpleHypergraph V) (hT : T⊆U) :
    F \ T = (F \ U) ∪ ((F ∩ U) \ T) := by
  ext e
  constructor
  · intro h
    obtain ⟨he, ht⟩ := mem_sdiff.mp h
    by_cases hu : e ∈ U
    · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨mem_inter.mpr ⟨he,hu⟩,ht⟩))
    · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨he,hu⟩))
  · intro h
    rcases mem_union.mp h with h | h
    · obtain ⟨he,hu⟩ := mem_sdiff.mp h
      exact mem_sdiff.mpr ⟨he,fun ht => hu (hT ht)⟩
    · obtain ⟨he,ht⟩ := mem_sdiff.mp h
      exact mem_sdiff.mpr ⟨(mem_inter.mp he).1,ht⟩

/-- Exact complement-exposure success event, still using every original lower
bound, rather than newly bounded residual offsets. -/
lemma restricted_batch_retains_lower_iff (F U J0 A0 S : SimpleHypergraph V)
    (hJ : J0⊆U) (hA : F\U=A0) (hS : F∩U=S)
    (ell : V→ℕ) (τ : ℕ) (σ : BatchOrder J0.card) :
    BatchRetainsLower F ell (batchSelection J0 J0.card rfl τ σ) ↔
      ∀ v, ell v ≤ vertexDegree
        (A0 ∪ (S \ batchSelection J0 J0.card rfl τ σ)) v := by
  unfold BatchRetainsLower
  rw [restricted_terminal_remainder F U _ ((batchSelection_subset _ _ _ _ _).trans hJ),hA,hS]

/-- Any pointwise estimate immediately gives the required exposed-terminal
feasibility probability. The original vertex count remains in the error. -/
theorem restricted_no_deficit_complement_feasibility
    (F U J0 A0 S : SimpleHypergraph V) (hJ : J0⊆U)
    (hA : F\U=A0) (hS : F∩U=S) (ell : V→ℕ) (k : ℕ) (ν A c : ℝ)
    (he : NoDeficitEstimate A c F J0 ell k ν) :
    1-noDeficitError A c (Fintype.card V) ν ≤
      (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder J0.card)).event
        (fun σ => ∀ v, ell v ≤ vertexDegree
          (A0 ∪ (S \ batchSelection J0 J0.card rfl
            (noDeficitBatchSize J0.card k ν) σ)) v) := by
  have hh := he.2
  simpa only [restricted_batch_retains_lower_iff F U J0 A0 S hJ hA hS] using hh
end LooseHamilton
