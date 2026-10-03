module

public import HittingTimeLooseHamilton.NoDeficitModels
public import HittingTimeLooseHamilton.RestrictedNoDeficitSampling
public import HittingTimeLooseHamilton.NoDeficitScales

public section

/-! Uniform no-deficit probability from a protected low-degree set and slack elsewhere. -/
noncomputable section
namespace LooseHamilton
open Filter Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restricted-host fixed-source estimate with explicit constants, with no containment hypothesis. It allows empty hosts,
and requires neither a new low-degree-set hypothesis nor a density window. -/
theorem eventually_restricted_no_deficit_estimate {C K L : ℝ}
    (hC : 0 < C) (hK : 0 < K) (hL : 0 < L) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type*) [Fintype V] [DecidableEq V],
      Fintype.card V=n → ∀ (F H : SimpleHypergraph V), 
      ∀ (ell : V → ℕ) (B : Finset V),
      (∀ v, ell v ≤ vertexDegree F v) →
      (B.card:ℝ) ≤ L*(n:ℝ)^(1/4:ℝ) →
      (∀ v, (vertexDegree F v:ℝ) ≤ C*Real.log n) →
      (∀ v ∉ B, ell v+Nat.floor (epsilon*Real.log n) ≤ vertexDegree F v) →
      ∀ (k : ℕ) (ν : ℝ), (n:ℝ) ≤ K*k → 1 ≤ ν → ν ≤ Real.log n →
      NoDeficitEstimate (L*C*K) (epsilon/8) F H ell k ν := by
  classical
  filter_upwards [eventually_noDeficit_binomial_tail_two_constants (K:=K) hC.le,
    eventually_noDeficit_batch_valid hK] with n htail hvalid
  intro V _ _ hV F H ell B hell hB hd hslack k ν hk hν hνlog
  have hν0 : 0 ≤ ν := by linarith
  have hlog : 0 ≤ Real.log (n:ℝ) := hν0.trans hνlog
  obtain ⟨hk0,hτ⟩ := hvalid.2 H.card k ν hk hν0 hνlog
  let τ := noDeficitBatchSize H.card k ν
  have hτ' : τ ≤ H.card := hτ
  refine ⟨hτ',?_⟩
  by_cases hm : H.card=0
  · have hzero : τ=0 := Nat.eq_zero_of_le_zero (hm ▸ hτ')
    have he : (fun σ : BatchOrder H.card =>
        BatchRetainsLower F ell (batchSelection H H.card rfl τ σ)) = (fun _ => True) := by
      funext σ
      have hs : batchSelection H H.card rfl τ σ=∅ :=
        card_eq_zero.mp ((batchSelection_card H H.card rfl τ hτ' σ).trans hzero)
      simp only [hs,BatchRetainsLower,sdiff_empty]
      exact propext ⟨fun _ => trivial,fun _ => hell⟩
    change 1-noDeficitError (L*C*K) (epsilon/8) (Fintype.card V) ν ≤
      (FiniteEntropy.uniform : FiniteEntropy.Law (BatchOrder H.card)).event _
    rw [he,FiniteEntropy.Law.event_true,hV]
    have hn : 0 ≤ noDeficitError (L*C*K) (epsilon/8) n ν := by
      unfold noDeficitError
      positivity
    linarith
  · have hm0 : 0 < H.card := Nat.pos_of_ne_zero hm
    let d := Nat.floor (C*Real.log (n:ℝ))
    let a := Nat.floor (epsilon*Real.log (n:ℝ))
    let q : ℝ := (τ:ℝ)/H.card
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hcap0 : 0 ≤ C*Real.log (n:ℝ) := mul_nonneg hC.le hlog
    have hcap : (d:ℝ) ≤ C*Real.log (n:ℝ) := Nat.floor_le hcap0
    have hd' (v : V) : vertexDegree F v ≤ d := (Nat.le_floor_iff hcap0).mpr (hd v)
    have hq : q ≤ K*ν/n := noDeficit_batch_ratio hvalid.1 hm0 hk0 hν0 hk
    have ht := htail.2 d q ν hcap hq0 hq hν0 hνlog
    have hp := noDeficit_protected_bound hvalid.1
      (Real.rpow_nonneg (Nat.cast_nonneg n) (1/4:ℝ)) (Nat.cast_nonneg d) hq0
      (le_refl ((n:ℝ)^(1/4:ℝ))) hcap hq
    have hb : (B.card:ℝ)*(d:ℝ)*q ≤
        (L*C*K)*ν*(n:ℝ)^(-3/4:ℝ)*Real.log n := by
      have hh := mul_le_mul_of_nonneg_right hB (mul_nonneg (Nat.cast_nonneg d) hq0)
      have hh' := mul_le_mul_of_nonneg_left hp hL.le
      nlinarith only [hh,hh']
    have hs := restricted_no_deficit_sampling_success_bound H F H.card rfl τ hτ' hm0
      ell B a d hell hslack hd'
    change 1-noDeficitError (L*C*K) (epsilon/8) (Fintype.card V) ν ≤ _
    apply le_trans _ hs
    rw [hV]
    unfold noDeficitError
    change 1-((L*C*K)*ν*(n:ℝ)^(-(3/4:ℝ))*Real.log n+
      Real.exp (-(epsilon/8)*(Real.log n)^2)) ≤
      1-((B.card:ℝ)*(d:ℝ)*q+(n:ℝ)*(d.choose a:ℝ)*q^a)
    have ht' : (n:ℝ)*(d.choose a:ℝ)*q^a ≤ Real.exp (-(epsilon/8)*(Real.log n)^2) := ht
    have hb' : (B.card:ℝ)*(d:ℝ)*q ≤
        (L*C*K)*ν*(n:ℝ)^(-(3/4:ℝ))*Real.log n := by simpa only [neg_div] using hb
    linarith
end LooseHamilton
