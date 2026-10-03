module

public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics

public section

/-! Scalar consequences of the multiplicative forward/reverse comparison.
The forward loss is multiplied by the bad-source probability before division;
no additive exceptional probability is introduced. -/
noncomputable section
namespace LooseHamilton
open Filter

/-- A forward success fraction bounded below by one half costs at most a factor two. -/
lemma forward_reverse_scalar_bound {ε p γ : ℝ}
    (hε : ε≤1/2) (hp : 0≤p) (hforward : (1-ε)*p≤γ) :
    0<1-ε ∧ p≤γ/(1-ε) ∧ p≤2*γ := by
  have hden : 0<1-ε := by linarith
  refine ⟨hden,(le_div_iff₀ hden).mpr ?_,?_⟩
  · nlinarith only [hforward]
  · have hh := mul_le_mul_of_nonneg_right hε hp
    nlinarith only [hforward,hh]

/-- Vanishing forward failure gives a positive denominator and a uniform factor-two bound. -/
theorem eventually_forward_reverse_bounds {ε p γ : ℕ→ℝ}
    (hε : Tendsto ε atTop (nhds 0))
    (hp : ∀ᶠ n in atTop,0≤p n)
    (hforward : ∀ᶠ n in atTop,(1-ε n)*p n≤γ n) :
    ∀ᶠ n in atTop,0<1-ε n ∧ p n≤γ n/(1-ε n) ∧ p n≤2*γ n := by
  filter_upwards [(tendsto_order.mp hε).2 (1/2) (by norm_num),hp,hforward]
    with n hn hp hf
  exact forward_reverse_scalar_bound hn.le hp hf

/-- Multiplicative forward errors remain harmless after any nonnegative weighting
for which the correspondingly weighted reverse bound vanishes. -/
theorem forward_reverse_weighted_tendsto_zero {ε p γ w : ℕ→ℝ}
    (hε : Tendsto ε atTop (nhds 0))
    (hp : ∀ᶠ n in atTop,0≤p n) (hw : ∀ᶠ n in atTop,0≤w n)
    (hforward : ∀ᶠ n in atTop,(1-ε n)*p n≤γ n)
    (hγ : Tendsto (fun n=>w n*γ n) atTop (nhds 0)) :
    Tendsto (fun n=>w n*p n) atTop (nhds 0) := by
  have hbound := eventually_forward_reverse_bounds hε hp hforward
  have hzero : Tendsto (fun n=>2*(w n*γ n)) atTop (nhds 0) := by
    simpa only [mul_zero] using hγ.const_mul 2
  apply squeeze_zero' ?_ ?_ hzero
  · filter_upwards [hp,hw] with n hp hw
    exact mul_nonneg hw hp
  · filter_upwards [hbound,hw] with n hn hw
    have hh := mul_le_mul_of_nonneg_left hn.2.2 hw
    nlinarith only [hh]

/-- In particular, the bad-source probability vanishes when the reverse bound does. -/
theorem forward_reverse_tendsto_zero {ε p γ : ℕ→ℝ}
    (hε : Tendsto ε atTop (nhds 0))
    (hp : ∀ᶠ n in atTop,0≤p n)
    (hforward : ∀ᶠ n in atTop,(1-ε n)*p n≤γ n)
    (hγ : Tendsto γ atTop (nhds 0)) : Tendsto p atTop (nhds 0) := by
  have hh := forward_reverse_weighted_tendsto_zero (w:=fun _=>1) hε hp
    (Eventually.of_forall fun _=>zero_le_one) hforward (by simpa using hγ)
  simpa using hh

/-- The comparison survives a polynomial-sized union whenever the reverse estimate does. -/
theorem forward_reverse_polynomial_tendsto_zero (d : ℕ) {ε p γ : ℕ→ℝ}
    (hε : Tendsto ε atTop (nhds 0))
    (hp : ∀ᶠ n in atTop,0≤p n)
    (hforward : ∀ᶠ n in atTop,(1-ε n)*p n≤γ n)
    (hγ : Tendsto (fun n : ℕ => (n:ℝ)^d*γ n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (n:ℝ)^d*p n) atTop (nhds 0) :=
  forward_reverse_weighted_tendsto_zero hε hp (Eventually.of_forall fun n=>by positivity)
    hforward hγ
end LooseHamilton
