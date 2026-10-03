module

public import HittingTimeLooseHamilton.ExtensionIncidenceTails
public import HittingTimeLooseHamilton.PathPopulationScales

public section

set_option maxHeartbeats 800000
noncomputable section
namespace LooseHamilton
open Finset Filter
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r M : ℕ} {ell : V → ℕ}

@[expose] def pathDegreeLowerFactor (r : ℕ) : ℝ := epsilon/(8*(32*((r:ℝ)+5)))

lemma pathDegreeLowerFactor_pos (r : ℕ) : 0<pathDegreeLowerFactor r := by
  unfold pathDegreeLowerFactor epsilon
  positivity

lemma eventually_terminal_lower_degree (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ ell : ℕ,
      |(ell:ℝ)-(Nat.floor (epsilon*Real.log (n:ℝ)):ℝ)|≤B →
        epsilon/2*Real.log n ≤ ell := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hlog.eventually (eventually_ge_atTop (200*(B+1)))] with n hn
  intro ell hell
  have he := (abs_le.mp hell).1
  have hf := Nat.lt_floor_add_one (epsilon*Real.log (n:ℝ))
  unfold epsilon at hf he ⊢
  change 200*(B+1)≤Real.log (n:ℝ) at hn
  linarith

lemma extension_degree_lower_polynomial (F : TerminalState V r M ell)
    {n j : ℕ} (hcard : Fintype.card V=n) (hr : 3≤r) (hn : r≤n)
    (hl : 0<Real.log (n:ℝ))
    (hhalf : (M:ℝ)≤(n.choose r:ℝ)/2)
    (hj : M≤j) (hjK : j≤(completeEdges V r).card)
    (hμlo : (99/100:ℝ)*Real.log n≤(r:ℝ)*M/n)
    (hμhi : (r:ℝ)*M/n≤2*Real.log n)
    (v : V) (hdlo : epsilon/2*Real.log n≤(vertexDegree F.val v:ℝ))
    (hdhi : (vertexDegree F.val v:ℝ)≤((n-1).choose (r-1):ℝ)/2) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => (vertexDegree (extensionState F σ j) v:ℝ)<
        pathDegreeLowerFactor r*((r:ℝ)*j/n)) ≤ (n:ℝ)^(-((r:ℝ)+5)) := by
  classical
  let μ : ℝ := (r:ℝ)*j/n
  let L : ℝ := 32*((r:ℝ)+5)
  let c : ℝ := pathDegreeLowerFactor r
  have hn0 : 0<n := by omega
  have hnreal : (0:ℝ)<n := by exact_mod_cast hn0
  have hr0 : (0:ℝ)≤r := by positivity
  have hL : 2≤L := by dsimp [L]; linarith
  have hc : 0<c := pathDegreeLowerFactor_pos r
  have hμ : 0≤μ := by dsimp [μ]; positivity
  have hK : (0:ℝ)<n.choose r := by exact_mod_cast Nat.choose_pos hn
  have hMK : M<(completeEdges V r).card := by
    rw [completeEdges_card,hcard]
    exact_mod_cast (show (M:ℝ)<n.choose r by linarith)
  have hMle : M≤n.choose r := by simpa [completeEdges_card,hcard] using hMK.le
  by_cases hearly : (j:ℝ)≤L*M
  · have hμearly : μ≤2*L*Real.log n := by
      have hj' := mul_le_mul_of_nonneg_left hearly hr0
      have hm' := mul_le_mul_of_nonneg_left ((div_le_iff₀ hnreal).mp hμhi) (by linarith : 0≤L)
      apply (div_le_iff₀ hnreal).mpr
      try dsimp [μ]
      nlinarith
    have hearlybound : c*μ≤epsilon/2*Real.log n := by
      have hh := mul_le_mul_of_nonneg_left hμearly hc.le
      have he : c*(2*L*Real.log (n:ℝ)) = epsilon/4*Real.log n := by
        dsimp [c,L,pathDegreeLowerFactor]
        field_simp <;> ring
      rw [he] at hh
      have heps : 0≤epsilon := by unfold epsilon; positivity
      nlinarith [mul_nonneg heps hl.le]
    have hzero : (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
        (fun σ => (vertexDegree (extensionState F σ j) v:ℝ)<c*μ)=0 := by
      apply FiniteEntropy.Law.event_eq_zero_of_false
      intro σ hσ
      have he := extension_filter_card F σ j (fun e => v∈e)
      change vertexDegree (extensionState F σ j) v = vertexDegree F.val v+_ at he
      have hb : (vertexDegree F.val v:ℝ)≤vertexDegree (extensionState F σ j) v := by
        exact_mod_cast (show vertexDegree F.val v≤vertexDegree (extensionState F σ j) v by omega)
      linarith
    change _≤_
    rw [show (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
        (fun σ => (vertexDegree (extensionState F σ j) v:ℝ)<pathDegreeLowerFactor r*((r:ℝ)*j/n))=0 from hzero]
    positivity
  · have hlate : L*M<(j:ℝ) := lt_of_not_ge hearly
    have h2M : 2*(M:ℝ)≤j := by nlinarith only [hL,hlate,show (0:ℝ)≤M by positivity]
    have hμlarge : 16*((r:ℝ)+5)*Real.log n≤μ := by
      have hlm := mul_le_mul_of_nonneg_left ((le_div_iff₀ hnreal).mp hμlo) (by linarith : 0≤L)
      have hlj := mul_le_mul_of_nonneg_left hlate.le hr0
      apply (le_div_iff₀ hnreal).mpr
      dsimp [L] at hlm hlj
      try dsimp [μ]
      nlinarith [mul_nonneg (show (0:ℝ)≤r+5 by positivity) (mul_nonneg hnreal.le hl.le)]
    let k := Nat.floor (c*μ)
    have hk : (k:ℝ)≤c*μ := Nat.floor_le (mul_nonneg hc.le hμ)
    have hklog : (k:ℝ)*Real.log 2≤μ/16 := by
      have hlog2 : Real.log 2≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
      have hcsmall : c≤1/16 := by
        dsimp [c,pathDegreeLowerFactor,epsilon]
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [hr0]
      have h1 := mul_le_mul_of_nonneg_right hcsmall hμ
      nlinarith only [hk,h1,mul_le_mul_of_nonneg_left hlog2 (show (0:ℝ)≤k by positivity)]
    have hD : vertexDegree F.val v≤(n-1).choose (r-1) := by
      exact_mod_cast (show (vertexDegree F.val v:ℝ)≤(n-1).choose (r-1) by linarith only [hdhi,show (0:ℝ)≤vertexDegree F.val v by positivity])
    have hstar : ((n-1).choose (r-1):ℝ)/2≤(((n-1).choose (r-1)-vertexDegree F.val v:ℕ):ℝ) := by
      rw [Nat.cast_sub hD]
      linarith
    have hmean : μ/4≤ (((n-1).choose (r-1)-vertexDegree F.val v:ℕ):ℝ)*
        (j-M:ℕ)/(n.choose r-M:ℕ) := by
      rw [Nat.cast_sub hj,Nat.cast_sub hMle]
      apply path_population_mean_lower hK (Nat.cast_nonneg _) hhalf h2M (Nat.cast_nonneg _) hstar
      have hi := vertex_incidence_ratio (show 1≤r by omega) hn
      try dsimp [μ]
      rw [show ((n-1).choose (r-1):ℝ)*(j:ℝ)/(n.choose r:ℝ)=
          (((n-1).choose (r-1):ℝ)/(n.choose r:ℝ))*(j:ℝ) by ring,hi]
      exact le_of_eq (by ring)
    have hmono : (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
        (fun σ => (vertexDegree (extensionState F σ j) v:ℝ)<c*μ) ≤
        (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
        (fun σ => vertexDegree (extensionState F σ j) v≤k) := by
      apply FiniteEntropy.Law.event_mono
      intro σ hσ
      exact (Nat.le_floor_iff (mul_nonneg hc.le hμ)).mpr hσ.le
    have ht := extension_vertex_lower_tail F (by omega) j k hjK hMK v (1/2) (by norm_num) (by norm_num)
    have he := path_degree_lower_exponent (r+4) hn0 (by convert hμlarge using 1 <;> push_cast <;> ring) hmean hklog
    have hloghalf : Real.log (1/2:ℝ) = -Real.log 2 := by rw [Real.log_div (by norm_num) (by norm_num),Real.log_one]; ring
    have ht' := hmono.trans ht
    simp only [completeEdges_card,hcard,hloghalf] at ht'
    apply ht'.trans
    convert he using 1 <;> push_cast <;> ring
end LooseHamilton
