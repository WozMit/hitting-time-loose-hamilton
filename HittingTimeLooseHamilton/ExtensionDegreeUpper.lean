module

public import HittingTimeLooseHamilton.ExtensionIncidenceTails
public import HittingTimeLooseHamilton.PathTailScales
public import HittingTimeLooseHamilton.PathPopulationScales

public section

/-! Pointwise polynomial upper tails for extension degrees. -/
noncomputable section
namespace LooseHamilton
open Finset Filter
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {r M : ℕ} {ell : V → ℕ}

@[expose] def pathDegreeUpperFactor (r : ℕ) (C₀ : ℝ) : ℝ := 2*C₀+16*((r:ℝ)+6)

lemma extension_degree_upper_polynomial (F : TerminalState V r M ell)
    {n j : ℕ} (hcard : Fintype.card V=n) (hr : 3≤r) (hn : r≤n)
    {C₀ : ℝ} (hC : 0≤C₀) (hl : 0≤Real.log (n:ℝ))
    (hhalf : (M:ℝ)≤(n.choose r:ℝ)/2) (hj : M≤j) (hjK : j≤(completeEdges V r).card)
    (hμ : (99/100:ℝ)*Real.log n≤(r:ℝ)*j/n)
    (v : V) (hd : (vertexDegree F.val v:ℝ)≤C₀*Real.log n) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => pathDegreeUpperFactor r C₀*((r:ℝ)*j/n) <
        (vertexDegree (extensionState F σ j) v:ℝ)) ≤ (n:ℝ)^(-((r:ℝ)+5)) := by
  classical
  let μ : ℝ := (r:ℝ)*j/n
  let A : ℝ := 16*((r:ℝ)+6)
  let k := Nat.floor (A*μ)+1
  have hn0 : 0<n := by omega
  have hK : (0:ℝ)<n.choose r := by exact_mod_cast Nat.choose_pos hn
  have hMK : M<(completeEdges V r).card := by
    rw [completeEdges_card,hcard]
    exact_mod_cast (show (M:ℝ)<n.choose r by linarith)
  have hMle : M≤n.choose r := by simpa [completeEdges_card,hcard] using hMK.le
  have hbase : (vertexDegree F.val v:ℝ)≤2*C₀*μ :=
    terminal_degree_absorption hC hμ hl hd
  have hmono : (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => pathDegreeUpperFactor r C₀*μ < (vertexDegree (extensionState F σ j) v:ℝ)) ≤
      (FiniteEntropy.uniform : FiniteEntropy.Law (MissingOrder V r M)).event
      (fun σ => vertexDegree F.val v+k≤vertexDegree (extensionState F σ j) v) := by
    apply FiniteEntropy.Law.event_mono
    intro σ hσ
    have hk : (Nat.floor (A*μ):ℝ)≤A*μ := Nat.floor_le (by dsimp [A,μ]; positivity)
    have hh : (vertexDegree F.val v+Nat.floor (A*μ):ℕ) < vertexDegree (extensionState F σ j) v := by
      have hh : (vertexDegree F.val v:ℝ)+(Nat.floor (A*μ):ℝ) < (vertexDegree (extensionState F σ j) v:ℝ) := by
        dsimp [pathDegreeUpperFactor] at hσ
        dsimp [A] at hk
        nlinarith
      exact_mod_cast hh
    dsimp [k]
    omega
  have ht := extension_vertex_upper_tail F (by omega) j k hjK hMK v 2 (by norm_num)
  have hmean : (((n-1).choose (r-1)-vertexDegree F.val v:ℕ):ℝ)*(j-M:ℕ)/(n.choose r-M:ℕ) ≤ 2*μ := by
    have hh := path_vertex_mean_upper (show 1≤r by omega) hn hhalf hj
    have hsub : (((n-1).choose (r-1)-vertexDegree F.val v:ℕ):ℝ) ≤ (n-1).choose (r-1) :=
      Nat.cast_le.mpr (Nat.sub_le _ _)
    calc
      _ ≤ ((n-1).choose (r-1):ℝ)*(j-M:ℕ)/(n.choose r-M:ℕ) := by gcongr
      _ ≤ _ := by simpa only [Nat.cast_sub hj,Nat.cast_sub hMle] using hh
  have hexp : Real.exp (2*(((n-1).choose (r-1)-vertexDegree F.val v:ℕ):ℝ)*(j-M:ℕ)/
      (n.choose r-M:ℕ))/(2:ℝ)^k ≤ Real.exp (4*μ-(k:ℝ)*Real.log 2) := by
    rw [show (2:ℝ)^k=Real.exp ((k:ℝ)*Real.log 2) by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]]
    rw [←Real.exp_sub]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hmean (by norm_num : (0:ℝ)≤2)
    linarith only [show 2*(((n-1).choose (r-1)-vertexDegree F.val v:ℕ):ℝ)*(j-M:ℕ)/(n.choose r-M:ℕ)≤4*μ by convert hh using 1 <;> ring]
  have hA : 2*(2:ℝ)+100*((r+4:ℕ)+1)/99 ≤ A*Real.log 2 := by
    have hh := Real.log_two_gt_d9
    have hr0 : (0:ℝ)≤r := by positivity
    dsimp [A]
    push_cast
    nlinarith
  have hk : A*μ≤(k:ℝ) := by
    dsimp [k]
    simpa only [Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one (A*μ)).le
  have he := path_degree_exponent 2 (r+4) hn0 hl hμ hA hk
  have ht' := hmono.trans ht
  simp only [hcard,completeEdges_card] at ht'
  exact ht'.trans (hexp.trans (by convert he using 1 <;> (try dsimp [μ]) <;> congr 1 <;> push_cast <;> ring))
end LooseHamilton
