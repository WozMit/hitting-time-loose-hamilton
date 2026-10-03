module

public import HittingTimeLooseHamilton.PartitionFallingFactorial

public section

/-! Deterministic complete-host partition ratios with quantitative errors. -/
noncomputable section
namespace LooseHamilton

@[expose] def completePartitionRatio (r n k : ℕ) : ℝ :=
  (k.choose 2:ℝ)*((n-k).choose (r-2):ℝ)/(n.choose r:ℝ)

lemma completePartitionRatio_falling {r n k : ℕ} (hr : 2≤r) (hn : 0<n) :
    completePartitionRatio r n k = (r.choose 2:ℝ)*
      normalizedFalling k n 2*normalizedFalling (n-k) n (r-2)/normalizedFalling n n r := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hfac : (r.factorial:ℝ)=(r.choose 2:ℝ)*(2:ℝ)*((r-2).factorial:ℝ) := by
    exact_mod_cast (by simpa using (Nat.choose_mul_factorial_mul_factorial hr).symm)
  have hp : (n:ℝ)^r=(n:ℝ)^2*(n:ℝ)^(r-2) := by rw [←pow_add]; congr 1; omega
  unfold completePartitionRatio normalizedFalling
  simp only [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  rw [hfac,hp]
  norm_num
  by_cases hc : n.choose r=0
  · simp [hc]
  · have hc0 : (n.choose r:ℝ)≠0 := by exact_mod_cast hc
    have hchoose : (r.choose 2:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hr)
    have hfactor : ((r-2).factorial:ℝ)≠0 := by positivity
    field_simp [hc0,hn0,hchoose,hfactor]
    <;> ring

lemma product_quotient_error {x y u v z E : ℝ}
    (hx0 : 0≤x) (hx1 : x≤1) (hy0 : 0≤y) (hy1 : y≤1)
    (hu0 : 0≤u) (hu1 : u≤1) (hv0 : 0≤v) (hv1 : v≤1)
    (hz : 1/2≤z) (hex : |x-u|≤E) (hey : |y-v|≤E) (hez : |z-1|≤E) :
    |x*y/z-u*v|≤6*E := by
  have hz0 : 0<z := by linarith
  have hp : |x*y-u*v|≤2*E := by
    calc
      _ = |(x-u)*y+u*(y-v)| := by congr 1; ring
      _ ≤ |(x-u)*y|+|u*(y-v)| := abs_add_le _ _
      _ ≤ |x-u|+|y-v| := by
        rw [abs_mul,abs_of_nonneg hy0,abs_mul,abs_of_nonneg hu0]
        nlinarith [abs_nonneg (x-u),abs_nonneg (y-v)]
      _ ≤ _ := by linarith
  have huv0 : 0≤u*v := mul_nonneg hu0 hv0
  have huv1 : u*v≤1 := by nlinarith
  have herr : |x*y-z*(u*v)|≤3*E := by
    calc
      _ = |(x*y-u*v)+(1-z)*(u*v)| := by congr 1; ring
      _ ≤ |x*y-u*v|+|(1-z)*(u*v)| := abs_add_le _ _
      _ ≤ 2*E+E := by
        apply add_le_add hp
        rw [abs_mul,abs_of_nonneg huv0,abs_sub_comm]
        exact (mul_le_mul_of_nonneg_left huv1 (abs_nonneg _)).trans (by simpa using hez)
      _ = _ := by ring
  rw [div_sub' (ne_of_gt hz0),abs_div,abs_of_pos hz0]
  apply (div_le_iff₀ hz0).mpr
  have hE : 0≤E := (abs_nonneg _).trans hex
  nlinarith

lemma completePartitionRatio_error {r n k : ℕ} {a ε : ℝ} (hr : 2≤r) (hn : 0<n)
    (hkn : k≤n) (ha0 : 0≤a) (ha1 : a≤1) (hε : |(k:ℝ)/n-a|≤ε)
    (hden : 1/2≤normalizedFalling n n r) :
    |completePartitionRatio r n k-(r.choose 2:ℝ)*a^2*(1-a)^(r-2)| ≤
      6*(r.choose 2:ℝ)*(r:ℝ)*(ε+(r:ℝ)/n) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hε0 : 0≤ε := (abs_nonneg _).trans hε
  have hcomp : |((n-k:ℕ):ℝ)/n-(1-a)|≤ε := by
    rw [Nat.cast_sub hkn,sub_div,div_self (ne_of_gt hn0)]
    simpa only [show (1-(k:ℝ)/n)-(1-a)= -((k:ℝ)/n-a) by ring,abs_neg] using hε
  have bound (j d : ℕ) (b : ℝ) (hj : j≤n) (hd : d≤r) (hb0 : 0≤b) (hb1 : b≤1)
      (he : |(j:ℝ)/n-b|≤ε) :
      |normalizedFalling j n d-b^d|≤(r:ℝ)*(ε+(r:ℝ)/n) := by
    apply (normalizedFalling_error hn hj hb0 hb1 d).trans
    gcongr
  have hx := normalizedFalling_mem hkn 2
  have hy := normalizedFalling_mem (Nat.sub_le n k) (r-2)
  have hu : 0≤a^2 ∧ a^2≤1 := ⟨by positivity, by nlinarith⟩
  have hv : 0≤(1-a)^(r-2) ∧ (1-a)^(r-2)≤1 :=
    ⟨pow_nonneg (by linarith) _, pow_le_one₀ (by linarith) (by linarith)⟩
  have h := product_quotient_error hx.1 hx.2 hy.1 hy.2 hu.1 hu.2 hv.1 hv.2 hden
    (bound k 2 a hkn hr ha0 ha1 hε)
    (bound (n-k) (r-2) (1-a) (Nat.sub_le _ _) (Nat.sub_le _ _) (by linarith) (by linarith) hcomp)
    (by simpa using bound n r 1 le_rfl le_rfl (by norm_num) le_rfl (by simp [ne_of_gt hn0,hε0]))
  rw [completePartitionRatio_falling hr hn]
  have heq : (r.choose 2:ℝ)*normalizedFalling k n 2*normalizedFalling (n-k) n (r-2)/normalizedFalling n n r-
      (r.choose 2:ℝ)*a^2*(1-a)^(r-2) = (r.choose 2:ℝ)*
      (normalizedFalling k n 2*normalizedFalling (n-k) n (r-2)/normalizedFalling n n r-a^2*(1-a)^(r-2)) := by ring
  rw [heq,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (r.choose 2) : (0:ℝ)≤r.choose 2)]
end LooseHamilton
