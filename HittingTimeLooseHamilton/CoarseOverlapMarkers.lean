module

public import HittingTimeLooseHamilton.CoarseOverlapMain
public import HittingTimeLooseHamilton.ExceptionalSetAsymptotics
public import Mathlib.Data.Nat.Choose.Bounds

public section

noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open Finset FiniteEntropy Filter
variable {r : ℕ}

/-- Literal mixed-edge overlap, including all prescribed marker pairs. -/
@[expose] def mixedOverlap (D : BiasedRoleInstance r) : ℝ :=
  D.cycleLaw.independentOverlap (fun C => C.val ∪ D.markers)

lemma mixedOverlap_le (D : BiasedRoleInstance r) :
    D.mixedOverlap ≤ D.ordinaryOverlap+D.s := by
  unfold mixedOverlap ordinaryOverlap Law.independentOverlap
  have hc (A B : Finset (Finset (Fin D.N))) :
      (((A∪D.markers)∩(B∪D.markers)).card:ℝ) ≤ ((A∩B).card:ℝ)+D.s := by
    have he : (A∪D.markers)∩(B∪D.markers)=(A∩B)∪D.markers := by ext; simp; tauto
    rw [he]
    exact_mod_cast (card_union_le (A∩B) D.markers)
  calc
    _ ≤ ∑a,∑b,D.cycleLaw.mass a*D.cycleLaw.mass b*(((a.val∩b.val).card:ℝ)+D.s) := by
      apply sum_le_sum; intro a _; apply sum_le_sum; intro b _
      exact mul_le_mul_of_nonneg_left (hc _ _) (mul_nonneg (D.cycleLaw.nonneg a) (D.cycleLaw.nonneg b))
    _ = _ := by
      simp only [mul_add,sum_add_distrib,←sum_mul,←mul_sum,D.cycleLaw.total,one_mul]

lemma μ_le_polynomial (D : BiasedRoleInstance r) : D.μ≤(r:ℝ)*(D.N:ℝ)^r := by
  have hh : D.host.card≤D.N^r := by
    have h := (card_le_card D.host_uniform).trans (by
      simpa [completeEdges_card] using Nat.choose_le_pow D.N r)
    exact h
  calc
    D.μ = (r:ℝ)*D.host.card/D.N := by simp [μ,meanDegree]
    _ ≤ (r:ℝ)*D.host.card := div_le_self (by positivity) (by exact_mod_cast D.N_pos)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hh) (Nat.cast_nonneg _)

lemma log_μ_le (D : BiasedRoleInstance r) (hr : 3≤r) :
    Real.log D.μ≤Real.log (r:ℝ)+(r:ℝ)*Real.log (D.N:ℝ) := by
  have hp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hN : (0:ℝ)<D.N := Nat.cast_pos.mpr D.N_pos
  have h := Real.log_le_log (D.μ_pos hr) D.μ_le_polynomial
  simpa [Real.log_mul hp.ne' (pow_pos hN r).ne',Real.log_pow] using h

/-- The standing polynomial marker budget makes their deterministic overlap
negligible at the coarse overlap scale. -/
theorem eventually_markers_le_overlap_scale (hr : 3≤r) (L : ℝ)
    (D : ℕ→BiasedRoleInstance r)
    (hμ : Tendsto (fun n => (D n).μ) atTop atTop)
    (hs : ∀ᶠn in atTop,((D n).s:ℝ)≤L*((D n).N:ℝ)^(1/10:ℝ)) :
    ∀ᶠn in atTop,((D n).s:ℝ)≤(D n).N/Real.log (D n).μ := by
  have h0 := (tendsto_nat_rpow_mul_log_pow (by norm_num : (-9/10:ℝ)<0) 0).const_mul (L*Real.log (r:ℝ))
  have h1 := (tendsto_nat_rpow_mul_log_pow (by norm_num : (-9/10:ℝ)<0) 1).const_mul (L*(r:ℝ))
  have ht := (h0.add h1).comp (N_tendsto_atTop D hμ)
  simp only [mul_zero,add_zero,pow_zero,mul_one,pow_one,Function.comp_apply] at ht
  filter_upwards [hs,hμ.eventually (eventually_gt_atTop 1),ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hs hm hh
  have hN : (0:ℝ)<(D n).N := Nat.cast_pos.mpr (D n).N_pos
  have hid : ((D n).N:ℝ)^(-9/10:ℝ)=((D n).N:ℝ)^(1/10:ℝ)/(D n).N := by
    rw [show (-9/10:ℝ)=1/10-1 by norm_num,Real.rpow_sub_one hN.ne']
  dsimp only [Function.comp_apply] at hh
  rw [hid] at hh
  have he : (L*Real.log (r:ℝ)*(((D n).N:ℝ)^(1/10:ℝ)/(D n).N)+
      L*(r:ℝ)*((((D n).N:ℝ)^(1/10:ℝ)/(D n).N)*Real.log (D n).N)) =
      (L*((D n).N:ℝ)^(1/10:ℝ)*(Real.log (r:ℝ)+(r:ℝ)*Real.log (D n).N))/(D n).N := by ring
  rw [he] at hh
  have hl := (D n).log_μ_le hr
  have hlog : 0<Real.log (D n).μ := Real.log_pos hm
  have hL : 0≤L*((D n).N:ℝ)^(1/10:ℝ) := (Nat.cast_nonneg _).trans hs
  apply (le_div_iff₀ hlog).mpr
  have hh' := (div_lt_iff₀ hN).mp hh
  have ha := mul_le_mul_of_nonneg_right hs hlog.le
  have hb := mul_le_mul_of_nonneg_left hl hL
  linarith
end LooseHamilton.BiasedRoleInstance
