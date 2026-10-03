module

public import HittingTimeLooseHamilton.BiasedCloneHostMean
public import Mathlib.Data.Nat.Choose.Cast

public section

/-! A uniform quantitative estimate for the actual role-conditioned clone mean. -/
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace LooseHamilton
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem partitionDensity_identity (r m : ℕ) (hr : 3≤r) :
    2*partitionDensity r*(m:ℝ) =
      (privateFraction r)^(r-2)*(r:ℝ)*m/((r:ℝ)-1) := by
  have hr' : (r:ℝ)-1≠0 := by
    have : (3:ℝ)≤r := by exact_mod_cast hr
    linarith
  unfold partitionDensity junctionFraction
  rw [Nat.cast_choose_two]
  field_simp
  <;> ring

theorem privateFraction_pow_bounds (r : ℕ) (hr : 3≤r) :
    0≤(privateFraction r)^(r-2) ∧ (privateFraction r)^(r-2)≤1 := by
  have hr' : (3:ℝ)≤r := by exact_mod_cast hr
  have hb : 0≤privateFraction r := by
    unfold privateFraction
    exact div_nonneg (by linarith) (by linarith)
  have hb' : privateFraction r≤1 := by
    unfold privateFraction
    apply (div_le_one (by linarith)).mpr
    linarith
  exact ⟨pow_nonneg hb _, pow_le_one₀ hb hb'⟩

namespace MixedCycleWitness
variable {r : ℕ} {markers edges : Finset (Finset V)}

/-- Explicit constant in the finite version of the clone average-degree estimate. -/
@[expose] def cloneMeanConstant (r : ℕ) (C : ℝ) : ℝ :=
  4*((r:ℝ)-1)+4*(r:ℝ)^2*((r:ℝ)-1)*(C+1)+2

theorem cloneHost_mean_quantitative (W : MixedCycleWitness r markers edges)
    (G : SimpleHypergraph V) (hr : 3≤r) (hG : ∀e∈G,e.card=r)
    (C δ : ℝ) (hC : 0≤C) (hδ : 0≤δ)
    (hμ : 1≤meanDegree (V:=V) r G.card)
    (hdeg : ∀v, (vertexDegree G v:ℝ)≤C*meanDegree (V:=V) r G.card)
    (hs : 2*markers.card≤Fintype.card V)
    (hN : 0<Fintype.card V)
    (hpart : |(partitionCount G (univ.image W.junction):ℝ)-partitionDensity r*G.card|≤
      δ*(Fintype.card V:ℝ)*meanDegree (V:=V) r G.card) :
    |((cloneHost G W.cloneVertices).card:ℝ)/(edges.card:ℝ)-
      privateFraction r^(r-2)*meanDegree (V:=V) r G.card| ≤
      cloneMeanConstant r C*(δ+(markers.card:ℝ)/(Fintype.card V:ℝ))*
        meanDegree (V:=V) r G.card := by
  let μ := meanDegree (V:=V) r G.card
  let N : ℝ := Fintype.card V
  let s : ℝ := markers.card
  let k : ℝ := edges.card
  let q : ℝ := (r:ℝ)-1
  let b := privateFraction r^(r-2)
  have hNp : 0<N := by dsimp [N]; exact_mod_cast hN
  have hr' : (3:ℝ)≤r := by exact_mod_cast hr
  have hq : 0<q := by dsimp [q]; linarith
  have hs0 : 0≤s := by dsimp [s]; positivity
  have hks : N=q*k+s := by
    have hh := W.vertex_card hr
    dsimp [N,q,k,s]
    have hh' : (Fintype.card V:ℝ) = ((r-1:ℕ):ℝ)*(edges.card:ℝ)+(markers.card:ℝ) := by exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 1≤r), Nat.cast_one] using hh'
  have hs' : 2*s≤N := by dsimp [s,N]; exact_mod_cast hs
  have hk : 0<k := by nlinarith
  have hkN : N≤2*q*k := by linarith
  have hμ0 : 0≤μ := by dsimp [μ]; linarith
  let L : ℕ := ⌈C*μ⌉₊
  have hL : (L:ℝ)≤(C+1)*μ := by
    have hh := Nat.ceil_lt_add_one (mul_nonneg hC hμ0)
    dsimp [L]
    nlinarith
  have hdegL : ∀v, vertexDegree G v≤L := by
    intro v
    exact_mod_cast (hdeg v).trans (Nat.le_ceil (C*μ))
  have hc := W.cloneHost_count_error G L hG hdegL (partitionDensity r*G.card)
    (δ*N*μ) hpart
  have htarget : 2*(partitionDensity r*G.card)=b*μ*N/q := by
    have hi := partitionDensity_identity r G.card hr
    dsimp [b,μ,meanDegree,N,q]
    have hn : (Fintype.card V:ℝ)≠0 := ne_of_gt hNp
    calc
      _ = privateFraction r^(r-2)*(r:ℝ)*G.card/((r:ℝ)-1) := by simpa [mul_assoc] using hi
      _ = _ := by field_simp <;> ring
  have hb0 : 0≤b := (privateFraction_pow_bounds r hr).1
  have hb1 : b≤1 := (privateFraction_pow_bounds r hr).2
  let H : ℝ := (cloneHost G W.cloneVertices).card
  have hc' : |H-b*μ*N/q|≤2*δ*N*μ+2*s*(r:ℝ)^2*(C+1)*μ := by
    rw [htarget] at hc
    have hmul := mul_le_mul_of_nonneg_left hL
      (show 0≤2*s*(r:ℝ)*(r:ℝ) by positivity)
    dsimp [H,s] at *
    nlinarith
  have hd : |H/k-b*μ|≤(2*δ*N*μ+2*s*(r:ℝ)^2*(C+1)*μ)/k+μ*s/(q*k) := by
    have he : H/k-b*μ=(H-b*μ*N/q)/k+b*μ*s/(q*k) := by
      rw [hks]
      field_simp
      <;> ring
    rw [he]
    calc
      _ ≤ |(H-b*μ*N/q)/k|+|b*μ*s/(q*k)| := abs_add_le _ _
      _ ≤ (2*δ*N*μ+2*s*(r:ℝ)^2*(C+1)*μ)/k+μ*s/(q*k) := by
        rw [abs_div,abs_of_pos hk,abs_of_nonneg (by positivity : 0≤b*μ*s/(q*k))]
        apply add_le_add ((div_le_div_iff_of_pos_right hk).mpr hc')
        apply (div_le_div_iff_of_pos_right (mul_pos hq hk)).mpr
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hb1 (mul_nonneg hμ0 hs0)
  change |H/k-b*μ|≤_
  apply hd.trans
  apply (mul_le_mul_iff_left₀ hNp).mp
  change (_+_)*N ≤ (cloneMeanConstant r C*(δ+s/N)*μ)*N
  have hfirst : (2*δ*N*μ+2*s*(r:ℝ)^2*(C+1)*μ)/k*N ≤
      (2*δ*N*μ+2*s*(r:ℝ)^2*(C+1)*μ)*(2*q) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hk).mpr
    have hp : 0≤2*δ*N*μ+2*s*(r:ℝ)^2*(C+1)*μ := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left hkN hp]
  have hsecond : μ*s/(q*k)*N≤2*μ*s := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos hq hk)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hkN (mul_nonneg hμ0 hs0)]
  have hid : (cloneMeanConstant r C*(δ+s/N)*μ)*N =
      cloneMeanConstant r C*(δ*N+s)*μ := by field_simp <;> ring
  rw [hid,add_mul]
  dsimp [cloneMeanConstant,q] at *
  have hextra : 0≤4*(r:ℝ)^2*((r:ℝ)-1)*(C+1)*δ*N*μ := by positivity
  have hextra' : 0≤4*((r:ℝ)-1)*s*μ := by positivity
  have hextra'' : 0≤2*δ*N*μ := by positivity
  nlinarith only [hfirst,hsecond,hextra,hextra',hextra'']
end MixedCycleWitness
end LooseHamilton
