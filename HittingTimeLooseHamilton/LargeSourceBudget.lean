module

public import HittingTimeLooseHamilton.AuxiliaryFrameEntropy
public import HittingTimeLooseHamilton.LogarithmicBenchmark
public import HittingTimeLooseHamilton.PathPerturbationScalars

public section

set_option maxHeartbeats 1000000
noncomputable section
namespace LooseHamilton
open Filter Topology
open AuxiliaryFrame

/-- Only an upper bound for the frame mean is needed: filtering the original
ports can only reduce this benchmark. No lower mean comparison is assumed. -/
theorem frame_benchmark_upper {N r k : ℕ} (hr : 3≤r)
    (hN : r≤N) (hlog : 1≤Real.log (N:ℝ))
    (original : Finset (Finset (Fin N)))
    (hsize : N=(r-1)*k+original.card)
    (F : Frame r original) (H : SimpleHypergraph (Fin N))
    (hX : 0<F.cycleCount H) (hHN : N≤H.card) (hHK : H.card≤N^r) :
    FrameEntropy.benchmark r F.k (F.mu H) ≤
      logarithmicBenchmark r N k H.card +
        ((2*((r:ℝ)+2)+4*r+((r:ℝ)-1)*(4*r+2))*Real.log N) := by
  have hfamily : (F.cycleFamily H).Nonempty := Finset.card_pos.mp hX
  have hv := F.vertex_identity hr hfamily
  have hn := F.n_add_deleted
  simp only [Fintype.card_fin] at hn
  have hd := F.val.deleted_card_le
  have hs : F.s≤original.card+2 := by
    have ha := F.marker_budget.introduced_le
    have hb := Finset.card_le_card_sdiff_add_card (s:=F.markers) (t:=original)
    change F.markers.card≤_ ; omega
  have hs' : original.card≤F.s+2 := by
    have ha := F.marker_budget.removed_le
    have hb := Finset.card_le_card_sdiff_add_card (s:=original) (t:=F.markers)
    change original.card≤F.markers.card+2 ; omega
  have hkupper : F.k≤k+2 := by
    have hR : 1≤r-1 := by omega
    nlinarith
  have hklower : k≤F.k+4*r+2 := by
    have hR : 1≤r-1 := by omega
    nlinarith
  have hnp : 0<F.n := (F.k_pos hr hfamily).trans_le F.k_le_n
  have hnr : 0<(F.n:ℝ) := Nat.cast_pos.mpr hnp
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hrR : (3:ℝ)≤r := Nat.cast_le.mpr hr
  have hm : 0<F.mu H := by
    obtain ⟨E,hE⟩ := hfamily
    have hc := Finset.card_le_card ((F.mem_cycleFamily H E).mp hE).1
    rw [F.edge_card hr hE] at hc
    have hmpos : 0<F.m H := (F.k_pos hr ⟨E,hE⟩).trans_le hc
    unfold Frame.mu
    exact div_pos (mul_pos (by positivity) (Nat.cast_pos.mpr hmpos)) hnr
  have hmle : F.mu H ≤ (r:ℝ)*H.card/F.n := by
    have hsub : F.rawHost H⊆H := by
      intro e he
      exact (Finset.mem_inter.mp (Finset.mem_filter.mp he).1).1
    unfold Frame.mu Frame.m
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hsub)) (by positivity)) hnr.le
  let a : ℝ := ((r:ℝ)-1)*((r:ℝ)*H.card/N)
  have hr1 : 0<(r:ℝ)-1 := by linarith
  have hHpos : 0<(H.card:ℝ) := hNr.trans_le (Nat.cast_le.mpr hHN)
  have ha : 0<a := by dsimp [a]; positivity
  have han : 1≤a := by
    have hH : (N:ℝ)≤H.card := Nat.cast_le.mpr hHN
    have hf : (1:ℝ)≤((r:ℝ)-1)*r := by nlinarith
    have hh : (N:ℝ)≤((r:ℝ)-1)*r*H.card := hH.trans (le_mul_of_one_le_left hHpos.le hf)
    dsimp [a]
    rw [←mul_div_assoc]
    exact (le_div_iff₀ hNr).mpr (by nlinarith)
  have hloga : 0≤Real.log a := Real.log_nonneg han
  have hloga_upper : Real.log a ≤ ((r:ℝ)+2)*Real.log N := by
    have hHr : (H.card:ℝ)≤(N:ℝ)^r := by exact_mod_cast hHK
    have hrN : (r:ℝ)≤N := Nat.cast_le.mpr hN
    have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
    have haupper : a≤(N:ℝ)^(r+2) := by
      have hprod : ((r:ℝ)-1)*r≤(N:ℝ)^2 := by nlinarith
      dsimp [a]
      rw [←mul_div_assoc]
      apply (div_le_self (by positivity) hN1).trans
      rw [←mul_assoc]
      calc
        ((r:ℝ)-1)*r*H.card ≤ (N:ℝ)^2*(N:ℝ)^r :=
          mul_le_mul hprod hHr (by positivity) (by positivity)
        _ = (N:ℝ)^(r+2) := by rw [←pow_add]; congr 1; omega
    have hh := Real.log_le_log ha haupper
    rw [Real.log_pow] at hh
    push_cast at hh
    exact hh
  have hlf : Real.log (((r:ℝ)-1)*F.mu H) ≤
      Real.log a + (F.val.deleted.card:ℝ)/F.n := by
    have hlogupper := Real.log_le_log (mul_pos (by linarith) hm)
      (mul_le_mul_of_nonneg_left hmle (by linarith : 0≤(r:ℝ)-1))
    have heq : ((r:ℝ)-1)*((r:ℝ)*H.card/F.n) = a*((N:ℝ)/F.n) := by
      dsimp [a]; field_simp
    rw [heq,Real.log_mul ha.ne' (div_pos hNr hnr).ne'] at hlogupper
    have hratio := Real.log_le_sub_one_of_pos (div_pos hNr hnr)
    have hnR : (F.n:ℝ)+F.val.deleted.card=N := by exact_mod_cast hn
    have heq' : (N:ℝ)/F.n-1=(F.val.deleted.card:ℝ)/F.n := by
      apply (eq_div_iff hnr.ne').mpr
      field_simp
      linarith
    rw [heq'] at hratio
    linarith
  have hkR : (F.k:ℝ)≤(k:ℝ)+2 := by exact_mod_cast hkupper
  have hkR' : (k:ℝ)≤(F.k:ℝ)+4*r+2 := by exact_mod_cast hklower
  have hdn : (F.val.deleted.card:ℝ)≤4*r := by exact_mod_cast hd
  have hklog := mul_le_mul_of_nonneg_left hlf (Nat.cast_nonneg F.k : (0:ℝ)≤F.k)
  have hlogdiff := mul_le_mul_of_nonneg_right hkR hloga
  have hkdiv : (F.k:ℝ)*((F.val.deleted.card:ℝ)/F.n)≤F.val.deleted.card := by
    have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr F.k_le_n)
      (div_nonneg (Nat.cast_nonneg F.val.deleted.card) hnr.le)
    convert hh using 1
    field_simp
  have hrkd := mul_le_mul_of_nonneg_left hkR' (show 0≤(r:ℝ)-1 by linarith)
  have hconst : 4*(r:ℝ)+((r:ℝ)-1)*(4*r+2) ≤
      (4*(r:ℝ)+((r:ℝ)-1)*(4*r+2))*Real.log N := by
    exact le_mul_of_one_le_right (by positivity) hlog
  change (F.k:ℝ)*Real.log (((r:ℝ)-1)*F.mu H)-((r:ℝ)-1)*F.k ≤
    (k:ℝ)*Real.log a-((r:ℝ)-1)*k+_
  nlinarith only [hklog,hlogdiff,hkdiv,hrkd,hconst,hloga_upper,hdn]

end LooseHamilton
