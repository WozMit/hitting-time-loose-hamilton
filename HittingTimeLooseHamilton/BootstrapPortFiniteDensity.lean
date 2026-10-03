module

public import HittingTimeLooseHamilton.BootstrapPortFailedLabels
public import HittingTimeLooseHamilton.BootstrapPortSourceGeometry
public import HittingTimeLooseHamilton.BootstrapPortRegisteredDensity

public section

/-! Finite density for the actual original-port test, derived from sequential mobility. -/
noncomputable section
namespace LooseHamilton.BootstrapPortFiniteDensity
open Finset BootstrapBases BootstrapConstants SequentialCompletion
variable {N r : ℕ} {M : Finset (Finset (Fin N))}

theorem density_le (hr : 3 ≤ r) (hN : 2*r ≤ N) (ha : 0 ≤ FrameScales.alpha N)
    (hM : IsPairMatching M) (H J : SimpleHypergraph (Fin N))
    (hH : H ⊆ completeEdges (Fin N) r) (X c : ℝ) (hc : 0<c)
    (hb : ∀ b : Base M, BootstrapSequentialMobility.Bounds (r:=r) hM b H X c)
    (h time : ℕ) (P : Finset (Fin N)) (y z u : Fin N)
    (hs : LegalPrivateCompletion r (M.erase {y,z}) P {u,z})
    (hy : y ∉ P ∪ {u,z}) (hm : {y,z} ∈ M) (hyz : y ≠ z)
    (hlarge : X/(N:ℝ)^(2*r) ≤
      (rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u:ℝ)) :
    rootLinkDensity r y ((registerPortRootTest r h time M (originalPorts M) P y z u
      (portThreshold r c)).badSet (J,H)) ≤
      ((2:ℝ)^(r-1)*((r-1).factorial:ℝ))*
        (((r-1:ℕ):ℝ)*exceptionBound r N
          (fixedPorts (some (⟨y,BootstrapPortSourceGeometry.chosen_port_mem hm⟩ : ↥(originalPorts M)))).card/(N:ℝ)) +
      (((originalPorts M).erase y).card:ℝ)*(r-1:ℕ)/(N-1:ℕ) := by
  classical
  let a : ↥(originalPorts M) := ⟨y,BootstrapPortSourceGeometry.chosen_port_mem hm⟩
  have hz : z = OriginalPortPartner.partner hM a := BootstrapPortSourceGeometry.partner_eq hM hyz hm
  have hmarkers : markers hM (some a) = M.erase {y,z} :=
    BootstrapPortSourceGeometry.residual_markers_eq hM hyz hm
  have hsrc : LegalPrivateCompletion r (markers hM (some a)) P {u,OriginalPortPartner.partner hM a} := by
    rw [hmarkers,←hz]; exact hs
  have hP : a.val ∉ P := fun hp => hy (mem_union_left _ hp)
  have hu := BootstrapPortSourceGeometry.root_not_mem_originalPorts hs hy
  have hfail := BootstrapPortFailedLabels.failed_labels hM a H hH X c (hb (some a))
    P u hsrc hP hu (by simpa only [←hz] using hlarge)
  simp only [←hz] at hfail
  let B := exceptionBound r N (fixedPorts (some a)).card
  let W : ℝ := rootFreePortSource r M (fixedPortHost H (originalPorts M)) y z P u
  let T := privateFactor r c^(r-2)*endpointFactor r c*W
  let β := ((r-1:ℕ):ℝ)*B/(N:ℝ)
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hβ : 0≤β := div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (exceptionBound_nonneg r N _ ha)) hNp.le
  have hT : portThreshold r c*W ≤ T :=
    mul_le_mul_of_nonneg_right (portThreshold_lt hr hc).le (Nat.cast_nonneg _)
  have hpow : (N:ℝ)^(r-1) = (N:ℝ)^(r-2)*(N:ℝ) := by
    rw [←pow_succ]; congr 1; omega
  have hnormalize : ((r-1:ℕ):ℝ)*B*(N:ℝ)^(r-2) = β*(N:ℝ)^(r-1) := by
    rw [hpow]
    dsimp [β]
    field_simp
    <;> ring
  have hf : ((BootstrapPortLinkDensity.failed r M (fixedPortHost H (originalPorts M)) y z T).card:ℝ) ≤
      β*(Fintype.card (Fin N):ℝ)^(r-1) := by
    simp only [Fintype.card_fin]
    rw [←hnormalize]
    exact hfail
  rw [BootstrapPortRegisteredDensity.badSet_eq r h time M J H P y z u (portThreshold r c) hs hy hm hyz]
  simpa only [Fintype.card_fin] using BootstrapPortLinkDensity.density_le hr
    (by simpa using hN) M (fixedPortHost H (originalPorts M)) P y z u hm hM.2
    (portThreshold r c) T β hβ hT hf

end LooseHamilton.BootstrapPortFiniteDensity
