module

public import HittingTimeLooseHamilton.BootstrapSequentialMobility
public import HittingTimeLooseHamilton.SequentialCompletionOrdinaryPorts

public section

/-! The two manuscript branches, stated directly for actual set-valued sources. -/
noncomputable section
namespace LooseHamilton.BootstrapSequentialSourceLabels
open Finset BootstrapBases BootstrapConstants SequentialCompletion
variable {N r : ℕ} {M : Finset (Finset (Fin N))}

theorem ordinary (hM : IsPairMatching M) (H : SimpleHypergraph (Fin N)) (X c : ℝ)
    (bounds : BootstrapSequentialMobility.Bounds (r:=r) hM none H X c)
    (P : Finset ↥(active (none : Base M))) (y z : ↥(active (none : Base M)))
    (hs : LegalPrivateCompletion r (restrictEdges (active none) (markers hM none)) P {y,z})
    (hlarge : X/(N:ℝ)^(2*r) ≤ (completionCount r (restrictEdges (active none) (markers hM none))
      (fixedPortHost (inducedHost (active none) H) (fixedPorts none)) P {y,z}:ℝ))
    (labels : Finset (Finset ↥(active (none : Base M)) × ↥(active (none : Base M)) × ↥(active (none : Base M))))
    (hlabels : ∀ l ∈ labels, l.1.card = r-2) :
    ((labels.filter (fun l => (completionCount r (restrictEdges (active none) (markers hM none))
      (fixedPortHost (inducedHost (active none) H) (fixedPorts none)) l.1 {l.2.1,l.2.2}:ℝ) <
      privateFactor r c ^ (r-2) * endpointFactor r c ^ 2 *
        (completionCount r (restrictEdges (active none) (markers hM none))
          (fixedPortHost (inducedHost (active none) H) (fixedPorts none)) P {y,z}:ℝ))).card:ℝ) ≤
      (r:ℝ)*exceptionBound r N (fixedPorts (none : Base M)).card*(N:ℝ)^(r-1) := by
  classical
  obtain ⟨s,hP,hy,hz,hs'⟩ := exists_state_of_legal _ P y z hs.private_card hs
  have hw : s.weight r (restrictEdges (active none) (markers hM none))
      (fixedPortHost (inducedHost (active none) H) (fixedPorts none)) =
      completionCount r (restrictEdges (active none) (markers hM none))
        (fixedPortHost (inducedHost (active none) H) (fixedPorts none)) P {y,z} := by
    simp only [State.weight,hP,hy,hz]
  simpa only [hw] using bounds.ordinary s hs' (ordinary_source_ports hM s hs')
    (by simpa only [hw] using hlarge) (ordinary_fixedPorts hM) labels hlabels

theorem original_port (hM : IsPairMatching M) (a : ↥(originalPorts M))
    (H : SimpleHypergraph (Fin N)) (X c : ℝ)
    (bounds : BootstrapSequentialMobility.Bounds (r:=r) hM (some a) H X c)
    (P : Finset ↥(active (some a))) (y z : ↥(active (some a)))
    (hs : LegalPrivateCompletion r (restrictEdges (active (some a)) (markers hM (some a))) P {y,z})
    (hzPartner : z.val = OriginalPortPartner.partner hM a)
    (hyOrdinary : y ∉ fixedPorts (some a))
    (hlarge : X/(N:ℝ)^(2*r) ≤ (completionCount r (restrictEdges (active (some a)) (markers hM (some a)))
      (fixedPortHost (inducedHost (active (some a)) H) (fixedPorts (some a))) P {y,z}:ℝ))
    (labels : Finset (Finset ↥(active (some a)) × ↥(active (some a)) × ↥(active (some a))))
    (hlabels : ∀ l ∈ labels, l.1.card = r-2 ∧ l.2.2 = z) :
    ((labels.filter (fun l => (completionCount r (restrictEdges (active (some a)) (markers hM (some a)))
      (fixedPortHost (inducedHost (active (some a)) H) (fixedPorts (some a))) l.1 {l.2.1,l.2.2}:ℝ) <
      privateFactor r c ^ (r-2) * endpointFactor r c *
        (completionCount r (restrictEdges (active (some a)) (markers hM (some a)))
          (fixedPortHost (inducedHost (active (some a)) H) (fixedPorts (some a))) P {y,z}:ℝ))).card:ℝ) ≤
      ((r-1:ℕ):ℝ)*exceptionBound r N (fixedPorts (some a)).card*(N:ℝ)^(r-2) := by
  classical
  obtain ⟨s,hP,hy,hz,hs'⟩ := exists_state_of_legal _ P y z hs.private_card hs
  have hw : s.weight r (restrictEdges (active (some a)) (markers hM (some a)))
      (fixedPortHost (inducedHost (active (some a)) H) (fixedPorts (some a))) =
      completionCount r (restrictEdges (active (some a)) (markers hM (some a)))
        (fixedPortHost (inducedHost (active (some a)) H) (fixedPorts (some a))) P {y,z} := by
    simp only [State.weight,hP,hy,hz]
  have hp : EndpointSourcePorts (fixedPorts (some a))
      (restrictEdges (active (some a)) (markers hM (some a))) s.first s.second := by
    rw [hy,hz]
    exact BootstrapEndpointBasePorts.original_port hM a y z hzPartner hyOrdinary
  simpa only [hw] using bounds.port s hs' hp
    (by simpa only [hw] using hlarge) labels (by simpa only [hz] using hlabels)

end LooseHamilton.BootstrapSequentialSourceLabels
