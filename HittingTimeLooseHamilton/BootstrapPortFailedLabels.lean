module

public import HittingTimeLooseHamilton.BootstrapPortLabelTransport
public import HittingTimeLooseHamilton.BootstrapPortLinkDensity
public import HittingTimeLooseHamilton.BootstrapSequentialSourceLabels

public section

noncomputable section
namespace LooseHamilton.BootstrapPortFailedLabels
open Finset BootstrapBases BootstrapConstants SequentialCompletion BootstrapPortLabelTransport
variable {N r : ℕ} {M : Finset (Finset (Fin N))}

theorem label_weight (hM : IsPairMatching M) (a : ↥(originalPorts M))
    (H : SimpleHypergraph (Fin N)) (hH : H ⊆ completeEdges (Fin N) r)
    (l : Finset (Fin N) × Fin N × Fin N)
    (hl : l ∈ BootstrapPortLinkDensity.labels r a.val (OriginalPortPartner.partner hM a)) :
    rootFreePortCompletion r M (fixedPortHost H (originalPorts M)) a.val
      (OriginalPortPartner.partner hM a) l.1 {l.2.1,l.2.2} =
    completionCount r (restrictEdges (active (some a)) (markers hM (some a)))
      (fixedPortHost (inducedHost (active (some a)) H) (fixedPorts (some a)))
      (label hM a l).1 {(label hM a l).2.1,(label hM a l).2.2} := by
  have hh := (mem_filter.mp hl).2
  have hy := vertex_val hM a l.2.1 hh.2.2.1
  have hp : (partner hM a).val = l.2.2 := hh.2.2.2.symm
  have he : ({l.2.1,l.2.2} : Finset (Fin N)) = {(vertex hM a l.2.1).val,(partner hM a).val} := by rw [hy,hp]
  rw [he,weight_eq hM a H hH _ _ (by
    intro v hv
    rcases mem_insert.mp hv with hv|hv
    · exact hv ▸ (vertex hM a l.2.1).property
    · exact (mem_singleton.mp hv) ▸ (partner hM a).property),pair_restrict]
  rfl

theorem label_injOn (hM : IsPairMatching M) (a : ↥(originalPorts M)) :
    Set.InjOn (label hM a) (BootstrapPortLinkDensity.labels r a.val (OriginalPortPartner.partner hM a)) := by
  intro l hl k hk he
  have hl' := (mem_filter.mp hl).2
  have hk' := (mem_filter.mp hk).2
  have hp := congrArg (fun t => liftEdge (active (some a)) t.1) he
  change liftEdge _ (restrictEdge _ l.1) = liftEdge _ (restrictEdge _ k.1) at hp
  rw [lift_restrictEdge _ _ (by
    intro v hv
    simp only [active,deleted,mem_sdiff,mem_univ,mem_singleton,true_and]
    exact fun hv' => hl'.2.1 (hv' ▸ hv)),lift_restrictEdge _ _ (by
    intro v hv
    simp only [active,deleted,mem_sdiff,mem_univ,mem_singleton,true_and]
    exact fun hv' => hk'.2.1 (hv' ▸ hv))] at hp
  have hu := congrArg (fun t => t.2.1.val) he
  change (vertex hM a l.2.1).val = (vertex hM a k.2.1).val at hu
  rw [vertex_val _ _ _ hl'.2.2.1,vertex_val _ _ _ hk'.2.2.1] at hu
  exact Prod.ext hp (Prod.ext hu (hl'.2.2.2.trans hk'.2.2.2.symm))

theorem failed_labels (hM : IsPairMatching M) (a : ↥(originalPorts M))
    (H : SimpleHypergraph (Fin N)) (hH : H ⊆ completeEdges (Fin N) r) (X c : ℝ)
    (hb : BootstrapSequentialMobility.Bounds (r:=r) hM (some a) H X c)
    (P : Finset (Fin N)) (u : Fin N)
    (hs : LegalPrivateCompletion r (markers hM (some a)) P {u,OriginalPortPartner.partner hM a})
    (hP : a.val ∉ P) (hu : u ∉ originalPorts M)
    (hlarge : X/(N:ℝ)^(2*r) ≤ (rootFreePortSource r M (fixedPortHost H (originalPorts M))
      a.val (OriginalPortPartner.partner hM a) P u:ℝ)) :
    ((BootstrapPortLinkDensity.failed r M (fixedPortHost H (originalPorts M)) a.val
      (OriginalPortPartner.partner hM a)
      (privateFactor r c^(r-2)*endpointFactor r c*
        (rootFreePortSource r M (fixedPortHost H (originalPorts M)) a.val
          (OriginalPortPartner.partner hM a) P u:ℝ))).card:ℝ) ≤
      ((r-1:ℕ):ℝ)*exceptionBound r N (fixedPorts (some a)).card*(N:ℝ)^(r-2) := by
  classical
  have hua : u ≠ a.val := fun h => hu (h ▸ a.property)
  let src : Finset (Fin N) × Fin N × Fin N := (P,u,OriginalPortPartner.partner hM a)
  have hsrc : src ∈ BootstrapPortLinkDensity.labels r a.val (OriginalPortPartner.partner hM a) :=
    mem_filter.mpr ⟨mem_univ _,hs.private_card,hP,hua,rfl⟩
  have hw := label_weight hM a H hH src hsrc
  have hy : (vertex hM a u).val = u := vertex_val hM a u hua
  have hz : (partner hM a).val = OriginalPortPartner.partner hM a := rfl
  have hleg := legal hM a P (vertex hM a u) (partner hM a)
    (by intro v hv; simp only [active,deleted,mem_sdiff,mem_univ,mem_singleton,true_and]; exact fun h => hP (h ▸ hv))
    (by simpa only [hy,hz] using hs)
  let labs := BootstrapPortLinkDensity.labels r a.val (OriginalPortPartner.partner hM a)
  have hbound := BootstrapSequentialSourceLabels.original_port hM a H X c hb
    (restrictEdge (active (some a)) P) (vertex hM a u) (partner hM a) hleg hz
    (by rw [mem_fixedPorts,hy]; exact hu)
    (by simpa only [rootFreePortSource,hw,label,src] using hlarge)
    (labs.image (label hM a)) (by
      intro l hl
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hl
      have hk' := (mem_filter.mp hk).2
      exact ⟨(block_card hM a k hk'.2.1).trans hk'.1,rfl⟩)
  have hc : (BootstrapPortLinkDensity.failed r M (fixedPortHost H (originalPorts M)) a.val
      (OriginalPortPartner.partner hM a) (privateFactor r c^(r-2)*endpointFactor r c*
        (rootFreePortSource r M (fixedPortHost H (originalPorts M)) a.val
          (OriginalPortPartner.partner hM a) P u:ℝ))).card ≤
    ((labs.image (label hM a)).filter (fun l =>
      (completionCount r (restrictEdges (active (some a)) (markers hM (some a)))
        (fixedPortHost (inducedHost (active (some a)) H) (fixedPorts (some a))) l.1 {l.2.1,l.2.2}:ℝ) <
      privateFactor r c^(r-2)*endpointFactor r c*
        (rootFreePortSource r M (fixedPortHost H (originalPorts M)) a.val
          (OriginalPortPartner.partner hM a) P u:ℝ))).card := by
    apply card_le_card_of_injOn (label hM a)
    · intro l hl
      have hll := (mem_filter.mp hl).1
      exact mem_filter.mpr ⟨mem_image_of_mem _ hll,by
        rw [←label_weight hM a H hH l hll]
        exact (mem_filter.mp hl).2⟩
    · intro l hl k hk he
      exact label_injOn hM a (mem_filter.mp hl).1 (mem_filter.mp hk).1 he
  apply (Nat.cast_le.mpr hc).trans
  simpa only [rootFreePortSource,hw,label,src] using hbound

end LooseHamilton.BootstrapPortFailedLabels
