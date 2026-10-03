module

public import HittingTimeLooseHamilton.AssociationBadChoicesTools

public section

noncomputable section
namespace LooseHamilton
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

@[expose] def associationGoodTargets (F : SimpleHypergraph V) (B e : Finset V) (z : V) :
    Finset (Finset V × V) :=
  (graphIncidences F).filter (fun p => p.2 ∉ B ∧ Disjoint e p.1 ∧
    switchedEdge e z p.2 ∉ F ∧ switchedEdge p.1 p.2 z ∉ F)

@[simp] lemma mem_associationGoodTargets (F : SimpleHypergraph V) (B e : Finset V) (z : V)
    (p : Finset V × V) : p ∈ associationGoodTargets F B e z ↔
      p.1 ∈ F ∧ p.2∈p.1 ∧ p.2∉B ∧ Disjoint e p.1 ∧
        switchedEdge e z p.2∉F ∧ switchedEdge p.1 p.2 z∉F := by
  simp only [associationGoodTargets,mem_filter,mem_graphIncidences]
  tauto

lemma association_meeting_targets_le {F : SimpleHypergraph V} {r Δ : ℕ}
    (hF : F ⊆ completeEdges V r) (hdeg : ∀ v, vertexDegree F v ≤ Δ)
    (e : Finset V) (he : e.card=r) :
    ((graphIncidences F).filter (fun p => ¬Disjoint e p.1)).card ≤ r^2*Δ := by
  let T := F.filter (fun f => ¬Disjoint e f)
  have hT : T.card ≤ r*Δ := by
    calc
      T.card ≤ (e.biUnion (fun v => F.filter (fun f => v ∈ f))).card := by
        apply card_le_card
        intro f hf
        obtain ⟨hf,hd⟩ := mem_filter.mp hf
        obtain ⟨v,hve,hvf⟩ := not_disjoint_iff.mp hd
        exact mem_biUnion.mpr ⟨v,hve,mem_filter.mpr ⟨hf,hvf⟩⟩
      _ ≤ ∑ v ∈ e, (F.filter (fun f => v∈f)).card := card_biUnion_le
      _ ≤ ∑ _v ∈ e, Δ := sum_le_sum (fun v _ => hdeg v)
      _ = r*Δ := by simp [he]
  have h := card_le_uniform_fibres ((graphIncidences F).filter (fun p => ¬Disjoint e p.1))
    T Prod.fst r (by
      intro p hp
      obtain ⟨hp,hd⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨((mem_graphIncidences F p).mp hp).1,hd⟩) (by
      intro f hf
      have hfF := (mem_filter.mp hf).1
      calc
        _ ≤ ((graphIncidences F).filter (fun p => p.1=f)).card := by
          apply card_le_card
          intro p hp
          exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
        _ = f.card := graphIncidences_edge_fibre F hfF
        _ = r := (mem_completeEdges r f).mp (hF hfF))
  calc
    _ ≤ T.card*r := h
    _ ≤ (r*Δ)*r := Nat.mul_le_mul_right r hT
    _ = _ := by ring

lemma association_first_collision_le {F : SimpleHypergraph V} {Δ : ℕ}
    (hdeg : ∀ v, vertexDegree F v ≤ Δ) {e : Finset V} {z w : V}
    (hw : w∈e.erase z) :
    ((graphIncidences F).filter (fun p => p.2∉e ∧ switchedEdge e z p.2∈F)).card ≤ Δ^2 := by
  let A := univ.filter (fun a => a∉e ∧ switchedEdge e z a∈F)
  have hA : A.card ≤ Δ := by
    calc
      A.card ≤ (F.filter (fun g => w∈g)).card := by
        apply card_le_card_of_injOn (fun a => switchedEdge e z a)
        · intro a ha
          obtain ⟨_,ha,hg⟩ := mem_filter.mp ha
          exact mem_filter.mpr ⟨hg,mem_switchedEdge _ _ _ _ |>.mpr (Or.inr (mem_erase.mp hw))⟩
        · intro a ha b hb he
          exact switchedEdge_insert_injective (mem_filter.mp ha).2.1 (mem_filter.mp hb).2.1 he
      _ ≤ Δ := hdeg w
  have h := card_le_uniform_fibres
    ((graphIncidences F).filter (fun p => p.2∉e ∧ switchedEdge e z p.2∈F)) A Prod.snd Δ
    (by intro p hp; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hp).2⟩) (by
      intro a ha
      calc
        _ ≤ ((graphIncidences F).filter (fun p => p.2=a)).card := by
          apply card_le_card
          intro p hp
          exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
        _ = vertexDegree F a := graphIncidences_vertex_fibre F a
        _ ≤ Δ := hdeg a)
  calc
    _ ≤ A.card*Δ := h
    _ ≤ Δ*Δ := Nat.mul_le_mul_right Δ hA
    _ = _ := by ring

lemma association_second_collision_le {F : SimpleHypergraph V} {r Δ : ℕ}
    (hr : 2≤r) (hF : F ⊆ completeEdges V r) (hdeg : ∀ v, vertexDegree F v ≤ Δ) (z : V) :
    ((graphIncidences F).filter (fun p => z∉p.1 ∧ switchedEdge p.1 p.2 z∈F)).card ≤ Δ^2 := by
  let S := (graphIncidences F).filter (fun p => z∉p.1 ∧ switchedEdge p.1 p.2 z∈F)
  let T := F.filter (fun g => z∈g)
  have hfibre (g : Finset V) (hg : g∈T) :
      (S.filter (fun p => switchedEdge p.1 p.2 z=g)).card ≤ Δ := by
    obtain ⟨hgF,hzg⟩ := mem_filter.mp hg
    have hgc : g.card=r := (mem_completeEdges r g).mp (hF hgF)
    have hpos : 0<(g.erase z).card := by rw [card_erase_of_mem hzg,hgc]; omega
    obtain ⟨w,hw⟩ := card_pos.mp hpos
    calc
      _ ≤ (F.filter (fun f => w∈f)).card := by
        apply card_le_card_of_injOn Prod.fst
        · intro p hp
          obtain ⟨hp,hpg⟩ := mem_filter.mp hp
          obtain ⟨hp,hzp,hnew⟩ := mem_filter.mp hp
          obtain ⟨hpF,hap⟩ := (mem_graphIncidences F p).mp hp
          refine mem_filter.mpr ⟨hpF,?_⟩
          have hwg : w∈switchedEdge p.1 p.2 z := hpg.symm ▸ mem_of_mem_erase hw
          rcases (mem_switchedEdge _ _ _ _).mp hwg with heq | hmem
          · exact False.elim ((mem_erase.mp hw).1 heq)
          · exact hmem.2
        · intro p hp q hq hf
          obtain ⟨hp,hpg⟩ := mem_filter.mp hp
          obtain ⟨hq,hqg⟩ := mem_filter.mp hq
          have hpz := (mem_filter.mp hp).2.1
          have hpa := ((mem_graphIncidences F p).mp (mem_filter.mp hp).1).2
          have hqa := ((mem_graphIncidences F q).mp (mem_filter.mp hq).1).2
          apply Prod.ext hf
          apply switchedEdge_remove_injective hpz hpa (by simpa only [hf] using hqa)
          simpa only [hf] using hpg.trans hqg.symm
      _ ≤ Δ := hdeg w
  have h := card_le_uniform_fibres S T (fun p => switchedEdge p.1 p.2 z) Δ (by
    intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).2.2,by simp⟩) hfibre
  calc
    _ ≤ T.card*Δ := h
    _ ≤ Δ*Δ := Nat.mul_le_mul_right Δ (hdeg z)
    _ = _ := by ring

/-- Every failed target is accounted for by one of the four exclusions in the paper. -/
theorem association_good_targets_lower_bound {F : SimpleHypergraph V} {r Δ : ℕ}
    (hr : 3≤r) (hF : F ⊆ completeEdges V r) (hdeg : ∀ v, vertexDegree F v ≤ Δ)
    (B : Finset V) {e : Finset V} {z : V} (he : e∈F) (hz : z∈e) :
    (graphIncidences F).card ≤ (associationGoodTargets F B e z).card +
      (∑v∈B, vertexDegree F v) + r^2*Δ + 2*Δ^2 := by
  let I := graphIncidences F
  let G := associationGoodTargets F B e z
  let A := I.filter (fun p => p.2∈B)
  let M := I.filter (fun p => ¬Disjoint e p.1)
  let C₁ := I.filter (fun p => p.2∉e ∧ switchedEdge e z p.2∈F)
  let C₂ := I.filter (fun p => z∉p.1 ∧ switchedEdge p.1 p.2 z∈F)
  have hcover : I ⊆ G ∪ (A ∪ (M ∪ (C₁ ∪ C₂))) := by
    intro p hp
    have hm := (mem_graphIncidences F p).mp hp
    simp only [mem_union]
    by_cases hB : p.2∈B
    · exact Or.inr (Or.inl (mem_filter.mpr ⟨hp,hB⟩))
    by_cases hd : Disjoint e p.1
    · have hae : p.2∉e := fun ha => disjoint_left.mp hd ha hm.2
      have hzf : z∉p.1 := fun hzf => disjoint_left.mp hd hz hzf
      by_cases h₁ : switchedEdge e z p.2∈F
      · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_filter.mpr ⟨hp,hae,h₁⟩))))
      by_cases h₂ : switchedEdge p.1 p.2 z∈F
      · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_filter.mpr ⟨hp,hzf,h₂⟩))))
      · exact Or.inl (mem_filter.mpr ⟨hp,hB,hd,h₁,h₂⟩)
    · exact Or.inr (Or.inr (Or.inl (mem_filter.mpr ⟨hp,hd⟩)))
  have htotal : I.card ≤ G.card+A.card+M.card+C₁.card+C₂.card := by
    have h := card_le_card hcover
    have h₁ := card_union_le G (A ∪ (M ∪ (C₁ ∪ C₂)))
    have h₂ := card_union_le A (M ∪ (C₁ ∪ C₂))
    have h₃ := card_union_le M (C₁ ∪ C₂)
    have h₄ := card_union_le C₁ C₂
    omega
  have hecard : e.card=r := (mem_completeEdges r e).mp (hF he)
  have hM := association_meeting_targets_le hF hdeg e hecard
  have hA : A.card=∑v∈B,vertexDegree F v := graphIncidences_heads_card F B
  have hnonempty : (e.erase z).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem hz,hecard]
    omega
  obtain ⟨w,hw⟩ := hnonempty
  have h₁ := association_first_collision_le hdeg hw
  have h₂ := association_second_collision_le (by omega : 2≤r) hF hdeg z
  change M.card≤r^2*Δ at hM
  change C₁.card≤Δ^2 at h₁
  change C₂.card≤Δ^2 at h₂
  change I.card≤G.card+(∑v∈B,vertexDegree F v)+r^2*Δ+2*Δ^2
  omega

/-- The same exact count in the fixed prescribed-degree model. -/
theorem association_good_targets_fixed {r : ℕ} {d : V→ℕ} (hr : 3≤r)
    (F : FixedDegreeState V r d) (B : Finset V) {e : Finset V} {z : V}
    (he : e∈F.val) (hz : z∈e) :
    (graphIncidences F.val).card ≤ (associationGoodTargets F.val B e z).card +
      associationBadBudget r d B := by
  have h := association_good_targets_lower_bound hr F.property.1
    (fun v => (F.property.2 v).trans_le (degree_le_maximum d v)) B he hz
  simp_rw [F.property.2] at h
  simpa only [associationBadBudget,degreeOn,Nat.add_assoc] using h
end LooseHamilton
