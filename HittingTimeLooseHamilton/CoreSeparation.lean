module

public import HittingTimeLooseHamilton.CoreBergePaths

public section

/-! Separation of selected exceptional edges and uniqueness of contacted blocks. -/
noncomputable section
namespace LooseHamilton
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two intersecting incident edges give a Berge path with at most two edges. -/
theorem shortBergeConnected_of_incident_intersection {H : SimpleHypergraph V}
    {u v x : V} {e f : Finset V} (he : e ∈ H) (hf : f ∈ H)
    (hu : u ∈ e) (hv : v ∈ f) (hxe : x ∈ e) (hxf : x ∈ f) (huv : u ≠ v) :
    shortBergeConnected H u v := by
  by_cases hef : e=f
  · exact shortBergeConnected_one he hu (by simpa only [hef] using hv) huv
  by_cases hux : u=x
  · exact shortBergeConnected_one hf (by simpa only [hux] using hxf) hv huv
  by_cases hxv : x=v
  · exact shortBergeConnected_one he hu (by simpa only [hxv] using hxe) huv
  exact shortBergeConnected_two he hf hu hxe hxf hv huv hux hxv hef

/-- Choosing one incident edge at each separated anchor yields disjoint edges. -/
theorem selected_edges_pairwise_disjoint {H : SimpleHypergraph V} {B : Finset V}
    (edge : ↥B → Finset V) (hedge : ∀ v, edge v ∈ H) (hanchor : ∀ v, v.val ∈ edge v)
    (hsep : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → ¬ shortBergeConnected H u v) :
    Pairwise (fun u v => Disjoint (edge u) (edge v)) := by
  intro u v huv
  apply disjoint_left.mpr
  intro x hxu hxv
  have hne : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  exact hsep u.val u.property v.val v.property hne
    (shortBergeConnected_of_incident_intersection (hedge u) (hedge v)
      (hanchor u) (hanchor v) hxu hxv hne)

/-- A four-edge route through disjoint selected edges contains a short Berge
path, even when the two middle edges or adjacent vertices coincide. -/
theorem shortBergeConnected_of_two_block_contacts {H : SimpleHypergraph V}
    {u x w y v : V} {e f g k : Finset V}
    (he : e ∈ H) (hf : f ∈ H) (hg : g ∈ H) (hk : k ∈ H)
    (hu : u ∈ e) (hxe : x ∈ e) (hxf : x ∈ f) (hwf : w ∈ f)
    (hwg : w ∈ g) (hyg : y ∈ g) (hyk : y ∈ k) (hv : v ∈ k)
    (hek : Disjoint e k) (hwu : w ≠ u) (hwx : w ≠ x) (hwy : w ≠ y) (hwv : w ≠ v) :
    shortBergeConnected H u v := by
  have hcross {a b : V} (ha : a ∈ e) (hb : b ∈ k) : a ≠ b := by
    intro hab
    exact disjoint_left.mp hek ha (by simpa only [hab] using hb)
  have huw : u ≠ w := Ne.symm hwu
  have hxw : x ≠ w := Ne.symm hwx
  have huv := hcross hu hv
  have huy := hcross hu hyk
  have hxv := hcross hxe hv
  have hxy := hcross hxe hyk
  have hek' : e ≠ k := by
    intro hh
    exact disjoint_left.mp hek hu (by simpa only [hh] using hu)
  have hfk : f ≠ k := by
    intro hh
    exact disjoint_left.mp hek hxe (by simpa only [hh] using hxf)
  have heg : e ≠ g := by
    intro hh
    exact disjoint_left.mp hek (by simpa only [hh] using hyg) hyk
  by_cases hfg : f=g
  · subst g
    by_cases hux : u=x
    · by_cases hvy : v=y
      · exact shortBergeConnected_one hf (by simpa only [hux] using hxf) (by simpa only [hvy] using hyg) huv
      · exact shortBergeConnected_two hf hk (by simpa only [hux] using hxf) hyg hyk hv
          huv huy (Ne.symm hvy) hfk
    · by_cases hvy : v=y
      · exact shortBergeConnected_two he hf hu hxe hxf (by simpa only [hvy] using hyg)
          huv hux hxv heg
      · apply shortBergeConnected_three he hf hk hu hxe hxf hyg hyk hv
        · simp_all [List.pairwise_cons, ne_comm]
        · simp_all [List.pairwise_cons, ne_comm]
  · by_cases hleft : f=e ∨ u=x
    · have huf : u ∈ f := by
        rcases hleft with hh | hh
        · simpa only [hh] using hu
        · simpa only [hh] using hxf
      by_cases hright : g=k ∨ v=y
      · have hvg : v ∈ g := by
          rcases hright with hh | hh
          · simpa only [hh] using hv
          · simpa only [hh] using hyg
        exact shortBergeConnected_two hf hg huf hwf hwg hvg huv (Ne.symm hwu) hwv hfg
      · have hgk : g ≠ k := fun hh => hright (Or.inl hh)
        have hvy : v ≠ y := fun hh => hright (Or.inr hh)
        apply shortBergeConnected_three hf hg hk huf hwf hwg hyg hyk hv
        · simp_all [List.pairwise_cons, ne_comm]
        · simp_all [List.pairwise_cons, ne_comm]
    · have hef : e ≠ f := fun hh => hleft (Or.inl hh.symm)
      have hux : u ≠ x := fun hh => hleft (Or.inr hh)
      by_cases hright : g=k ∨ v=y
      · have hvg : v ∈ g := by
          rcases hright with hh | hh
          · simpa only [hh] using hv
          · simpa only [hh] using hyg
        apply shortBergeConnected_three he hf hg hu hxe hxf hwf hwg hvg
        · simp_all [List.pairwise_cons, ne_comm]
        · simp_all [List.pairwise_cons, ne_comm]
      · have hgk : g ≠ k := fun hh => hright (Or.inl hh)
        have hvy : v ≠ y := fun hh => hright (Or.inr hh)
        apply shortBergeConnected_four he hf hg hk hu hxe hxf hwf hwg hyg hyk hv
        · simp_all [List.pairwise_cons, ne_comm]
        · simp_all [List.pairwise_cons, ne_comm]

/-- A surviving vertex can contact private vertices of at most one selected
block; the anchor separation hypothesis concerns the original host. -/
theorem contacted_block_unique {H : SimpleHypergraph V} {B : Finset V}
    (edge block : ↥B → Finset V) (hedge : ∀ v, edge v ∈ H)
    (hanchor : ∀ v, v.val ∈ block v) (hblock : ∀ v, block v ⊆ edge v)
    (hsep : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → ¬ shortBergeConnected H u v)
    {w : V} (hw : w ∉ univ.biUnion block)
    {u v : ↥B} {x y : V} {f g : Finset V}
    (hxu : x ∈ block u) (hyv : y ∈ block v)
    (hf : f ∈ H) (hg : g ∈ H) (hxf : x ∈ f) (hwf : w ∈ f)
    (hyg : y ∈ g) (hwg : w ∈ g) : u=v := by
  by_contra huv
  have hne : u.val ≠ v.val := fun hh => huv (Subtype.ext hh)
  have hdis := selected_edges_pairwise_disjoint edge hedge
    (fun a => hblock a (hanchor a)) hsep huv
  have hnot (a : ↥B) (z : V) (hz : z ∈ block a) : w ≠ z := by
    intro hwz
    exact hw (mem_biUnion.mpr ⟨a, mem_univ _, by simpa only [hwz] using hz⟩)
  exact hsep u.val u.property v.val v.property hne
    (shortBergeConnected_of_two_block_contacts (hedge u) hf hg (hedge v)
      (hblock u (hanchor u)) (hblock u hxu) hxf hwf hwg hyg (hblock v hyv)
      (hblock v (hanchor v)) hdis (hnot u _ (hanchor u)) (hnot u _ hxu)
      (hnot v _ hyv) (hnot v _ (hanchor v)))
end LooseHamilton
