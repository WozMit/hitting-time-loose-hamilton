module

public import HittingTimeLooseHamilton.PathPerturbationBasic
public import HittingTimeLooseHamilton.PathRegularityModels
public import HittingTimeLooseHamilton.TerminalFeasibilityScales

public section

noncomputable section
namespace LooseHamilton
open Finset Filter
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma partitionCount_nested_lipschitz (H : SimpleHypergraph V) (A B : Finset V)
    (hAB : A ⊆ B) (d : ℝ) (hdeg : ∀v,(vertexDegree H v:ℝ) ≤  d) :
    |(partitionCount H A:ℝ)-partitionCount H B| ≤  ((B.card:ℝ)-A.card)*d := by
  let G := survivingHost H (B\A)
  have hG : G ⊆ H := filter_subset _ _
  have heq : partitionCount G A = partitionCount G B := by
    unfold partitionCount
    congr 1
    apply filter_congr
    intro e he
    have hd := (mem_filter.mp he).2
    have hh : e∩A=e∩B := by
      ext v
      simp only [mem_inter]
      constructor
      · exact fun h => ⟨h.1,hAB h.2⟩
      · intro h
        refine ⟨h.1, ?_⟩
        by_contra hv
        exact disjoint_left.mp hd h.1 (mem_sdiff.mpr ⟨h.2,hv⟩)
    rw [hh]
  have hA := filter_card_loss_le hG (fun e => (e∩A).card=2)
  have hB := filter_card_loss_le hG (fun e => (e∩B).card=2)
  have hAc := card_le_card (filter_subset_filter (fun e => (e∩A).card=2) hG)
  have hBc := card_le_card (filter_subset_filter (fun e => (e∩B).card=2) hG)
  change partitionCount H A - partitionCount G A ≤  H.card-G.card at hA
  change partitionCount H B - partitionCount G B ≤  H.card-G.card at hB
  change partitionCount G A ≤  partitionCount H A at hAc
  change partitionCount G B ≤  partitionCount H B at hBc
  have hd := deletion_edge_loss_le H (B\A)
  have hdc : ((H.card-G.card:ℕ):ℝ) ≤  ((B\A).card:ℝ)*d := by
    calc
      _ ≤  ∑ v∈B\A, (vertexDegree H v:ℝ) := by exact_mod_cast hd
      _ ≤  ∑ _v∈B\A, d := sum_le_sum (fun v _ => hdeg v)
      _ = _ := by simp
  have hAr : (partitionCount H A:ℝ)-partitionCount G A ≤  ((H.card-G.card:ℕ):ℝ) := by exact_mod_cast hA
  have hBr : (partitionCount H B:ℝ)-partitionCount G B ≤  ((H.card-G.card:ℕ):ℝ) := by exact_mod_cast hB
  have hAcr : (partitionCount G A:ℝ)≤ partitionCount H A := by exact_mod_cast hAc
  have hBcr : (partitionCount G B:ℝ)≤ partitionCount H B := by exact_mod_cast hBc
  rw [card_sdiff_of_subset hAB, Nat.cast_sub (card_le_card hAB)] at hdc
  rw [abs_le]
  rw [heq] at hAr hAcr
  constructor <;> linarith

lemma exists_nested_set_card (A : Finset V) (m : ℕ) (hm : m≤ Fintype.card V) :
    ∃ B : Finset V, B.card=m ∧ (A⊆B ∨ B⊆A) := by
  by_cases ha : A.card≤  m
  · obtain ⟨B,hAB,hBU,hB⟩ := exists_subsuperset_card_eq (subset_univ A) ha (by simpa using hm)
    exact ⟨B,hB,Or.inl hAB⟩
  · obtain ⟨B,hBA,hB⟩ := exists_subset_card_eq (le_of_not_ge ha)
    exact ⟨B,hB,Or.inr hBA⟩

lemma partitionCount_near_card_lipschitz (H : SimpleHypergraph V) (A : Finset V)
    (m : ℕ) (hm : m≤ Fintype.card V) (d : ℝ)
    (hdeg : ∀v,(vertexDegree H v:ℝ)≤ d) :
    ∃ B : Finset V, B.card=m ∧
      |(partitionCount H A:ℝ)-partitionCount H B| ≤  |(A.card:ℝ)-m| *d := by
  obtain ⟨B,hB,hAB|hBA⟩ := exists_nested_set_card A m hm
  · refine ⟨B,hB,?_⟩
    have h := partitionCount_nested_lipschitz H A B hAB d hdeg
    have hc : (A.card:ℝ)≤ B.card := by exact_mod_cast card_le_card hAB
    rw [hB] at hc
    rw [abs_of_nonpos (by linarith : (A.card:ℝ)-m≤ 0)]
    rw [hB] at h
    linarith
  · refine ⟨B,hB,?_⟩
    have h := partitionCount_nested_lipschitz H B A hBA d hdeg
    have hc : (B.card:ℝ)≤ A.card := by exact_mod_cast card_le_card hBA
    rw [hB] at hc
    rw [abs_of_nonneg (by linarith : 0≤ (A.card:ℝ)-m)]
    rwa [abs_sub_comm, hB] at h

/-- Enlarging a fixed partition window costs at most a factor two in the
regularity constant once the explicitly displayed scalar inequalities hold. -/
theorem PathGraphUpperRegular.enlarge_window {r : ℕ} {C L L' : ℝ}
    {H : SimpleHypergraph V} (hr : 3≤ r) (hC : 0≤ C)
    (h : PathGraphUpperRegular r C L H)
    (hsmall : 1≤ L*(Fintype.card V:ℝ)^(1/10:ℝ))
    (hlarge : L'*(Fintype.card V:ℝ)^(1/10:ℝ)+1 ≤ 
      (Fintype.card V:ℝ)*(Real.log (Fintype.card V:ℝ))^(-1/8:ℝ)) :
    PathGraphUpperRegular r (2*C) L' H := by
  have hμ : 0≤ meanDegree (V:=V) r H.card := by unfold meanDegree; positivity
  have hCm : 0≤ C*meanDegree (V:=V) r H.card := mul_nonneg hC hμ
  refine ⟨?_,?_,?_⟩
  · intro v
    have := h.upper_degree v
    nlinarith
  · intro u v huv
    have hh := h.codegree u v huv
    have hp := mul_nonneg hCm (Real.rpow_nonneg (Real.log_natCast_nonneg (Fintype.card V)) (-1/4:ℝ))
    nlinarith
  · intro A hA
    let x : ℝ := junctionFraction r*Fintype.card V
    have hrR : (3:ℝ)≤ r := by exact_mod_cast hr
    have hrpos : (0:ℝ)<(r:ℝ)-1 := by linarith
    have hx : 0≤ x := by unfold x junctionFraction; positivity
    have hxN : x≤ Fintype.card V := by
      unfold x junctionFraction
      have hf : 1/((r:ℝ)-1)≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg (Fintype.card V): (0:ℝ)≤ Fintype.card V)]
    let m := Nat.floor x
    have hm : m≤ Fintype.card V := Nat.floor_le_of_le hxN
    have hf : (m:ℝ)≤ x := Nat.floor_le hx
    have hfloor : x<(m:ℝ)+1 := Nat.lt_floor_add_one x
    have hmx : |(m:ℝ)-x|≤ 1 := by rw [abs_le]; constructor <;> linarith
    obtain ⟨B,hB,hAB⟩ := partitionCount_near_card_lipschitz H A m hm
      (C*meanDegree (V:=V) r H.card) h.upper_degree
    have hBwindow : |(B.card:ℝ)-junctionFraction r*Fintype.card V|≤ 
        L*(Fintype.card V:ℝ)^(1/10:ℝ) := by
      rw [hB]
      exact hmx.trans hsmall
    have hBcount := h.partitions B hBwindow
    have hdist : |(A.card:ℝ)-m| ≤  L'*(Fintype.card V:ℝ)^(1/10:ℝ)+1 := by
      have ht := abs_sub_le (A.card:ℝ) x (m:ℝ)
      have hmxx : |x-(m:ℝ)|≤ 1 := by rwa [abs_sub_comm]
      change |(A.card:ℝ)-x|≤ _ at hA
      linarith
    have hpert := hAB.trans (mul_le_mul_of_nonneg_right (hdist.trans hlarge) hCm)
    have ht := abs_sub_le (partitionCount H A:ℝ) (partitionCount H B:ℝ)
      (partitionDensity r*H.card)
    calc
      _ ≤  _ := ht
      _ ≤  (Fintype.card V:ℝ)*(Real.log (Fintype.card V:ℝ))^(-1/8:ℝ)*
          (C*meanDegree (V:=V) r H.card)+
          C*Fintype.card V*meanDegree (V:=V) r H.card*
            (Real.log (Fintype.card V:ℝ))^(-1/8:ℝ) := add_le_add hpert hBcount
      _ = _ := by ring

end LooseHamilton
