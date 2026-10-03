module

public import HittingTimeLooseHamilton.RootLinkUniformTail
public import HittingTimeLooseHamilton.RootLinkTailTransfer
public import HittingTimeLooseHamilton.RootLinkScales
public import HittingTimeLooseHamilton.UniformNestedOuter

public section

noncomputable section
namespace LooseHamilton
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma uniform_subset_occupancy_tail_arbitrary (U Γ : Finset A) (q a : ℕ)
    (hq : q≤U.card) (hU : 0<U.card) [Nonempty ↥(U.powersetCard q)] :
    (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard q)).event
      (fun B=>a≤(B.val∩Γ).card) ≤
        (q.choose a:ℝ)*(((Γ∩U).card:ℝ)/U.card)^a := by
  have he (B : ↥(U.powersetCard q)) : B.val∩(Γ∩U)=B.val∩Γ := by
    ext x
    simp only [mem_inter]
    have hx : x∈B.val→x∈U := fun hh => (mem_powersetCard.mp B.property).1 hh
    tauto
  simpa only [he] using uniform_subset_occupancy_tail U (Γ∩U) q a (show Γ∩U⊆U from inter_subset_right) hq hU

/-- Finite root-link tail with prescribed elements, without a deficit constraint. -/
theorem uniform_subset_prescribed_root_tail (U Γ R : Finset A) (q Q h : ℕ) (ρ : ℝ)
    (hqU : q≤U.card) (hU : 0<U.card) [Nonempty ↥(U.powersetCard q)]
    (hqQ : q≤Q) (hQ : 12*(h+1)≤Q) (hR : R.card≤h)
    (hρ : 0≤ρ) (hsmall : 8*ρ≤1)
    (hden : ((Γ∩U).card:ℝ)/U.card≤2*ρ) :
    (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard q)).event
      (fun B=>2*Q≤3*((B.val∪R)∩Γ).card) ≤ (8*ρ)^((Q:ℝ)/4) := by
  let a := (2*Q+2)/3-h-1
  have hmono : (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard q)).event
      (fun B=>2*Q≤3*((B.val∪R)∩Γ).card) ≤
      (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard q)).event
      (fun B=>a≤(B.val∩Γ).card) := by
    apply FiniteEntropy.Law.event_mono
    intro B hB
    have hh := prescribed_inter_card_le B.val R Γ
    dsimp [a]
    omega
  have ht := uniform_subset_occupancy_tail_arbitrary U Γ q a hqU hU
  have hpow : (q.choose a:ℝ)*(((Γ∩U).card:ℝ)/U.card)^a≤(q.choose a:ℝ)*(2*ρ)^a := by gcongr
  exact hmono.trans (ht.trans (hpow.trans (rootLink_prescribed_tail hqQ hQ hρ hsmall)))

/-- The unrestricted nested experiment has the same tail because its outer link is uniform. -/
theorem uniform_nested_prescribed_root_tail (U Γ R : Finset A) (b q Q h : ℕ) (ρ : ℝ)
    [Nonempty (FiniteNestedSubsets U b q)] (hqU : q≤U.card) (hU : 0<U.card)
    (hqQ : q≤Q) (hQ : 12*(h+1)≤Q) (hR : R.card≤h)
    (hρ : 0≤ρ) (hsmall : 8*ρ≤1)
    (hden : ((Γ∩U).card:ℝ)/U.card≤2*ρ) :
    (FiniteEntropy.uniform : FiniteEntropy.Law (FiniteNestedSubsets U b q)).event
      (fun B=>2*Q≤3*((B.val.2∪R)∩Γ).card) ≤ (8*ρ)^((Q:ℝ)/4) := by
  letI : Nonempty ↥(U.powersetCard q) := Nonempty.map (nestedOuter U b q) inferInstance
  have h := uniform_subset_prescribed_root_tail U Γ R q Q h ρ hqU hU hqQ hQ hR hρ hsmall hden
  rw [←uniform_nested_outer U b q,FiniteEntropy.Law.event_map] at h
  exact h

/-- A one-swap outer-link coupling preserves the same finite bound after prescribed edges. -/
theorem coupled_prescribed_root_tail {Ω : Type*} [Fintype Ω]
    (U Γ R : Finset A) (q Q h : ℕ) (ρ : ℝ)
    (hqU : q≤U.card) (hU : 0<U.card) [Nonempty ↥(U.powersetCard q)]
    (p : FiniteEntropy.Law Ω) (Y : Ω→Finset A)
    (π : FiniteEntropy.Law (↥(U.powersetCard q) × Ω))
    (hp : π.map Prod.fst=(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard q)))
    (hy : π.map Prod.snd=p)
    (hswap : ∀ z, 0<π.mass z → (Y z.2∩Γ).card≤(z.1.val∩Γ).card+1)
    (hqQ : q≤Q) (hQ : 12*(h+1)≤Q) (hR : R.card≤h)
    (hρ : 0≤ρ) (hsmall : 8*ρ≤1)
    (hden : ((Γ∩U).card:ℝ)/U.card≤2*ρ) :
    p.event (fun B=>2*Q≤3*((Y B∪R)∩Γ).card) ≤ (8*ρ)^((Q:ℝ)/4) := by
  let k := (2*Q+2)/3
  have hmono : p.event (fun B=>2*Q≤3*((Y B∪R)∩Γ).card) ≤
      p.event (fun B=>k≤((Y B∪R)∩Γ).card) := by
    apply FiniteEntropy.Law.event_mono
    intro B hB
    dsimp [k]
    omega
  have hc := coupled_prescribed_subset_tail
    (FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard q)) p π hp hy
    Subtype.val Y Γ R h k hR hswap
  have ht := uniform_subset_occupancy_tail_arbitrary U Γ q (k-(h+1)) hqU hU
  have hpow : (q.choose (k-(h+1)):ℝ)*(((Γ∩U).card:ℝ)/U.card)^(k-(h+1)) ≤
      (q.choose (k-(h+1)):ℝ)*(2*ρ)^(k-(h+1)) := by gcongr
  have ha : k-(h+1)=(2*Q+2)/3-h-1 := by dsimp [k]; omega
  rw [ha] at hpow ht hc
  exact hmono.trans (hc.trans (ht.trans (hpow.trans (rootLink_prescribed_tail hqQ hQ hρ hsmall))))
/-- Version using the outer-set laws directly, as returned by the fresh-extension coupling. -/
theorem coupled_prescribed_root_tail_finset
    (U Γ R : Finset A) (q Q h : ℕ) (ρ : ℝ)
    (hqU : q≤U.card) (hU : 0<U.card) [Nonempty ↥(U.powersetCard q)]
    (p : FiniteEntropy.Law (Finset A))
    (π : FiniteEntropy.Law (Finset A × Finset A))
    (hp : π.map Prod.fst=(FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard q)).map Subtype.val)
    (hy : π.map Prod.snd=p)
    (hswap : ∀ z, 0<π.mass z → (z.2∩Γ).card≤(z.1∩Γ).card+1)
    (hqQ : q≤Q) (hQ : 12*(h+1)≤Q) (hR : R.card≤h)
    (hρ : 0≤ρ) (hsmall : 8*ρ≤1)
    (hden : ((Γ∩U).card:ℝ)/U.card≤2*ρ) :
    p.event (fun B=>2*Q≤3*((B∪R)∩Γ).card) ≤ (8*ρ)^((Q:ℝ)/4) := by
  let k := (2*Q+2)/3
  have hmono : p.event (fun B=>2*Q≤3*((B∪R)∩Γ).card) ≤
      p.event (fun B=>k≤((B∪R)∩Γ).card) := by
    apply FiniteEntropy.Law.event_mono
    intro B hB
    dsimp [k]
    omega
  have hc := coupled_prescribed_subset_tail
    ((FiniteEntropy.uniform : FiniteEntropy.Law ↥(U.powersetCard q)).map Subtype.val) p π hp hy
    id id Γ R h k hR hswap
  rw [FiniteEntropy.Law.event_map] at hc
  have ht := uniform_subset_occupancy_tail_arbitrary U Γ q (k-(h+1)) hqU hU
  have hpow : (q.choose (k-(h+1)):ℝ)*(((Γ∩U).card:ℝ)/U.card)^(k-(h+1)) ≤
      (q.choose (k-(h+1)):ℝ)*(2*ρ)^(k-(h+1)) := by gcongr
  have ha : k-(h+1)=(2*Q+2)/3-h-1 := by dsimp [k]; omega
  rw [ha] at hpow ht hc
  exact hmono.trans (hc.trans (ht.trans (hpow.trans (rootLink_prescribed_tail hqQ hQ hρ hsmall))))
/-- The density hypothesis above follows from the original universe after bounded prescriptions. -/
lemma rootLink_density_after_prescriptions (Ω Γ R : Finset A) (ρ : ℝ)
    (hΩ : 0<Ω.card) (hR : R⊆Ω) (hhalf : 2*R.card≤Ω.card)
    (hρ : 0≤ρ) (hΓ : (Γ.card:ℝ)≤ρ*Ω.card) :
    ((Γ∩(Ω\R)).card:ℝ)/(Ω\R).card≤2*ρ := by
  have hb : ((Γ∩(Ω\R)).card:ℝ)≤ρ*Ω.card :=
    (Nat.cast_le.mpr (card_le_card inter_subset_left)).trans hΓ
  rw [card_sdiff_of_subset hR,Nat.cast_sub (card_le_card hR)]
  exact rootLink_remaining_density (by exact_mod_cast hΩ) (by exact_mod_cast hhalf) hρ hb
end LooseHamilton
