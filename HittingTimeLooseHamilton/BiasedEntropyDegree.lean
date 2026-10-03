module

public import HittingTimeLooseHamilton.BiasedEntropyMeanAverage

public section

noncomputable section
namespace LooseHamilton.BiasedRoleInstance
open Finset FiniteEntropy
variable {r : ℕ}

@[expose] def auxDegree (D : BiasedRoleInstance r) (C : ℝ) : ℕ := ⌈(r:ℝ)^2*C*D.μ⌉₊
@[expose] def clonePairBound (D : BiasedRoleInstance r) : ℕ := r*r*maxPairDegree D.host
@[expose] def cloneCollisionRate (D : BiasedRoleInstance r) (C : ℝ) : ℝ :=
  (r.choose 2:ℝ)*D.clonePairBound/D.auxDegree C

lemma max_degree_real_le (D : BiasedRoleInstance r) (C : ℝ)
    (hdeg : ∀v, (vertexDegree D.host v:ℝ)≤C*D.μ) :
    (maxVertexDegree D.host:ℝ)≤C*D.μ := by
  have hne : (univ : Finset (Fin D.N)).Nonempty := ⟨D.initial.val,mem_univ _⟩
  obtain ⟨v,_,hv⟩ := exists_mem_eq_sup univ hne (vertexDegree D.host)
  change ((univ.sup (vertexDegree D.host):ℕ):ℝ)≤_
  rw [hv]
  exact hdeg v

lemma ensemble_degree_le_auxDegree (D : BiasedRoleInstance r) (hr : 3≤r)
    (C : ℝ) (hdeg : ∀v, (vertexDegree D.host v:ℝ)≤C*D.μ)
    (z : D.ensembleIndex) (v : Fin (r*D.k)) :
    Fintype.card (KahnIncident (D.ensembleHost hr z) v) ≤ D.auxDegree C := by
  have hh := biasedCloneKahnHost_degree D.uniformCard D.root D.initial
    (BiasedEnsemble.reference D.root D.initial D.cycleLaw z)
    (BiasedEnsemble.labels hr D.root D.initial D.cycleLaw z) v
  apply hh.trans
  have hle : ((r*r*maxVertexDegree D.host:ℕ):ℝ)≤(r:ℝ)^2*C*D.μ := by
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left (D.max_degree_real_le C hdeg)
      (sq_nonneg (r:ℝ))]
  unfold auxDegree
  exact_mod_cast hle.trans (Nat.le_ceil ((r:ℝ)^2*C*D.μ))

lemma auxDegree_pos (D : BiasedRoleInstance r) (hr : 3≤r) (C : ℝ) (hC : 0<C) :
    0<D.auxDegree C := by
  have hx : 0<(r:ℝ)^2*C*D.μ := mul_pos
    (mul_pos (sq_pos_of_pos (by exact_mod_cast (show 0<r by omega))) hC) (D.μ_pos hr)
  have hh := Nat.le_ceil ((r:ℝ)^2*C*D.μ)
  have hpos : (0:ℝ)<D.auxDegree C := hx.trans_le hh
  exact_mod_cast hpos

lemma auxDegree_le (D : BiasedRoleInstance r) (C : ℝ) (hC : 0≤C) (hμ : 1≤D.μ) :
    (D.auxDegree C:ℝ)≤((r:ℝ)^2*C+1)*D.μ := by
  have hm : 0≤D.μ := by linarith
  have hh := Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (sq_nonneg (r:ℝ)) hC) hm)
  change (⌈(r:ℝ)^2*C*D.μ⌉₊:ℝ)≤_
  nlinarith only [hh,hμ]

lemma clonePairBound_pos (D : BiasedRoleInstance r) (hr : 3≤r) : 0<D.clonePairBound :=
  Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (D.maxPairDegree_pos hr)

lemma ensemble_pair_bound (D : BiasedRoleInstance r) (hr : 3≤r)
    (z : D.ensembleIndex) (q : Finset (Fin (r*D.k))) (hq : q.card=2) :
    ((D.ensembleHost hr z).edges.filter (q ⊆ ·)).card ≤ D.clonePairBound :=
  biasedCloneKahnHost_pairSubset D.uniformCard D.root D.initial
    (BiasedEnsemble.reference D.root D.initial D.cycleLaw z)
    (BiasedEnsemble.labels hr D.root D.initial D.cycleLaw z) q hq

lemma cloneCollisionRate_pos (D : BiasedRoleInstance r) (hr : 3≤r) (C : ℝ) (hC : 0<C) :
    0<D.cloneCollisionRate C := by
  have hchoose : (0:ℝ)<r.choose 2 := by
    exact_mod_cast Nat.choose_pos (by omega : 2≤r)
  exact div_pos (mul_pos hchoose (by exact_mod_cast D.clonePairBound_pos hr))
    (by exact_mod_cast D.auxDegree_pos hr C hC)

lemma cloneCollisionRate_le (D : BiasedRoleInstance r) (hr : 3≤r) (C : ℝ) (hC : 0<C) :
    D.cloneCollisionRate C ≤ ((r.choose 2:ℝ)/C)*D.η := by
  have hrp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hμ := D.μ_pos hr
  have hden : 0<(r:ℝ)^2*C*D.μ := by positivity
  have hle := Nat.le_ceil ((r:ℝ)^2*C*D.μ)
  have hp : 0≤(r.choose 2:ℝ)*D.clonePairBound := by positivity
  unfold cloneCollisionRate
  calc
    _ ≤ (r.choose 2:ℝ)*D.clonePairBound/((r:ℝ)^2*C*D.μ) :=
      div_le_div_of_nonneg_left hp hden hle
    _ = _ := by
      unfold clonePairBound η
      push_cast
      field_simp
      <;> ring
end LooseHamilton.BiasedRoleInstance
