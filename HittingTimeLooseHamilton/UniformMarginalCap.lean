module

public import HittingTimeLooseHamilton.UniformMarginalCapStatement
public import HittingTimeLooseHamilton.MarginalBootstrap

public section

/-! # Uniform marginal cap under the extension law (item 34)
The deterministic bootstrap and its common-event probability bound use the
same fixed constants and registry. A violating marginal can therefore occur
only outside that single common event, uniformly over the whole path.
-/
noncomputable section
namespace LooseHamilton.UniformMarginalCap
open Filter BootstrapCatalogue BootstrapConstants

/-- The manuscript's uniform marginal cap, with the constant chosen before
all instance parameters and with no auxiliary event in the conclusion. -/
theorem uniform_marginal_cap (r : ℕ) (hr : 3 ≤ r) : Statement r := by
  obtain ⟨c,C,D,hc,hC,hD,hprob,hdet⟩ :=
    MarginalBootstrap.fixed_constants_bootstrap r hr
  obtain ⟨Ndet,hNdet⟩ := eventually_atTop.mp hdet
  refine ⟨2*D,by positivity,?_⟩
  intro offset hoff ε hε
  obtain ⟨Nprob,hNprob⟩ := hprob 2 offset 1 (rootConstant c)
    (by norm_num) hoff (by norm_num) (rootConstant_pos hc) ε hε
  refine ⟨max Ndet Nprob,?_⟩
  intro N hN m ell M hadm
  letI := hadm.feasible
  obtain ⟨hroom,hcap⟩ := hNdet N ((le_max_left _ _).trans hN) m ell M offset hadm
  let tests := fixedRegistry (h:=4*r) hadm.marker_matching hr hroom
    (rootThreshold r) (rootThreshold r) (portThreshold r c)
  have hgood := hNprob N ((le_max_right _ _).trans hN) m ell M hadm tests
  have hbad : (extensionLaw r m ell).event
      (fun ω => ¬ RootFreeCommonEvent tests (4*r) c C 1 2 (rootConstant c) ω) ≤ ε := by
    rw [(extensionLaw r m ell).event_compl]
    linarith
  apply le_trans ?_ hbad
  apply (extensionLaw r m ell).event_mono
  intro ω hfail hω
  obtain ⟨j,hj,hK,hAj,e,he,hviol⟩ := hfail
  have hbound := (hcap (4*r) (4*r) 1 ω hω j hj hK hAj e).2
  exact (not_lt_of_ge hbound) hviol

end LooseHamilton.UniformMarginalCap

namespace LooseHamilton
/-- The assembled Theorem 10.1. -/
theorem theorem101 : Theorem101 := UniformMarginalCap.uniform_marginal_cap
end LooseHamilton
