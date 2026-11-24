import PLAStochastic.ForMathlib.Analysis.Asymptotics.InverseArithmetic
import PLAStochastic.Index.CEPS.FiniteLayer
import PLAStochastic.Index.CEPS.DensityResidual
import PLAStochastic.Index.CEPS.Reference.Density
import PLAStochastic.Index.CEPS.Leading.Limit
import PLAStochastic.Index.CEPS.Fluctuation.Basic

/-!
# The qualitative finite-depth route, with explicit expansion inputs

This is an intermediate conditional assembly. It does not establish P-CEPS:
fixed-depth scalar expansions and stabilized strong-norm residual estimates
must still be proved for the Brownian reference law.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

/-- The projections of fixed-depth expansion and stabilization consumed here.
The positive distance weight may shrink with the fixed depth. -/
structure CepsFixedDepthInputs (ν : ProbabilityMeasure ℝ) : Prop where
  proxy_expansion : ∀ j : ℕ, ∃ a : ℕ → ℝ,
    HasInverseExpansion (fun eps => cepsProxy eps ν j / eps ^ 2) a
  residual : ∀ j : ℕ, ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 < η → η < ηMax →
    IsInverseOrder (fun eps =>
      dEta η ((lawPhi eps)^[j] ν) ((lawPhi eps)^[j + 1] ν) +
        |lawVar ((lawPhi eps)^[j + 1] ν) - lawVar ((lawPhi eps)^[j] ν)|) (j + 1)

/-- Actual finite-layer scalar expansions supply the proxy projection by finite arithmetic. -/
theorem cepsProxy_hasInverseExpansion_of_components (ν : ProbabilityMeasure ℝ) (j : ℕ)
    {a b c : ℕ → ℝ}
    (ha : HasInverseExpansion (fun eps => lawVar ((lawPhi eps)^[j] ν)) a)
    (hb : HasInverseExpansion (fun eps => lawC eps ((lawPhi eps)^[j] ν) / eps ^ 2) b)
    (hc : HasInverseExpansion (fun eps => lawVar ((lawPhi eps)^[j + 1] ν)) c)
    (hc0 : c 0 ≠ 0) :
    ∃! d : ℕ → ℝ, HasInverseExpansion (fun eps => cepsProxy eps ν j / eps ^ 2) d := by
  obtain ⟨p, hp, -⟩ := ha.mul_exists hb
  have hq := hp.div_exists hc hc0
  have he (eps : ℝ) :
      (lawVar ((lawPhi eps)^[j] ν) * (lawC eps ((lawPhi eps)^[j] ν) / eps ^ 2)) /
        lawVar ((lawPhi eps)^[j + 1] ν) = cepsProxy eps ν j / eps ^ 2 := by
    unfold cepsProxy
    simp only [div_eq_mul_inv]
    ring
  simpa only [he] using hq

/-- Fixed-depth expansions and stabilized residuals suffice without a rate for
the qualitative joint-response coefficient. -/
theorem ceps_scaled_proxy_inverseOrder_of_fixed_depth {D θ vlo vhi eOrbit : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ)
    (hν : ∀ eps, eOrbit ≤ eps → ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] ν))
    (hexp : ∀ eps, eOrbit ≤ eps → ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] expPM))
    (hfix : CepsFixedDepthInputs ν) (M : ℕ) :
    IsInverseOrder (fun eps => gepC eps / eps ^ 2 - cepsProxy eps ν M / eps ^ 2) (M + 1) := by
  obtain ⟨a, ha⟩ := hfix.proxy_expansion M
  obtain ⟨ηMax, hηMax, hres⟩ := hfix.residual M
  obtain ⟨η, H, e0, hη, hηMax', hH, he0, hCpos, hpost⟩ :=
    ceps_log_error_on_regular_class hD hθ hvlo hv ν hν hexp hηMax
  obtain ⟨K, eRes, -, -, hres⟩ := (hres η hη hηMax').nonneg_witness
  have hLog : IsInverseOrder (fun eps => gepLogC eps - cepsProxyLog eps ν M) (M + 1) := by
    refine ⟨H * K, max e0 eRes, fun eps heps => ?_⟩
    have he := (le_max_left _ _).trans heps
    have hr := (le_max_right _ _).trans heps
    have hp := hpost eps he M
    have hd := hres eps hr
    rw [abs_of_nonneg (add_nonneg (dEta_nonneg _ _ _) (abs_nonneg _))] at hd
    calc
      |gepLogC eps - cepsProxyLog eps ν M| ≤ H * _ := hp
      _ ≤ H * (K * (eps⁻¹) ^ (M + 1)) := mul_le_mul_of_nonneg_left hd hH
      _ = (H * K) * (eps⁻¹) ^ (M + 1) := by ring
  have hsmall : ∀ᶠ eps in atTop, |gepLogC eps - cepsProxyLog eps ν M| ≤ 1 := by
    have ht := (hLog.tendsto_zero (Nat.succ_pos M)).abs
    simp only [abs_zero] at ht
    exact ht.eventually_le_const (by norm_num : (0 : ℝ) < 1)
  obtain ⟨B, -, hb⟩ := (ha M).bounded
  obtain ⟨L, eLog, -, -, hlog⟩ := hLog.nonneg_witness
  have herr : ∀ᶠ eps in atTop,
      |gepC eps / eps ^ 2 - cepsProxy eps ν M / eps ^ 2| ≤
        (2 * B * L) * (eps⁻¹) ^ (M + 1) := by
    filter_upwards [hsmall, hb, eventually_ge_atTop e0, eventually_ge_atTop eLog,
      eventually_ge_atTop eOrbit] with eps hs hb he0' heLog' heOrbit
    have hepos : 0 < eps := by linarith [(he0.trans he0')]
    have hv0 := hvlo.trans_le (hν eps heOrbit M).var_ge
    have hv1 := hvlo.trans_le (hν eps heOrbit (M + 1)).var_ge
    have hC := hCpos eps he0' M
    have hbp : cepsProxy eps ν M / eps ^ 2 ≤ B := (le_abs_self _).trans hb
    have ht := abs_scaled_gepC_sub_cepsProxy_le hepos hv0 hv1 hC hs (hlog eps heLog') hbp
    simpa only [mul_assoc] using ht
  obtain ⟨eps0, heps0⟩ := eventually_atTop.mp herr
  exact ⟨2 * B * L, eps0, heps0⟩

/-- The projected fixed-depth inputs give a unique all-orders expansion. -/
theorem gepC_hasInverseExpansion_of_fixed_depth {D θ vlo vhi eOrbit : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ)
    (hν : ∀ eps, eOrbit ≤ eps → ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] ν))
    (hexp : ∀ eps, eOrbit ≤ eps → ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] expPM))
    (hfix : CepsFixedDepthInputs ν) :
    ∃! a : ℕ → ℝ, HasInverseExpansion (fun eps => gepC eps / eps ^ 2) a := by
  apply existsUnique_inverseExpansion_of_finite_orders
  intro M
  obtain ⟨a, ha⟩ := hfix.proxy_expansion M
  exact ⟨a, (ha M).transfer (ceps_scaled_proxy_inverseOrder_of_fixed_depth hD hθ hvlo hv ν hν hexp hfix M)⟩

/-- A leading limit of the depth-zero proxy identifies the exact constant coefficient. -/
theorem gepC_coeff_zero_of_fixed_depth {D θ vlo vhi eOrbit L : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ)
    (hν : ∀ eps, eOrbit ≤ eps → ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] ν))
    (hexp : ∀ eps, eOrbit ≤ eps → ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] expPM))
    (hfix : CepsFixedDepthInputs ν)
    (hleading : Tendsto (fun eps => cepsProxy eps ν 0 / eps ^ 2) atTop (𝓝 L))
    {a : ℕ → ℝ} (ha : HasInverseExpansion (fun eps => gepC eps / eps ^ 2) a) : a 0 = L := by
  obtain ⟨b, hb⟩ := hfix.proxy_expansion 0
  have herror := ceps_scaled_proxy_inverseOrder_of_fixed_depth hD hθ hvlo hv ν hν hexp hfix 0
  have hf := (hb 0).transfer herror
  have hc : a 0 = b 0 := inverseExpansion_coeff_eq (ha 0) hf (by intro j hj; omega)
  exact hc.trans (tendsto_nhds_unique (hb 0).tendsto_zero_order hleading)

/-- The conditional assembly has exactly the quantifiers of the target statement. -/
theorem gepC_asymptoticExpansion_of_fixed_depth {D θ vlo vhi eOrbit : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ)
    (hν : ∀ eps, eOrbit ≤ eps → ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] ν))
    (hexp : ∀ eps, eOrbit ≤ eps → ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] expPM))
    (hfix : CepsFixedDepthInputs ν) :
    ∃! a : ℕ → ℝ, ∀ M : ℕ, ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps →
      |gepC eps / eps ^ 2 - ∑ j ∈ Finset.range (M + 1), a j * eps ^ (-(j : ℤ))| ≤
        K * eps ^ (-((M : ℤ) + 1)) := by
  simpa only [← hasInverseExpansion_iff_zpow] using
    gepC_hasInverseExpansion_of_fixed_depth hD hθ hvlo hv ν hν hexp hfix

/-- Orbit closure is discharged for a regular starting law. Only the finite-depth
expansion projections remain as analytic inputs. -/
theorem gepC_asymptoticExpansion_of_regLaw_fixed_depth {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ) (hν : RegLaw D θ vlo vhi ν) (hfix : CepsFixedDepthInputs ν) :
    ∃! a : ℕ → ℝ, ∀ M : ℕ, ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps →
      |gepC eps / eps ^ 2 - ∑ j ∈ Finset.range (M + 1), a j * eps ^ (-(j : ℤ))| ≤
        K * eps ^ (-((M : ℤ) + 1)) := by
  obtain ⟨Ds, θs, vlos, vhis, e0, hDs, hθs, hvlos, hvs, hνs, hexp⟩ :=
    exists_common_regular_orbits hD hθ hvlo hv ν hν
  exact gepC_asymptoticExpansion_of_fixed_depth hDs hθs hvlos hvs ν hνs hexp hfix

/-- The leading-coefficient readout after unconditional orbit closure. -/
theorem gepC_coeff_zero_of_regLaw_fixed_depth {D θ vlo vhi L : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ) (hν : RegLaw D θ vlo vhi ν) (hfix : CepsFixedDepthInputs ν)
    (hleading : Tendsto (fun eps => cepsProxy eps ν 0 / eps ^ 2) atTop (𝓝 L))
    {a : ℕ → ℝ} (ha : HasInverseExpansion (fun eps => gepC eps / eps ^ 2) a) : a 0 = L := by
  obtain ⟨Ds, θs, vlos, vhis, e0, hDs, hθs, hvlos, hvs, hνs, hexp⟩ :=
    exists_common_regular_orbits hD hθ hvlo hv ν hν
  exact gepC_coeff_zero_of_fixed_depth hDs hθs hvlos hvs ν hνs hexp hfix hleading ha

/-- The Brownian starting law needs no additional regularity or orbit-closure inputs. -/
theorem gepC_asymptoticExpansion_of_cepsLambda_fixed_depth
    (hfix : CepsFixedDepthInputs cepsLambda) :
    ∃! a : ℕ → ℝ, ∀ M : ℕ, ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps →
      |gepC eps / eps ^ 2 - ∑ j ∈ Finset.range (M + 1), a j * eps ^ (-(j : ℤ))| ≤
        K * eps ^ (-((M : ℤ) + 1)) := by
  obtain ⟨D, θ, hD, hθ, hν⟩ := exists_regLaw_cepsLambda
  exact gepC_asymptoticExpansion_of_regLaw_fixed_depth hD hθ
    BrownianAffine.optimalDispersionConstant_pos le_rfl cepsLambda hν hfix

/-- The exact Brownian leading value is read out once its proxy limit is proved. -/
theorem gepC_coeff_zero_of_cepsLambda_fixed_depth
    (hfix : CepsFixedDepthInputs cepsLambda)
    (hleading : Tendsto (fun eps => cepsProxy eps cepsLambda 0 / eps ^ 2) atTop
      (𝓝 (BrownianAffine.optimalMeanConstant / BrownianAffine.optimalDispersionConstant)))
    {a : ℕ → ℝ} (ha : HasInverseExpansion (fun eps => gepC eps / eps ^ 2) a) :
    a 0 = BrownianAffine.optimalMeanConstant / BrownianAffine.optimalDispersionConstant := by
  obtain ⟨D, θ, hD, hθ, hν⟩ := exists_regLaw_cepsLambda
  exact gepC_coeff_zero_of_regLaw_fixed_depth hD hθ BrownianAffine.optimalDispersionConstant_pos
    le_rfl cepsLambda hν hfix hleading ha

/-- The actual normalized Brownian reference converges to the unchanged exact compression limit. -/
theorem tendsto_log_lawC_cepsLambda_orbit :
    ∃ e0 : ℝ, ∀ eps : ℝ, e0 ≤ eps →
      Tendsto (fun j : ℕ => Real.log (lawC eps ((lawPhi eps)^[j] cepsLambda)))
        atTop (𝓝 (gepLogC eps)) := by
  obtain ⟨D, θ, hD, hθ, hν⟩ := exists_regLaw_cepsLambda
  obtain ⟨e0, he⟩ := tendsto_log_lawC_orbit hD hθ BrownianAffine.optimalDispersionConstant_pos le_rfl
  exact ⟨e0, fun eps heps => he eps heps cepsLambda hν⟩

end

end PGM
