import PLAStochastic.Index.CEPS.ZeroOrder.CharDistance
import PLAStochastic.Index.CEPS.Leading.Proxy
import PLAStochastic.Index.CEPS.Assembly.Interfaces

/-!
# C-16 support: the output characteristic function converges to `φ_Λ`

`cepsOutChar eps ν u` is the characteristic function of the raw law `Law(v S_T / ε²)` at
`u / s_ε`, `s_ε = v C_ε / ε² → κ`; the raw law converges to the Brownian lifetime `cepsTau`
in the weighted `W₁` distance (`ceps_rawLaw_distance_on_regular_class`), and
`φ_Λ(u) = E e^{iuτ/κ}`. Hence `cepsOutChar eps ν (U eps) → φ_Λ(u₀)` whenever `U eps → u₀`,
on every regular law. No Sobolev input is needed here.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory BrownianAffine Filter Topology Set
open scoped ENNReal

/-- The scale `s_ε = v C_ε / ε²` relating the output law to the raw law. -/
def cepsRawScale (eps : ℝ) (ν : ProbabilityMeasure ℝ) : ℝ := lawVar ν * lawC eps ν / eps ^ 2

/-- The output characteristic function as a characteristic integral of the raw law. -/
theorem cepsOutChar_eq_rawLaw_integral {eps : ℝ} {ν : ProbabilityMeasure ℝ}
    (hv : 0 < lawVar ν) (hC : 0 < lawC eps ν) (heps : 0 < eps) (u : ℝ) :
    cepsOutChar eps ν u =
      ∫ x, Complex.exp (Complex.I * ((u / cepsRawScale eps ν : ℝ) : ℂ) * x)
        ∂(rawLaw eps ν : Measure ℝ) := by
  unfold cepsOutChar
  change ∫ x, Complex.exp (Complex.I * u * x) ∂((iidLaw ν).map (fun g => stopSum eps g / lawC eps ν)) =
    ∫ x, Complex.exp (Complex.I * ((u / cepsRawScale eps ν : ℝ) : ℂ) * x)
      ∂((iidLaw ν).map (fun g => lawVar ν * stopSum eps g / eps ^ 2))
  rw [integral_map ((measurable_stopSum eps).div_const _).aemeasurable
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (Complex.I * u * x)).aestronglyMeasurable,
    integral_map (((measurable_stopSum eps).const_mul _).div_const _).aemeasurable
    (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (Complex.I * ((u / cepsRawScale eps ν : ℝ) : ℂ) * x)).aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show Complex.exp _ = Complex.exp _
  congr 1
  unfold cepsRawScale
  push_cast
  have hv' : (lawVar ν : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  have hC' : (lawC eps ν : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have he' : (eps : ℂ) ≠ 0 := by exact_mod_cast heps.ne'
  field_simp

/-- `φ_Λ(u) = E e^{iuτ/κ}` with `τ` the unnormalized Brownian lifetime. -/
theorem cepsLambdaChar_eq_cepsTau_integral (u : ℝ) :
    cepsLambdaChar u =
      ∫ x, Complex.exp (Complex.I * ((u / optimalMeanConstant : ℝ) : ℂ) * x)
        ∂(cepsTau : Measure ℝ) := by
  unfold cepsLambdaChar
  change ∫ x, Complex.exp (Complex.I * u * x) ∂(canonicalPreBrownianMeasure.map
      (fun ω => optimalUnitLifetime canonicalBrownian ω / optimalMeanConstant)) =
    ∫ x, Complex.exp (Complex.I * ((u / optimalMeanConstant : ℝ) : ℂ) * x)
      ∂(canonicalPreBrownianMeasure.map (optimalUnitLifetime canonicalBrownian))
  rw [integral_map ((aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian).div_const _)
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (Complex.I * u * x)).aestronglyMeasurable,
    integral_map (aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian)
    (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (Complex.I * ((u / optimalMeanConstant : ℝ) : ℂ) * x)).aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  show Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  ring

theorem continuous_cepsTau_charIntegral :
    Continuous fun a : ℝ => ∫ x, Complex.exp (Complex.I * a * x) ∂(cepsTau : Measure ℝ) := by
  have he : (fun a : ℝ => ∫ x, Complex.exp (Complex.I * a * x) ∂(cepsTau : Measure ℝ)) =
      charFun (cepsTau : Measure ℝ) := by
    funext a
    rw [charFun_apply_real]
    congr 1
    funext x
    ring_nf
  rw [he]
  exact continuous_charFun

/-- `φ_Λ` is continuous. -/
theorem continuous_cepsLambdaChar : Continuous cepsLambdaChar := by
  have he : cepsLambdaChar = fun u : ℝ =>
      ∫ x, Complex.exp (Complex.I * ((u / optimalMeanConstant : ℝ) : ℂ) * x)
        ∂(cepsTau : Measure ℝ) := funext cepsLambdaChar_eq_cepsTau_integral
  rw [he]
  exact continuous_cepsTau_charIntegral.comp (continuous_id.div_const _)

/-- **Convergence of the output characteristic function along moving frequencies.** On every
regular law, `cepsOutChar eps ν (U eps) → φ_Λ(u₀)` when `U eps → u₀`. -/
theorem cepsOutChar_tendsto_cepsLambdaChar_of_tendsto {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) {U : ℝ → ℝ} {u₀ : ℝ}
    (hU : Tendsto U atTop (𝓝 u₀)) :
    Tendsto (fun eps => cepsOutChar eps ν (U eps)) atTop (𝓝 (cepsLambdaChar u₀)) := by
  obtain ⟨γ₀, K, hγ₀, hK, hdist⟩ := ceps_rawLaw_distance_on_regular_class hD hθ hvlo hv
  obtain ⟨c, hc, hraw⟩ := ceps_rawLaw_exp_integrable_on_regular_class hD hθ hvlo hv
  obtain ⟨ζ, hζ, hτ⟩ := cepsTau_exp_integrable
  let γ := min γ₀ (min (c / 2) (ζ / 2))
  have hγ : 0 < γ := lt_min hγ₀ (lt_min (half_pos hc) (half_pos hζ))
  have hγc : γ < c := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hγζ : γ < ζ := (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by linarith))
  have hτi := integrable_mul_exp_of_exp_integrable cepsTau_nonneg hγζ hτ
  have hm := hν.momClass hθ hvlo
  have hvm := regV_pos hvlo
  have hvν : 0 < lawVar ν := hvm.trans_le hm.var_ge
  have hpos := ceps_rawLaw_nonneg hm.pos
  -- the scale `s_ε → κ` and the frequency `a_ε = U ε / s_ε → u₀ / κ`
  have hs : Tendsto (fun eps => cepsRawScale eps ν) atTop (𝓝 optimalMeanConstant) :=
    ceps_scaled_lawC_tendsto hD hθ hvlo hv hν
  have ha : Tendsto (fun eps => U eps / cepsRawScale eps ν) atTop
      (𝓝 (u₀ / optimalMeanConstant)) := hU.div hs optimalMeanConstant_pos.ne'
  -- the Brownian side converges by continuity
  have hg : Tendsto (fun eps => ∫ x, Complex.exp
      (Complex.I * ((U eps / cepsRawScale eps ν : ℝ) : ℂ) * x) ∂(cepsTau : Measure ℝ))
      atTop (𝓝 (cepsLambdaChar u₀)) := by
    rw [cepsLambdaChar_eq_cepsTau_integral]
    exact (continuous_cepsTau_charIntegral.tendsto _).comp ha
  -- the distance to the Brownian side vanishes
  have hbound : ∀ᶠ eps : ℝ in atTop,
      dist (∫ x, Complex.exp (Complex.I * ((U eps / cepsRawScale eps ν : ℝ) : ℂ) * x)
          ∂(cepsTau : Measure ℝ)) (cepsOutChar eps ν (U eps)) ≤
        2 * |U eps / cepsRawScale eps ν| * (K * eps ^ (-(17 / 32 : ℝ))) := by
    filter_upwards [hdist, hraw, eventually_ge_atTop (0 : ℝ),
      eventually_ge_atTop (epsZero (regB vhi) (regBeta D θ vlo)), eventually_gt_atTop (0 : ℝ)]
      with eps hd hi heps hez heps'
    obtain ⟨_, _, _, _, _, _, hCm, _⟩ := momClass_setup hvm hez hm
    have hC : 0 < lawC eps ν := (by positivity : 0 < eps ^ 2 / lawVar ν / 128).trans_le hCm
    rw [cepsOutChar_eq_rawLaw_integral hvν hC heps', dist_comm, dist_eq_norm]
    have hd' := (dEtaL_mono (show γ ≤ γ₀ from min_le_left _ _) (rawLaw eps ν) cepsTau).trans
      (hd ν hν)
    have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd'
    have hri := integrable_mul_exp_of_exp_integrable (hpos eps) hγc (hi ν hν)
    have h := norm_integral_cexp_sub_le_dEtaL (hpos eps) cepsTau_nonneg
      (U eps / cepsRawScale eps ν) hγ.le hri hτi hfin
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK (Real.rpow_nonneg heps _)) hd'
  have hzero : Tendsto (fun eps : ℝ =>
      2 * |U eps / cepsRawScale eps ν| * (K * eps ^ (-(17 / 32 : ℝ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun eps : ℝ => K * eps ^ (-(17 / 32 : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 17 / 32)).const_mul K
    simpa only [mul_zero] using (ha.abs.const_mul 2).mul h1
  refine hg.congr_dist ?_
  exact squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hbound hzero

/-- **The pointwise limit of the output characteristic function is `φ_Λ`.** -/
theorem cepsOutChar_tendsto_cepsLambdaChar {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (u : ℝ) :
    Tendsto (fun eps => cepsOutChar eps ν u) atTop (𝓝 (cepsLambdaChar u)) :=
  cepsOutChar_tendsto_cepsLambdaChar_of_tendsto hD hθ hvlo hv hν tendsto_const_nhds

end

end PGM
