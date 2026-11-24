import PLAStochastic.Index.CEPS.Output.Main
import PLAStochastic.Index.CEPS.Family.Defs
import PLAStochastic.ForMathlib.Analysis.Calculus.MellinEnvelope

/-!
# Track O: the high-frequency bound under the Sobolev hypotheses of the family interface

`outInput_of_cepsSobolev`: a nonnegative density `f` of a law on `(0, ∞)` with
`f ∈ CepsSobolevClass (r + 3) η` and `cepsSobolev (r + 3) η f ≤ R` is in the input class
`OutInput r (sobolevEnvConst r η R) (η/2)`: the weighted `L¹` bound of `f^{(i+1)}` gives the
envelope `|f^{(i)}| ≤ R e^{-η|x|}` (`abs_iteratedDeriv_le_of_weighted`), and the Mellin powers
are universal combinations of `x^j f^{(j)}` (`abs_mellinOp_iterate_le`).

`norm_charFun_lawPhi_le_of_cepsSobolev` is interface T2 in the form of the task: for every `r`
and class parameters `(D, θ, vlo, vhi, η, R)` there are `K, ε₀` with
`|u|^r |∫ e^{iux} d(lawPhi ε ν)| ≤ K ε^{r+2}` for all `ε ≥ ε₀`, all such `ν`, and all real `u`.
-/

noncomputable section

open MeasureTheory Set Finset Filter Topology
open scoped ENNReal

namespace PGM

/-- The envelope constant derived from a Sobolev bound. -/
def sobolevEnvConst (r : ℕ) (η R : ℝ) : ℝ :=
  R * (∑ a ∈ range (max r 1 + 1), mellinEnvConst a η) + R

/-- A continuous nonnegative density of a law on `(0, ∞)` vanishes on `(-∞, 0]`. -/
theorem eq_zero_of_nonpos_of_density {f : ℝ → ℝ} (hfc : Continuous f) (hpos : ∀ x, 0 ≤ f x)
    {ν : Measure ℝ} (hν : ν = volume.withDensity fun x => ENNReal.ofReal (f x))
    (hν0 : ν (Iic 0) = 0) : ∀ x ≤ 0, f x = 0 := by
  have hIio : ν (Iio 0) = 0 := measure_mono_null Iio_subset_Iic_self hν0
  rw [hν, withDensity_apply _ measurableSet_Iio,
    lintegral_eq_zero_iff hfc.measurable.ennreal_ofReal] at hIio
  have hae : f =ᵐ[volume.restrict (Iio 0)] fun _ => 0 := by
    filter_upwards [hIio] with x hx
    have : ENNReal.ofReal (f x) = 0 := hx
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp this) (hpos x)
  have hon : EqOn f (fun _ => 0) (Iio 0) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Iio hfc.continuousOn continuousOn_const
  intro x hx
  rcases hx.lt_or_eq with hlt | rfl
  · exact hon hlt
  · have h1 : Tendsto f (𝓝[<] 0) (𝓝 (f 0)) := hfc.continuousAt.continuousWithinAt.tendsto
    have h2 : Tendsto f (𝓝[<] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (Filter.eventually_of_mem self_mem_nhdsWithin
        fun y hy => (hon hy).symm)
    exact tendsto_nhds_unique h1 h2

/-- **The input class from the Sobolev hypotheses of the family interface.** -/
theorem outInput_of_cepsSobolev {r : ℕ} {η R : ℝ} (hη : 0 < η) {f : ℝ → ℝ}
    {ν : ProbabilityMeasure ℝ} (hpos : ∀ x, 0 ≤ f x)
    (hν : (ν : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f x))
    (hν0 : (ν : Measure ℝ) (Iic 0) = 0) (hf : CepsSobolevClass (r + 3) η f)
    (hR : cepsSobolev (r + 3) η f ≤ R) :
    OutInput r (sobolevEnvConst r η R) (η / 2) f ν := by
  have hR0 : 0 ≤ R := (cepsSobolev_nonneg _ _ _).trans hR
  have h0 := eq_zero_of_nonpos_of_density hf.continuous hpos hν hν0
  have hcd : ContDiff ℝ ((r + 3 : ℕ) : WithTop ℕ∞) f := hf.contDiff
  have hder : ∀ i < r + 3, ∀ x, |iteratedDeriv i f x| ≤ R * Real.exp (-η * |x|) := by
    intro i hi x
    refine (abs_iteratedDeriv_le_of_weighted hcd hη.le hf.integrable h0 hi x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine le_trans ?_ hR
    exact Finset.single_le_sum (f := fun j => ∫ x, Real.exp (η * |x|) * |iteratedDeriv j f x|)
      (fun _ _ => integral_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
      (Finset.mem_range.mpr (by omega))
  have hS0 : 0 ≤ ∑ a ∈ range (max r 1 + 1), mellinEnvConst a η :=
    Finset.sum_nonneg fun a _ => mellinEnvConst_nonneg a hη
  have hRE : R ≤ sobolevEnvConst r η R := by
    unfold sobolevEnvConst; nlinarith
  have hexp : ∀ x : ℝ, Real.exp (-η * |x|) ≤ Real.exp (-(η / 2) * |x|) := fun x =>
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x])
  refine ⟨by positivity, hpos, h0, hcd.of_le (by exact_mod_cast (show max r 2 ≤ r + 3 by omega)),
    hν, ?_, ?_⟩
  · intro a ha x
    have ha' : a ≤ r + 3 := by have := le_max_left r 1; omega
    have hbound := abs_mellinOp_iterate_le hcd ha' hη
      (fun j hj => hder j (by have := le_max_left r 1; omega)) x
    refine hbound.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    unfold sobolevEnvConst
    have : mellinEnvConst a η ≤ ∑ a ∈ range (max r 1 + 1), mellinEnvConst a η :=
      Finset.single_le_sum (f := fun a => mellinEnvConst a η)
        (fun a _ => mellinEnvConst_nonneg a hη) (Finset.mem_range.mpr (by omega))
    nlinarith
  · intro x
    have h2 : deriv (deriv f) = iteratedDeriv 2 f := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2]
    calc |iteratedDeriv 2 f x| ≤ R * Real.exp (-η * |x|) := hder 2 (by omega) x
      _ ≤ sobolevEnvConst r η R * Real.exp (-(η / 2) * |x|) :=
        mul_le_mul hRE (hexp x) (Real.exp_pos _).le (hR0.trans hRE)

/-- **Interface T2** (`design.md`): the high-frequency bound of the actual one-layer output,
for inputs in a fixed regular class with a density bounded in the exponentially weighted
`W^{r+3,1}` size. The constants depend only on `r` and the class parameters. -/
theorem norm_charFun_lawPhi_le_of_cepsSobolev (r : ℕ) {D θ vlo vhi η R : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hη : 0 < η) :
    ∃ K eps₀ : ℝ, 0 < eps₀ ∧ ∀ eps : ℝ, eps₀ ≤ eps → ∀ (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ),
      RegLaw D θ vlo vhi ν → (∀ x, 0 ≤ f x) →
      (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      CepsSobolevClass (r + 3) η f → cepsSobolev (r + 3) η f ≤ R →
      ∀ u : ℝ, |u| ^ r * ‖∫ x, Complex.exp (Complex.I * u * x) ∂(lawPhi eps ν : Measure ℝ)‖ ≤
        K * eps ^ (r + 2) := by
  refine ⟨outHighConst r D θ vlo (sobolevEnvConst r η R) (η / 2), outHighEps r D θ vlo vhi,
    lt_of_lt_of_le one_pos ((one_le_epsZero _ _).trans (le_max_left _ _)),
    fun eps heps ν f hreg hpos hν hf hR u => ?_⟩
  have hν0 : (ν : Measure ℝ) (Iic 0) = 0 := (hreg.momClass hθ hvlo).pos
  exact norm_charFun_lawPhi_le r hD hθ hvlo heps hreg (outInput_of_cepsSobolev hη hpos hν hν0 hf hR) u

end PGM
