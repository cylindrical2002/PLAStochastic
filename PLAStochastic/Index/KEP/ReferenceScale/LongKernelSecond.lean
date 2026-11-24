import PLAStochastic.Index.KEP.ReferenceScale.KernelSecond

/-!
# Endpoint-aware second derivatives of the actual long killed row

The existing Fourier/BV decomposition is discharged before retaining the final
two genuine convolution steps. Only its exponentially small remainder pays the
second derivative of the input density. The two one-step endpoint derivatives
remain explicit, ready for the physical slope integral.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepLongRowEnergy (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (D vlo vhi w β a : ℝ) (m k : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (Real.exp (-(krKappa D vlo vhi * (k / 4 : ℕ) / w ^ 2)) *
    (∫ y, krDens (Icc 0 w) ν f β a (m + 1) x y ^ 2) /
      (killCnu D vlo vhi * (k / 4 : ℕ)))

def kepLongRowVarBudget (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (D vlo vhi w β a : ℝ) (m k : ℕ) (x : ℝ) : ℝ :=
  (8 * Real.pi * Real.sqrt w +
    8 * Real.pi * Real.sqrt w / (1 - Real.sqrt (1 - killCnu D vlo vhi))) *
      kepLongRowEnergy ν f D vlo vhi w β a m k x

def kepLongRowRemBudget (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (D vlo vhi w β a : ℝ) (m k : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (1 - killCnu D vlo vhi) ^ (k / 2) *
    kepLongRowEnergy ν f D vlo vhi w β a m k x

theorem kepLongRowVarBudget_nonneg {D θ vlo vhi K L w A a β a' : ℝ}
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (m k : ℕ) (x : ℝ) :
    0 ≤ kepLongRowVarBudget ν f D vlo vhi w β a' m k x := by
  have hρ : Real.sqrt (1 - killCnu D vlo vhi) < 1 :=
    kBVHighStepL2_regLaw_factor_lt_one H.hD H.hvlo H.hvhi
  unfold kepLongRowVarBudget kepLongRowEnergy
  exact mul_nonneg (add_nonneg (by positivity)
    (div_nonneg (by positivity) (by linarith))) (Real.sqrt_nonneg _)

/-- No regular/remainder decomposition is assumed by this estimate. It is
obtained from the actual killed row and the class-uniform Fourier theorem. -/
theorem krDens_second_long_bound
    (p : HellingerDensity (volume : Measure ℝ)) (ν : ProbabilityMeasure ℝ)
    {D θ vlo vhi K L w A a β a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν p.density w A a β a')
    {f' f'' : ℝ → ℝ}
    (hp : Continuous p.density) (hp' : Continuous f') (hp'' : Continuous f'')
    (hpi' : Integrable f' volume) (hpi'' : Integrable f'' volume)
    (hd : ∀ t, HasDerivAt p.density (f' t) t)
    (hdd : ∀ t, HasDerivAt f' (f'' t) t)
    (m k : ℕ) (hk : 8 ≤ k) (x y : ℝ) :
    |truncatedConvolution 0 w (kepStepSpatialSecond f'' β a')
        (fun z => krDens (Icc 0 w) ν p.density β a' (m + k + 2) x z) y| ≤
      (D / |a'|) * kepLongRowVarBudget ν p.density D vlo vhi w β a' m k x *
        (((∫ t, |f' t|) / |a'|) +
          w * (|kepStepSpatialFirst f' β a' y| +
            |kepStepSpatialFirst f' β a' (y - w)|)) +
      ((∫ t, |f'' t|) / |a'| ^ 2) * Real.sqrt (D / |a'|) *
        kepLongRowRemBudget ν p.density D vlo vhi w β a' m k x := by
  obtain ⟨g, r, -, hg, -, -, hr, hr2, hs, hsum, hvar, hR⟩ :=
    krDens_long_real_decomposition ν H m k hk x
  apply krDens_second_of_decomposition p ν H.hw0.le hp hp' hp'' hpi' hpi'' hd hdd
    H.hfD H.hνf H.ha' (m + k) x (kepLongRowVarBudget_nonneg ν H m k x)
    hg hr hr2 hs
  · intro z
    have heq : m + k + 1 = m + 1 + k := by omega
    simpa only [heq] using hsum z
  · exact hvar
  · exact hR

/-- The bounded final convolution is twice classically differentiable on the
whole line, including both band endpoints. Its bound keeps the endpoint terms. -/
theorem hasDerivAt_kepFinalConvolutionFirst_long_bound
    (p : HellingerDensity (volume : Measure ℝ)) (ν : ProbabilityMeasure ℝ)
    {D θ vlo vhi K L w A a β a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν p.density w A a β a')
    {f' f'' : ℝ → ℝ}
    (hp : Continuous p.density) (hp' : Continuous f') (hp'' : Continuous f'')
    (hpi' : Integrable f' volume) (hpi'' : Integrable f'' volume)
    (hd : ∀ t, HasDerivAt p.density (f' t) t)
    (hdd : ∀ t, HasDerivAt f' (f'' t) t)
    (m k : ℕ) (hk : 8 ≤ k) (x y : ℝ) :
    ∃ v : ℝ,
      HasDerivAt (truncatedConvolution 0 w (kepStepSpatialFirst f' β a')
        (fun z => krDens (Icc 0 w) ν p.density β a' (m + k + 2) x z)) v y ∧
      |v| ≤
        (D / |a'|) * kepLongRowVarBudget ν p.density D vlo vhi w β a' m k x *
          (((∫ t, |f' t|) / |a'|) +
            w * (|kepStepSpatialFirst f' β a' y| +
              |kepStepSpatialFirst f' β a' (y - w)|)) +
        ((∫ t, |f'' t|) / |a'| ^ 2) * Real.sqrt (D / |a'|) *
          kepLongRowRemBudget ν p.density D vlo vhi w β a' m k x := by
  refine ⟨_, ?_, krDens_second_long_bound p ν H hp hp' hp'' hpi' hpi'' hd hdd m k hk x y⟩
  convert hasDerivAt_kepFinalConvolutionFirst ν (w := w) (β := β) (a := a')
    H.hf hp' hp'' hdd H.hf0 H.hfD (m + k + 1) x y using 1

end

end PGM
