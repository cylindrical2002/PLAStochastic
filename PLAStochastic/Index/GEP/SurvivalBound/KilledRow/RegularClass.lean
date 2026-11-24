import PLAStochastic.Index.GEP.SurvivalBound.KilledRow.PointwiseBound
import PLAStochastic.Index.GEP.SurvivalBound.KilledRow.ComplexFourierGap

/-!
# WP4 `SurvivalBound`: killed rows for the regular class

Combination of the class-level complex Fourier gap (`kill_complex_charFun_gap`, at slope one) with
the killed `L²` gap and the mixed decomposition (`norm_kRow_le_gap_exp`), for the step laws of
`SurvivalBound`: `ν` regular (`RegLaw D θ vlo vhi`, density `f ≤ D e^{-θx} ≤ D`) and `σ` a direction
law (`SigmaLaw A θσ`, no density bound).

`norm_kRow_le_class`: there is `c₁ > 0` from the class such that for every `(A, θσ)` there is
`r > 0` with, on `J = [α, α + w]` (`w ≥ 1`), for `|a| ≥ 1/2`, `‖z‖ < r`, measurable `‖φ‖ ≤ 1`,
`n ≥ 1` and every `y`,

`‖kRow J ν σ z β a n φ y‖ ≤ 3 √(2 D w) e^{-c₁ (n-1)/(2w²)} + ‖z‖ⁿ`.

`integral_norm_kStepZ_sq_le_class` is the coefficient-one `L²` bound on any `J` under the same
smallness of `z`, and `norm_kRow_le_class_one` the corresponding pointwise row bound
`3 √(2 D w) + ‖z‖ⁿ` (used for the free short paths).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- A regular law has a density bounded by `D`. -/
theorem RegLaw.kill_density_le {D θ vlo vhi : ℝ} (hθ : 0 < θ) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
      (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  obtain ⟨f, hfm, hf0, hfz, hfD, hνf⟩ := hν.density
  have hD := hν.D_nonneg
  refine ⟨f, hfm, hf0, fun x => ?_, hνf⟩
  rcases le_or_gt x 0 with hx | hx
  · rw [hfz x hx]; exact hD
  · calc f x ≤ D * Real.exp (-θ * x) := hfD x
      _ ≤ D * 1 := by
          gcongr
          exact Real.exp_le_one_iff.2 (by nlinarith)
      _ = D := mul_one D

/-- **Killed rows for the regular class.**  For the class `(D, θ, vlo, vhi)` there is `c₁ > 0`
such that for every direction class `SigmaLaw A θσ` (`θσ > 0`) there is `r > 0` with: for
`RegLaw D θ vlo vhi ν`, `SigmaLaw A θσ σ`, `‖z‖ < r`, `J = [α, α + w]` with `w ≥ 1`, `|a| ≥ 1/2`,
measurable `φ` with `‖φ‖ ≤ 1`, `n ≥ 1` and every `y`,
`‖kRow J ν σ z β a n φ y‖ ≤ 3 √(2 D w) e^{-c₁ (n-1)/(2w²)} + ‖z‖ⁿ`. -/
theorem norm_kRow_le_class (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hvhi : vlo ≤ vhi) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ A θσ : ℝ, 0 < θσ → ∃ r : ℝ, 0 < r ∧
      ∀ ν σ : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν → SigmaLaw A θσ σ →
        ∀ z : ℂ, ‖z‖ < r → ∀ α w β a : ℝ, 1 ≤ w → 1 / 2 ≤ |a| →
          ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) → ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ,
            ‖kRow (Icc α (α + w)) ν σ z β a n φ y‖ ≤
              3 * Real.sqrt (2 * D * w) * Real.exp (-(c₁ * ((n : ℝ) - 1) / (2 * w ^ 2))) +
                ‖z‖ ^ n := by
  obtain ⟨c, hc0, hc1, hcl⟩ := kill_complex_charFun_gap D θ vlo vhi hD hθ hvlo hvhi
  refine ⟨killGapConst c (1 / 2), killGapConst_pos hc0 (by norm_num), ?_⟩
  intro A θσ hθσ
  obtain ⟨r, hr0, hr⟩ := hcl A θσ hθσ
  refine ⟨min r (1 / 3), lt_min hr0 (by norm_num), ?_⟩
  intro ν σ hν hσ z hz α w β a hw ha φ hφ hφ1 n hn y
  have hzr : ‖z‖ < r := hz.trans_le (min_le_left _ _)
  have hz3 : ‖z‖ ≤ 1 / 3 := hz.le.trans (min_le_right _ _)
  have hgap : ∀ t : ℝ, ‖(1 - z) * charFun (ν : Measure ℝ) t + z * charFun (σ : Measure ℝ) t‖ ^ 2 ≤
      1 - c * min (t ^ 2) 1 := by
    intro t
    have h := hr ν σ hν hσ z hzr 1 ⟨by norm_num, by norm_num⟩ t
    simpa only [one_mul] using h
  obtain ⟨f, hfm, hf0, hfD, hνf⟩ := hν.kill_density_le hθ
  have h := norm_kRow_le_gap_exp (ν := (ν : Measure ℝ)) (σ := (σ : Measure ℝ)) (α := α) (β := β)
    (a₀ := 1 / 2) hw hfm hf0 hfD hνf (by norm_num) ha hc0 hc1 hgap hz3 hφ hφ1 hn y
  have e : D * w / (1 / 2) = 2 * D * w := by ring
  rwa [e] at h

/-- **Killed rows for the regular class without a gap** (free short paths): with the radius `r`
of the class-level Fourier gap and `‖z‖ ≤ 1/2`, on any measurable `J` with `|J| ≤ w` and any
slope `|a| ≥ 1/2`, `‖kRow J ν σ z β a n φ y‖ ≤ 3 √(2 D w) + ‖z‖ⁿ` for `n ≥ 1` and every `y`. -/
theorem norm_kRow_le_class_one (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hvhi : vlo ≤ vhi) :
    ∀ A θσ : ℝ, 0 < θσ → ∃ r : ℝ, 0 < r ∧
      ∀ ν σ : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν → SigmaLaw A θσ σ →
        ∀ z : ℂ, ‖z‖ < r → ∀ (J : Set ℝ) (w β a : ℝ), MeasurableSet J →
          volume J ≤ ENNReal.ofReal w → 0 ≤ w → 1 / 2 ≤ |a| →
          ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) → ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ,
            ‖kRow J ν σ z β a n φ y‖ ≤ 3 * Real.sqrt (2 * D * w) + ‖z‖ ^ n := by
  obtain ⟨c, hc0, -, hcl⟩ := kill_complex_charFun_gap D θ vlo vhi hD hθ hvlo hvhi
  intro A θσ hθσ
  obtain ⟨r, hr0, hr⟩ := hcl A θσ hθσ
  refine ⟨min r (1 / 2), lt_min hr0 (by norm_num), ?_⟩
  intro ν σ hν hσ z hz J w β a hJ hJw hw ha φ hφ hφ1 n hn y
  have hzr : ‖z‖ < r := hz.trans_le (min_le_left _ _)
  have hz2 : ‖z‖ ≤ 1 / 2 := hz.le.trans (min_le_right _ _)
  have hm : ∀ t : ℝ, ‖(1 - z) * charFun (ν : Measure ℝ) t + z * charFun (σ : Measure ℝ) t‖ ≤ 1 := by
    intro t
    have h := hr ν σ hν hσ z hzr 1 ⟨by norm_num, by norm_num⟩ t
    simp only [one_mul] at h
    have hmin : 0 ≤ c * min (t ^ 2) 1 := mul_nonneg hc0.le (le_min (sq_nonneg _) zero_le_one)
    nlinarith [norm_nonneg ((1 - z) * charFun (ν : Measure ℝ) t + z * charFun (σ : Measure ℝ) t)]
  obtain ⟨f, hfm, hf0, hfD, hνf⟩ := hν.kill_density_le hθ
  have h := norm_kRow_le_of_mult_le_one (ν := (ν : Measure ℝ)) (σ := (σ : Measure ℝ)) (β := β)
    (a₀ := 1 / 2) hJ hJw hw hfm hf0 hfD hνf (by norm_num) ha hz2 hm hφ hφ1 hn y
  have e : D * w / (1 / 2) = 2 * D * w := by ring
  rwa [e] at h

/-- **Coefficient-one killed `L²` bound for the regular class**: under the smallness of `z` given
by the class-level Fourier gap, `∫ ‖kStepZ J ν σ z β a u‖² ≤ ∫ ‖u‖²` for every `J`, every slope
and `u` measurable in `L¹ ∩ L²`. -/
theorem integral_norm_kStepZ_sq_le_class (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    ∀ A θσ : ℝ, 0 < θσ → ∃ r : ℝ, 0 < r ∧
      ∀ ν σ : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν → SigmaLaw A θσ σ →
        ∀ z : ℂ, ‖z‖ < r → ∀ (J : Set ℝ) (β a : ℝ) (u : ℝ → ℂ), Measurable u → Integrable u →
          MemLp u 2 →
            ∫ y, ‖kStepZ J ν σ z β a u y‖ ^ 2 ≤ ∫ y, ‖u y‖ ^ 2 := by
  obtain ⟨c, hc0, -, hcl⟩ := kill_complex_charFun_gap D θ vlo vhi hD hθ hvlo hvhi
  intro A θσ hθσ
  obtain ⟨r, hr0, hr⟩ := hcl A θσ hθσ
  refine ⟨r, hr0, ?_⟩
  intro ν σ hν hσ z hz J β a u hu h1 h2
  refine integral_norm_kStepZ_sq_le (J := J) (β := β) (a := a) (fun t => ?_) hu h1 h2
  have h := hr ν σ hν hσ z hz 1 ⟨by norm_num, by norm_num⟩ t
  simp only [one_mul] at h
  have hmin : 0 ≤ c * min (t ^ 2) 1 := mul_nonneg hc0.le (le_min (sq_nonneg _) zero_le_one)
  have hsq : ‖(1 - z) * charFun (ν : Measure ℝ) t + z * charFun (σ : Measure ℝ) t‖ ^ 2 ≤ 1 := by
    linarith
  nlinarith [norm_nonneg ((1 - z) * charFun (ν : Measure ℝ) t + z * charFun (σ : Measure ℝ) t)]

end

end PGM
