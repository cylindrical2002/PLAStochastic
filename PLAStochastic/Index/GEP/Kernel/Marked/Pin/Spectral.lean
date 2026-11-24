import PLAStochastic.Index.GEP.Kernel.Marked.Pin.TiltedDensity

/-! # Pointwise spectral decay of the genuine kernel density -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- A last true random step converts the existing killed-row spectral estimate
into a pointwise estimate for the selected density representative. -/
theorem kernel_regLaw_density_spectral (D θ vlo vhi a₀ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (ha₀ : 0 < a₀) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
      ∀ α w β a : ℝ, 1 ≤ w → a₀ ≤ |a| → ∀ n : ℕ, 2 ≤ n → ∀ y z : ℝ,
        krDens (Icc α (α + w)) ν f β a n y z ≤
          (D / a₀) * (3 * Real.sqrt (D * w / a₀) *
            Real.exp (-(c * ((n : ℝ) - 2) / (2 * w ^ 2)))) := by
  obtain ⟨c, hc, hb⟩ := kernel_norm_pure_row_regLaw_scaled D θ vlo vhi a₀ hD hθ hvlo hv ha₀
  refine ⟨c, hc, ?_⟩
  intro ν hν f hf hf0 hfD α w β a hw ha n hn y z
  let J := Icc α (α + w)
  let φ : ℝ → ℝ := fun u => krKer J f β a u z
  have hφ : Measurable φ :=
    (measurable_krKer_prod measurableSet_Icc hf β a).comp (measurable_id.prodMk measurable_const)
  have hφD (u : ℝ) : ‖(φ u : ℂ)‖ ≤ D / a₀ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_krKer_le hf0 hfD u z).trans
      (div_le_div_of_nonneg_left hD.le ha₀ ha)
  have hh := hb ν hν α w β a hw ha (fun u => (φ u : ℂ))
    (Complex.measurable_ofReal.comp hφ) (D / a₀) (div_pos hD ha₀) hφD
    (n - 1) (by omega) y
  have hi : J.indicator (fun u => (φ u : ℂ)) = fun u => (φ u : ℂ) := by
    funext u
    by_cases hu : u ∈ J
    · simp only [indicator_of_mem hu]
    · simp only [indicator_of_notMem hu, φ, krKer_eq_zero_of_left_notMem hu, Complex.ofReal_zero]
  change ‖((kStep J (ν : Measure ℝ) β a)^[n - 1]
    (J.indicator (fun u => (φ u : ℂ)))) y‖ ≤ _ at hh
  rw [hi, kernel_killed_ofReal] at hh
  have hnreal : ((n - 1 : ℕ) : ℝ) - 1 = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    ring
  rw [hnreal, Complex.norm_real, Real.norm_eq_abs] at hh
  have he := kernel_krDens_eq_iterate (J := J) measurableSet_Icc ν hf hf0 hfD β a n y z
  change krDens J ν f β a n y z = ((krStep J (ν : Measure ℝ) β a)^[n - 1] φ) y at he
  rw [← he, abs_of_nonneg (krDens_nonneg ν hf0 n y z)] at hh
  exact hh

/-- The same density estimate includes the one-step case. The harmless
negative time offset avoids an extra exceptional short-time branch in sums. -/
theorem kernel_regLaw_density_spectral_all (D θ vlo vhi a₀ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (ha₀ : 0 < a₀) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
      ∀ α w β a : ℝ, 1 ≤ w → a₀ ≤ |a| → ∀ n : ℕ, 1 ≤ n → ∀ y z : ℝ,
        krDens (Icc α (α + w)) ν f β a n y z ≤
          (D / a₀) * (1 + 3 * Real.sqrt (D * w / a₀)) *
            Real.exp (-(c * ((n : ℝ) - 2) / (2 * w ^ 2))) := by
  obtain ⟨c, hc, hb⟩ := kernel_regLaw_density_spectral D θ vlo vhi a₀ hD hθ hvlo hv ha₀
  refine ⟨c, hc, ?_⟩
  intro ν hν f hf hf0 hfD α w β a hw ha n hn y z
  by_cases hn2 : 2 ≤ n
  · apply (hb ν hν f hf hf0 hfD α w β a hw ha n hn2 y z).trans
    have h0 : 0 ≤ (D / a₀) * Real.exp (-(c * ((n : ℝ) - 2) / (2 * w ^ 2))) := by positivity
    nlinarith
  · have hn1 : n = 1 := by omega
    subst n
    have he : 1 ≤ Real.exp (-(c * ((1 : ℝ) - 2) / (2 * w ^ 2))) := by
      apply Real.one_le_exp_iff.mpr
      have hw0 : 0 < w := by linarith
      have hh : 0 ≤ c / (2 * w ^ 2) := by positivity
      convert hh using 1
      ring
    have hcoef : D / a₀ ≤ (D / a₀) * (1 + 3 * Real.sqrt (D * w / a₀)) := by
      have hh : 0 ≤ (D / a₀) * (3 * Real.sqrt (D * w / a₀)) := by positivity
      nlinarith
    apply ((krDens_le_div ν hf0 hfD 1 y z).trans
      (div_le_div_of_nonneg_left hD.le ha₀ ha)).trans
    exact hcoef.trans (le_mul_of_one_le_right (by positivity) (by simpa using he))

/-- A uniform right-row density bound is preserved by the actual marked
integration, since the left row has mass at most one. -/
theorem kernelFar_marked_le_right {J : Set ℝ} (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D B β a t : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (ha : a ≠ 0) (hB : 0 ≤ B) {l : ℕ} (hl : 1 ≤ l) (r : ℕ) (y z : ℝ)
    (hb : ∀ u, krDens J ν f β a r u z ≤ B) :
    kernelMarkedDens J ν f β a t l r y z ≤ B := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  have hI := (kr_integrable_krDens_right (β := β) (a := a) ν hJ hJfin hf hf0 hfD
    (k + 1) y).mul_const B
  have hh : kernelMarkedDens J ν f β a t (k + 1) r y z ≤
      ∫ u, krDens J ν f β a (k + 1) y u * B := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u => mul_nonneg
        (krDens_nonneg ν hf0 _ _ _) (krDens_nonneg ν hf0 _ _ _)) hI
    exact Filter.Eventually.of_forall fun u => mul_le_mul_of_nonneg_left
      (hb (u + β - a * t)) (krDens_nonneg ν hf0 _ _ _)
  rw [integral_mul_const, integral_krDens ν hJ hJfin hf hf0 hfD hν ha] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right (krSurv_le_one hJ ν β a (k + 1) y) hB).trans_eq
    (one_mul _))

/-- A uniform left-row density bound is preserved as well. Translation of the
right row has unit Jacobian, and its reversed survival mass is at most one. -/
theorem kernelFar_marked_le_left {J : Set ℝ} (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D B β a t : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (ha : a ≠ 0) (hB : 0 ≤ B) (l : ℕ) {r : ℕ} (hr : 1 ≤ r) (y z : ℝ)
    (hb : ∀ u, krDens J ν f β a l y u ≤ B) :
    kernelMarkedDens J ν f β a t l r y z ≤ B := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have hI := ((kr_integrable_krDens_left (β := β) (a := a) ν hJ hJfin hf hf0 hfD
    (k + 1) z).comp_add_right (β - a * t)).const_mul B
  have hh : kernelMarkedDens J ν f β a t l (k + 1) y z ≤
      ∫ u, B * krDens J ν f β a (k + 1) (u + (β - a * t)) z := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u => mul_nonneg
        (krDens_nonneg ν hf0 _ _ _) (krDens_nonneg ν hf0 _ _ _)) hI
    exact Filter.Eventually.of_forall fun u => by
      dsimp only
      rw [show u + (β - a * t) = u + β - a * t by ring]
      exact mul_le_mul_of_nonneg_right (hb u) (krDens_nonneg ν hf0 _ _ _)
  rw [integral_const_mul, integral_add_right_eq_self
    (fun u => krDens J ν f β a (k + 1) u z) (β - a * t),
    integral_krDens_left ν hJ hJfin hf hf0 hfD hν ha] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (krSurv_le_one hJ ν (-β) (-a) (k + 1) z) hB).trans_eq
    (mul_one _))

/-- The spectral tail of a marked pair depends on all three random lengths.
Only the established row gap is used; no endpoint loss or time summation is
hidden in this pointwise estimate. -/
theorem kernel_regLaw_marked_pair_spectral (D θ vlo vhi a₀ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (ha₀ : 0 < a₀) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ α w β a : ℝ, 1 ≤ w → a₀ ≤ |a| → ∀ t y z : ℝ,
      ∀ l r M : ℕ, 1 ≤ l → 1 ≤ r → 1 ≤ M →
        kernelMarkedDens (Icc α (α + w)) ν f β a t l r y z *
          krDens (Icc α (α + w)) ν f β a M z y ≤
          ((D / a₀) * (1 + 3 * Real.sqrt (D * w / a₀))) ^ 2 *
            Real.exp (-(c * (((l : ℝ) + r + M) - 8) / (4 * w ^ 2))) := by
  obtain ⟨c, hc, hb⟩ := kernel_regLaw_density_spectral_all D θ vlo vhi a₀ hD hθ hvlo hv ha₀
  refine ⟨c, hc, ?_⟩
  intro ν hν f hf hf0 hfD hνf α w β a hw ha t y z l r M hl hr hM
  let J := Icc α (α + w)
  let C := (D / a₀) * (1 + 3 * Real.sqrt (D * w / a₀))
  have hC : 0 ≤ C := by positivity
  have ha0 : a ≠ 0 := by intro he; simp [he] at ha; linarith
  have hJfin : volume J ≠ ⊤ := by simp [J]
  have hmark : kernelMarkedDens J ν f β a t l r y z ≤
      C * Real.exp (-(c * ((max l r : ℕ) - (2 : ℝ)) / (2 * w ^ 2))) := by
    by_cases hlr : l ≤ r
    · rw [max_eq_right hlr]
      exact kernelFar_marked_le_right measurableSet_Icc hJfin ν hf hf0 hfD hνf ha0
        (by positivity) hl r y z (fun u => hb ν hν f hf hf0 hfD α w β a hw ha r hr u z)
    · rw [max_eq_left (by omega : r ≤ l)]
      exact kernelFar_marked_le_left measurableSet_Icc hJfin ν hf hf0 hfD hνf ha0
        (by positivity) l hr y z (fun u => hb ν hν f hf hf0 hfD α w β a hw ha l hl y u)
  have hpin := hb ν hν f hf hf0 hfD α w β a hw ha M hM z y
  have hm : (l : ℝ) + r ≤ 2 * (max l r : ℕ) := by
    exact_mod_cast (show l + r ≤ 2 * max l r by omega)
  have hw0 : 0 < w := by linarith
  have hexp :
      -(c * ((max l r : ℕ) - (2 : ℝ)) / (2 * w ^ 2)) +
        -(c * ((M : ℝ) - 2) / (2 * w ^ 2)) ≤
      -(c * (((l : ℝ) + r + M) - 8) / (4 * w ^ 2)) := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * w ^ 2 by positivity)).mp
    field_simp
    nlinarith [mul_nonneg hc.le (show 0 ≤ (M : ℝ) by positivity)]
  calc
    _ ≤ (C * Real.exp (-(c * ((max l r : ℕ) - (2 : ℝ)) / (2 * w ^ 2)))) *
        (C * Real.exp (-(c * ((M : ℝ) - 2) / (2 * w ^ 2)))) :=
      mul_le_mul hmark hpin (krDens_nonneg ν hf0 _ _ _) (by positivity)
    _ = C ^ 2 * Real.exp (-(c * ((max l r : ℕ) - (2 : ℝ)) / (2 * w ^ 2)) +
        -(c * ((M : ℝ) - 2) / (2 * w ^ 2))) := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (sq_nonneg C)

end
end PGM
