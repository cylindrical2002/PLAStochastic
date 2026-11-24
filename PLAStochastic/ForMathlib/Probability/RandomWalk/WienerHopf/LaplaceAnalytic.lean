import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.RenewalSeries
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Holomorphy of the Laplace transform of an exponential density

For `IsExpDensity g D θ`, `A(ζ) = ∫ e^{ζ x} g(x) dx` is holomorphic on `{Re ζ < θ}`
(`differentiableOn_laplaceC`). The proof splits `g` into the positive and negative parts of its
real and imaginary parts and uses the holomorphy of `complexMGF` for the finite measures
`p(x) dx`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped ENNReal

namespace PGM.WienerHopf

variable {g : ℝ → ℂ} {D θ : ℝ}

theorem integral_cexp_mul_ofReal_eq_complexMGF {p : ℝ → ℝ} (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (ζ : ℂ) :
    ∫ x : ℝ, cexp (ζ * x) * (p x : ℂ) =
      complexMGF id (volume.withDensity fun x => ENNReal.ofReal (p x)) ζ := by
  have hpE : Measurable fun x => ENNReal.ofReal (p x) := ENNReal.measurable_ofReal.comp hp
  rw [complexMGF, integral_withDensity_eq_integral_toReal_smul hpE
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hp0 x), Complex.real_smul, id]
  ring

/-- The holomorphy strip of a nonnegative part. -/
theorem differentiableOn_complexMGF_part {p : ℝ → ℝ} (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x)
    (hpD : ∀ x, p x ≤ (Ioi (0 : ℝ)).indicator (fun x => D * Real.exp (-θ * x)) x) :
    DifferentiableOn ℂ (complexMGF id (volume.withDensity fun x => ENNReal.ofReal (p x)))
      {z | z.re < θ} := by
  set ν := volume.withDensity fun x => ENNReal.ofReal (p x)
  have hsub : Iio θ ⊆ integrableExpSet id ν := by
    intro t ht
    simp only [mem_Iio] at ht
    show Integrable (fun x => Real.exp (t * id x)) ν
    refine ⟨(by fun_prop : Measurable fun x : ℝ => Real.exp (t * x)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [id, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hpE : Measurable fun x => ENNReal.ofReal (p x) := ENNReal.measurable_ofReal.comp hp
    have heE : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (t * x)) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    rw [lintegral_withDensity_eq_lintegral_mul _ hpE heE]
    calc ∫⁻ x, ((fun x => ENNReal.ofReal (p x)) * fun x => ENNReal.ofReal (Real.exp (t * x))) x
        ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal (D * Real.exp ((t - θ) * x)) := by
          rw [← lintegral_indicator measurableSet_Ioi]
          refine lintegral_mono fun x => ?_
          simp only [Pi.mul_apply]
          rw [← ENNReal.ofReal_mul (hp0 x)]
          by_cases hx : x ∈ Ioi (0 : ℝ)
          · rw [indicator_of_mem hx]
            refine ENNReal.ofReal_le_ofReal ?_
            have h := hpD x
            rw [indicator_of_mem hx] at h
            calc p x * Real.exp (t * x) ≤ D * Real.exp (-θ * x) * Real.exp (t * x) :=
                  mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
              _ = D * Real.exp ((t - θ) * x) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
          · rw [indicator_of_notMem hx]
            have h := hpD x
            rw [indicator_of_notMem hx] at h
            rw [le_antisymm h (hp0 x), zero_mul, ENNReal.ofReal_zero]
      _ < ⊤ := by
          rw [← ofReal_integral_eq_lintegral_ofReal
            ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul D)]
          · exact ENNReal.ofReal_lt_top
          · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
            have h := hpD x
            rw [indicator_of_mem hx] at h
            have := (hp0 x).trans h
            have hD : 0 ≤ D := by
              by_contra hD; push Not at hD
              have := mul_neg_of_neg_of_pos hD (Real.exp_pos (-θ * x)); linarith
            positivity
  refine (differentiableOn_complexMGF (X := id) (μ := ν)).mono fun z hz => ?_
  exact interior_maximal hsub isOpen_Iio hz

/-- **`A(ζ) = ∫ e^{ζ x} g(x) dx` is holomorphic on `{Re ζ < θ}`.** -/
theorem differentiableOn_laplaceC (hg : IsExpDensity g D θ) :
    DifferentiableOn ℂ (laplaceC g) {z | z.re < θ} := by
  set p₁ : ℝ → ℝ := fun x => max (g x).re 0
  set p₂ : ℝ → ℝ := fun x => max (-(g x).re) 0
  set p₃ : ℝ → ℝ := fun x => max (g x).im 0
  set p₄ : ℝ → ℝ := fun x => max (-(g x).im) 0
  have hm : ∀ q : ℝ → ℝ, (q = p₁ ∨ q = p₂ ∨ q = p₃ ∨ q = p₄) → Measurable q := by
    rintro q (rfl | rfl | rfl | rfl)
    · exact (Complex.measurable_re.comp hg.measurable).max measurable_const
    · exact (Complex.measurable_re.comp hg.measurable).neg.max measurable_const
    · exact (Complex.measurable_im.comp hg.measurable).max measurable_const
    · exact (Complex.measurable_im.comp hg.measurable).neg.max measurable_const
  have hb : ∀ q : ℝ → ℝ, (q = p₁ ∨ q = p₂ ∨ q = p₃ ∨ q = p₄) →
      ∀ x, q x ≤ (Ioi (0 : ℝ)).indicator (fun x => D * Real.exp (-θ * x)) x := by
    rintro q hq x
    have hnorm : q x ≤ ‖g x‖ := by
      rcases hq with rfl | rfl | rfl | rfl
      · exact max_le ((Complex.re_le_norm _).trans le_rfl) (norm_nonneg _)
      · exact max_le ((neg_le_abs _).trans (Complex.abs_re_le_norm _)) (norm_nonneg _)
      · exact max_le ((Complex.im_le_norm _).trans le_rfl) (norm_nonneg _)
      · exact max_le ((neg_le_abs _).trans (Complex.abs_im_le_norm _)) (norm_nonneg _)
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hx]; exact hnorm.trans (hg.norm_le x)
    · rw [indicator_of_notMem hx, ← norm_zero (E := ℂ), ← hg.eq_zero_of_nonpos x (not_lt.mp hx)]
      exact hnorm
  have h0 : ∀ q : ℝ → ℝ, (q = p₁ ∨ q = p₂ ∨ q = p₃ ∨ q = p₄) → ∀ x, 0 ≤ q x := by
    rintro q (rfl | rfl | rfl | rfl) x <;> exact le_max_right _ _
  have hdiff : ∀ q : ℝ → ℝ, (q = p₁ ∨ q = p₂ ∨ q = p₃ ∨ q = p₄) →
      DifferentiableOn ℂ (fun ζ => ∫ x : ℝ, cexp (ζ * x) * (q x : ℂ)) {z | z.re < θ} := by
    intro q hq
    simp_rw [integral_cexp_mul_ofReal_eq_complexMGF (hm q hq) (h0 q hq)]
    exact differentiableOn_complexMGF_part (hm q hq) (h0 q hq) (hb q hq)
  have hint : ∀ q : ℝ → ℝ, (q = p₁ ∨ q = p₂ ∨ q = p₃ ∨ q = p₄) → ∀ ζ : ℂ, ζ.re < θ →
      Integrable fun x : ℝ => cexp (ζ * x) * (q x : ℂ) := by
    intro q hq ζ hζ
    have hI : IntegrableOn (fun x : ℝ => D * Real.exp ((ζ.re - θ) * x)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (a := ζ.re - θ) (by linarith) 0).const_mul D
    refine (hI.integrable_indicator measurableSet_Ioi).mono'
      (((by fun_prop : Measurable fun x : ℝ => cexp (ζ * x)).mul
        (Complex.measurable_ofReal.comp (hm q hq))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_cexp_mul_ofReal', Complex.norm_real, Real.norm_of_nonneg (h0 q hq x)]
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hx]
      have h := hb q hq x
      rw [indicator_of_mem hx] at h
      calc Real.exp (-(-ζ.re) * x) * q x ≤ Real.exp (-(-ζ.re) * x) * (D * Real.exp (-θ * x)) :=
            mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
        _ = D * Real.exp ((ζ.re - θ) * x) := by rw [mul_comm, mul_assoc, ← Real.exp_add]; ring_nf
    · rw [indicator_of_notMem hx]
      have h := hb q hq x
      rw [indicator_of_notMem hx] at h
      rw [le_antisymm h (h0 q hq x), mul_zero]
  have hdecomp : ∀ ζ : ℂ, ζ.re < θ → laplaceC g ζ =
      ((∫ x : ℝ, cexp (ζ * x) * (p₁ x : ℂ)) - ∫ x : ℝ, cexp (ζ * x) * (p₂ x : ℂ)) +
        I * ((∫ x : ℝ, cexp (ζ * x) * (p₃ x : ℂ)) - ∫ x : ℝ, cexp (ζ * x) * (p₄ x : ℂ)) := by
    intro ζ hζ
    have h1 := hint p₁ (Or.inl rfl) ζ hζ
    have h2 := hint p₂ (Or.inr (Or.inl rfl)) ζ hζ
    have h3 := hint p₃ (Or.inr (Or.inr (Or.inl rfl))) ζ hζ
    have h4 := hint p₄ (Or.inr (Or.inr (Or.inr rfl))) ζ hζ
    have h12 : Integrable fun x : ℝ => cexp (ζ * x) * (p₁ x : ℂ) - cexp (ζ * x) * (p₂ x : ℂ) :=
      h1.sub h2
    have h34 : Integrable fun x : ℝ =>
        I * (cexp (ζ * x) * (p₃ x : ℂ) - cexp (ζ * x) * (p₄ x : ℂ)) := (h3.sub h4).const_mul I
    rw [← integral_sub h1 h2, ← integral_sub h3 h4, ← integral_const_mul, ← integral_add h12 h34]
    unfold laplaceC
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hre : ((p₁ x - p₂ x : ℝ) : ℂ) = ((g x).re : ℂ) := by
      congr 1; simp only [p₁, p₂]
      rcases le_total (g x).re 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    have him : ((p₃ x - p₄ x : ℝ) : ℂ) = ((g x).im : ℂ) := by
      congr 1; simp only [p₃, p₄]
      rcases le_total (g x).im 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    have hg_eq : g x = ((g x).re : ℂ) + ((g x).im : ℂ) * I := (Complex.re_add_im (g x)).symm
    push_cast at hre him
    show cexp (ζ * x) * g x = _
    rw [hg_eq, ← hre, ← him]
    ring
  have hd := (((hdiff p₁ (Or.inl rfl)).sub (hdiff p₂ (Or.inr (Or.inl rfl)))).add
    (((hdiff p₃ (Or.inr (Or.inr (Or.inl rfl)))).sub
      (hdiff p₄ (Or.inr (Or.inr (Or.inr rfl))))).const_mul I))
  exact hd.congr fun ζ hζ => hdecomp ζ hζ

end PGM.WienerHopf
