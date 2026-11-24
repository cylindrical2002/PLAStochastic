import PLAStochastic.Index.GEP.StrongApprox.Tilt.CenteredTilt
import PLAStochastic.Index.GEP.StrongApprox.LocalCLT.DensityComponent

/-! # Uniform density components and Cramer gaps under exponential tilting -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Truncation loses at most the ambient tail mass, and scalar domination transfers the part. -/
theorem SmoothPart.weighted_restrict {D c q : ℝ} {ν ρ : ProbabilityMeasure ℝ}
    (hs : SmoothPart D c ν) (hc : 0 ≤ c) (hq : 0 ≤ q) {A : Set ℝ}
    (hA : MeasurableSet A) (htail : (ν : Measure ℝ) Aᶜ ≤ ENNReal.ofReal (c / 2))
    (hdom : ENNReal.ofReal q • (ν : Measure ℝ).restrict A ≤ (ρ : Measure ℝ)) :
    SmoothPart (q * D) (q * (c / 2)) ρ := by
  obtain ⟨f, hfm, hf0, hfD, hmass, hν⟩ := hs.part
  let η : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hην : η ≤ (ν : Measure ℝ) := hν
  have hm : ENNReal.ofReal c ≤ η univ := by simpa [η, withDensity_apply] using hmass
  have htailη : η Aᶜ ≤ ENNReal.ofReal (c / 2) := (hην _).trans htail
  have hmA : ENNReal.ofReal (c / 2) ≤ η A := by
    apply (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp
    calc
      ENNReal.ofReal (c / 2) + ENNReal.ofReal (c / 2) = ENNReal.ofReal c := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ η univ := hm
      _ = η A + η Aᶜ := (measure_add_measure_compl hA).symm
      _ ≤ η A + ENNReal.ofReal (c / 2) := add_le_add le_rfl htailη
  let g : ℝ → ℝ := fun x => q * A.indicator f x
  have hgm : Measurable g := (hfm.indicator hA).const_mul q
  have hg0 : ∀ x, 0 ≤ g x := fun x => mul_nonneg hq (indicator_nonneg (fun x _ => hf0 x) x)
  have hgeq : volume.withDensity (fun x => ENNReal.ofReal (g x)) =
      ENNReal.ofReal q • η.restrict A := by
    have he : (fun x => ENNReal.ofReal (g x)) =
        ENNReal.ofReal q • (A.indicator (fun x => ENNReal.ofReal (f x))) := by
      funext x
      by_cases hx : x ∈ A <;> simp [g, hx, ENNReal.ofReal_mul hq]
    rw [he, withDensity_smul _ (hfm.ennreal_ofReal.indicator hA), withDensity_indicator hA,
      ← restrict_withDensity hA]
  refine ⟨g, hgm, hg0, ?_, ?_, ?_⟩
  · intro x
    apply mul_le_mul_of_nonneg_left _ hq
    by_cases hx : x ∈ A
    · simpa [hx] using hfD x
    · simp only [indicator_of_notMem hx]
      exact (hf0 x).trans (hfD x)
  · have hm' : ENNReal.ofReal q * ENNReal.ofReal (c / 2) ≤ ENNReal.ofReal q * η A := by
      gcongr
    rw [← ENNReal.ofReal_mul hq] at hm'
    have hgmass : (∫⁻ x, ENNReal.ofReal (g x)) = ENNReal.ofReal q * η A := by
      simpa [withDensity_apply] using congrArg (fun m : Measure ℝ => m univ) hgeq
    exact hgmass ▸ hm'
  · rw [hgeq]
    exact (_root_.smul_le_smul_left _ (Measure.restrict_mono_measure hην A)).trans hdom

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

/-- Positivity and mean one give a universal first absolute centered moment. -/
theorem UnivClass.integral_abs_sub_one_le_two (h : UnivClass vlo vhi κ₃ B θ ν) :
    (∫ x : ℝ, |x - 1| ∂(ν : Measure ℝ)) ≤ 2 := by
  have hx : Integrable (fun x : ℝ => x) (ν : Measure ℝ) := h.memLp3.integrable (by norm_num)
  calc
    (∫ x : ℝ, |x - 1| ∂(ν : Measure ℝ)) ≤ ∫ x : ℝ, x + 1 ∂(ν : Measure ℝ) := by
      apply integral_mono_ae ((hx.sub (integrable_const 1)).abs) (hx.add (integrable_const 1))
      filter_upwards [h.ae_pos] with x hx0
      change |x - 1| ≤ x + 1
      rw [abs_le]
      constructor <;> linarith
    _ = 2 := by
      rw [integral_add hx (integrable_const 1)]
      change lawMean ν + _ = 2
      norm_num [h.mean]

/-- A class-uniform compact interval retains all but half of the designated smooth mass. -/
theorem UnivClass.centered_tail_le (h : UnivClass vlo vhi κ₃ B θ ν) {c : ℝ} (hc : 0 < c) :
    (ν : Measure ℝ) {x : ℝ | |x - 1| ≤ 4 / c}ᶜ ≤ ENNReal.ofReal (c / 2) := by
  have hx : Integrable (fun x : ℝ => x) (ν : Measure ℝ) := h.memLp3.integrable (by norm_num)
  have hi := (hx.sub (integrable_const 1)).abs
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => abs_nonneg (x - 1)) hi (4 / c)
  have ht : (ν : Measure ℝ).real {x : ℝ | 4 / c ≤ |x - 1|} ≤ c / 2 := by
    have hb := hm.trans h.integral_abs_sub_one_le_two
    have hR : 0 < (4 : ℝ) / c := by positivity
    rw [mul_comm] at hb
    have hb' := (le_div_iff₀ hR).2 hb
    calc
      _ ≤ 2 / (4 / c) := hb'
      _ = c / 2 := by field_simp; norm_num
  have hs : {x : ℝ | |x - 1| ≤ 4 / c}ᶜ ⊆ {x : ℝ | 4 / c ≤ |x - 1|} := by
    intro x hx0
    change ¬ |x - 1| ≤ 4 / c at hx0
    exact (lt_of_not_ge hx0).le
  apply (measure_mono hs).trans
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal ht

/-- The normalizer has the same class-uniform upper bound as the centered exponential moment. -/
theorem UnivClass.integral_exp_centered_le (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| ≤ θ) :
    (∫ x : ℝ, Real.exp (lam * (x - 1)) ∂(ν : Measure ℝ)) ≤ Real.exp θ * B := by
  have hθ : 0 ≤ θ := (abs_nonneg lam).trans hlam
  have hl : (∫⁻ x, ENNReal.ofReal (Real.exp (lam * (x - 1))) ∂(ν : Measure ℝ)) ≤
      ENNReal.ofReal (Real.exp θ * B) := by
    apply le_trans (lintegral_mono (fun x => ?_)) (h.lintegral_exp_abs_sub_one_le hθ le_rfl)
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    calc lam * (x - 1) ≤ |lam| * |x - 1| := by simpa only [abs_mul] using le_abs_self (lam * (x - 1))
      _ ≤ θ * |x - 1| := mul_le_mul_of_nonneg_right hlam (abs_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable_exp_centered hlam)
    (ae_of_all _ fun x => Real.exp_nonneg _)] at hl
  rcases ENNReal.ofReal_le_ofReal_iff'.mp hl with hle | hle
  · exact hle
  · have hge := h.one_le_integral_exp_centered hlam
    linarith

/-- Uniform weight assigned to a compact part of every half-range tilt. -/
def tiltComponentFactor (θ B c : ℝ) : ℝ :=
  Real.exp (-(θ / 2) * (4 / c)) / (Real.exp θ * B)

/-- A uniformly positive bounded density part survives every half-range tilt. -/
theorem UnivClass.centeredTilt_smoothPart {D c : ℝ}
    (h : UnivClass vlo vhi κ₃ B θ ν) (hs : SmoothPart D c ν)
    (hθ : 0 < θ) (hc : 0 < c) {lam : ℝ} (hlam : |lam| ≤ θ / 2)
    {ρ : ProbabilityMeasure ℝ} (hρ : (ρ : Measure ℝ) = centeredTilt ν lam) :
    SmoothPart (tiltComponentFactor θ B c * D)
      (tiltComponentFactor θ B c * (c / 2)) ρ := by
  have hl : |lam| ≤ θ := hlam.trans (by linarith)
  have hM := h.one_le_integral_exp_centered hl
  have hMu := h.integral_exp_centered_le hl
  have hE : 0 < Real.exp θ * B := by linarith
  have hq : 0 < tiltComponentFactor θ B c := div_pos (Real.exp_pos _) hE
  let A : Set ℝ := {x : ℝ | |x - 1| ≤ 4 / c}
  have hA : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  apply hs.weighted_restrict hc.le hq.le hA (h.centered_tail_le hc)
  rw [hρ]
  let w : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (lam * (x - 1)) /
    (∫ z : ℝ, Real.exp (lam * (z - 1)) ∂(ν : Measure ℝ)))
  change ENNReal.ofReal (tiltComponentFactor θ B c) • (ν : Measure ℝ).restrict A ≤
    (ν : Measure ℝ).withDensity w
  calc
    ENNReal.ofReal (tiltComponentFactor θ B c) • (ν : Measure ℝ).restrict A =
        (ν : Measure ℝ).withDensity (A.indicator (fun _ => ENNReal.ofReal (tiltComponentFactor θ B c))) := by
      rw [withDensity_indicator hA, withDensity_const]
    _ ≤ (ν : Measure ℝ).withDensity w := by
      apply withDensity_mono
      apply ae_of_all
      intro x
      by_cases hx : x ∈ A
      · rw [indicator_of_mem hx]
        apply ENNReal.ofReal_le_ofReal
        have hx' : |x - 1| ≤ 4 / c := hx
        have hex : Real.exp (-(θ / 2) * (4 / c)) ≤ Real.exp (lam * (x - 1)) := by
          apply Real.exp_le_exp.mpr
          have habs : |lam * (x - 1)| ≤ θ / 2 * (4 / c) := by
            rw [abs_mul]
            exact mul_le_mul hlam hx' (abs_nonneg _) (by positivity)
          linarith [neg_abs_le (lam * (x - 1))]
        exact (div_le_div_of_nonneg_left (Real.exp_nonneg _) (by linarith) hMu).trans
          (div_le_div_of_nonneg_right hex (by linarith))
      · simp only [indicator_of_notMem hx]
        exact zero_le

/-- A raw second-moment bound independent of the input law and tilt. -/
def tiltRawSecondBound (θ B : ℝ) : ℝ := 2 * ((8 / θ ^ 2) * (Real.exp θ * B)) + 2

theorem UnivClass.centeredTilt_raw_second (h : UnivClass vlo vhi κ₃ B θ ν)
    (hθ : 0 < θ) {lam : ℝ} (hlam : |lam| ≤ θ / 2)
    {ρ : ProbabilityMeasure ℝ} (hρ : (ρ : Measure ℝ) = centeredTilt ν lam) :
    MemLp id 2 (ρ : Measure ℝ) ∧
      (∫ x : ℝ, x ^ 2 ∂(ρ : Measure ℝ)) ≤ tiltRawSecondBound θ B := by
  have hc := h.centeredTilt_second_moment hθ hlam
  rw [← hρ] at hc
  have hm : MemLp (fun x : ℝ => x - 1) 2 (ρ : Measure ℝ) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr hc.1
  have hr : MemLp id 2 (ρ : Measure ℝ) := by
    convert hm.add (memLp_const 1) using 1
    ext x
    exact (sub_add_cancel x 1).symm
  refine ⟨hr, ?_⟩
  calc
    (∫ x : ℝ, x ^ 2 ∂(ρ : Measure ℝ)) ≤ ∫ x : ℝ, 2 * (x - 1) ^ 2 + 2 ∂(ρ : Measure ℝ) := by
      apply integral_mono hr.integrable_sq ((hc.1.const_mul 2).add (integrable_const 2))
      intro x
      change x ^ 2 ≤ 2 * (x - 1) ^ 2 + 2
      nlinarith [sq_nonneg (x - 2)]
    _ = 2 * (∫ x : ℝ, (x - 1) ^ 2 ∂(ρ : Measure ℝ)) + 2 := by
      rw [integral_add (hc.1.const_mul 2) (integrable_const 2), integral_const_mul]
      simp
    _ ≤ tiltRawSecondBound θ B := by unfold tiltRawSecondBound; linarith [hc.2]

/-- The tilted Cramer gap is uniform in the law and tilt throughout a half-range interval. -/
theorem UnivClass.centeredTilt_cramer {D c t₀ : ℝ}
    (h : UnivClass vlo vhi κ₃ B θ ν) (hs : SmoothPart D c ν)
    (hθ : 0 < θ) (hc : 0 < c) (ht₀ : 0 < t₀) {lam : ℝ} (hlam : |lam| ≤ θ / 2)
    {ρ : ProbabilityMeasure ℝ} (hρ : (ρ : Measure ℝ) = centeredTilt ν lam) :
    let q := tiltComponentFactor θ B c
    0 < smoothPartCramerGap (q * D) (q * (c / 2)) (tiltRawSecondBound θ B) t₀ ∧
      ∀ t : ℝ, t₀ ≤ |t| → ‖charFun (ρ : Measure ℝ) t‖ ≤
        1 - smoothPartCramerGap (q * D) (q * (c / 2)) (tiltRawSecondBound θ B) t₀ := by
  dsimp only
  have hl : |lam| ≤ θ := hlam.trans (by linarith)
  have hM := h.one_le_integral_exp_centered hl
  have hMu := h.integral_exp_centered_le hl
  have hE : 0 < Real.exp θ * B := by linarith
  have hq : 0 < tiltComponentFactor θ B c := div_pos (Real.exp_pos _) hE
  have hcp : 0 < tiltComponentFactor θ B c * (c / 2) := by positivity
  have hC : 0 < tiltRawSecondBound θ B := by unfold tiltRawSecondBound; positivity
  have hs' := h.centeredTilt_smoothPart hs hθ hc hlam hρ
  obtain ⟨h2, h2bound⟩ := h.centeredTilt_raw_second hθ hlam hρ
  refine ⟨PGM.smoothPartCramerGap_pos (mul_pos hq (hs.D_pos hc)) hcp hC ht₀, ?_⟩
  intro t ht
  exact hs'.norm_charFun_le_uniform hcp h2 h2bound ht₀ ht

/-- Class-level packaging: the same positive constants work for every law and every tilt. -/
theorem exists_uniform_centeredTilt_class (vlo vhi κ₃ B θ D c t₀ : ℝ)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) (ht₀ : 0 < t₀) :
    ∃ D' c' C' δ : ℝ, 0 < D' ∧ 0 < c' ∧ 0 < C' ∧ 0 < δ ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
        ∀ lam : ℝ, |lam| ≤ θ / 2 →
          ∃ ρ : ProbabilityMeasure ℝ, (ρ : Measure ℝ) = centeredTilt ν lam ∧
            SmoothPart D' c' ρ ∧ MemLp id 2 (ρ : Measure ℝ) ∧
            (∫ x : ℝ, x ^ 2 ∂(ρ : Measure ℝ)) ≤ C' ∧
            ∀ t : ℝ, t₀ ≤ |t| → ‖charFun (ρ : Measure ℝ) t‖ ≤ 1 - δ := by
  let q := tiltComponentFactor θ B c
  have hq : 0 < q := div_pos (Real.exp_pos _) (mul_pos (Real.exp_pos _) hB)
  have hc' : 0 < q * (c / 2) := by positivity
  have hC : 0 < tiltRawSecondBound θ B := by unfold tiltRawSecondBound; positivity
  refine ⟨q * D, q * (c / 2), tiltRawSecondBound θ B,
    smoothPartCramerGap (q * D) (q * (c / 2)) (tiltRawSecondBound θ B) t₀,
    mul_pos hq hD, hc', hC, smoothPartCramerGap_pos (mul_pos hq hD) hc' hC ht₀, ?_⟩
  intro ν hν hs lam hlam
  have hl : |lam| ≤ θ := hlam.trans (by linarith)
  let ρ : ProbabilityMeasure ℝ := ⟨centeredTilt ν lam, hν.isProbabilityMeasure_centeredTilt hl⟩
  obtain ⟨h2, h2bound⟩ := hν.centeredTilt_raw_second hθ hlam (ρ := ρ) rfl
  refine ⟨ρ, rfl, hν.centeredTilt_smoothPart hs hθ hc hlam rfl, h2, h2bound, ?_⟩
  exact (hν.centeredTilt_cramer hs hθ hc ht₀ hlam rfl).2

end

end PGM
