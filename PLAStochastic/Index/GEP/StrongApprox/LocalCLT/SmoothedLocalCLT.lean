import PLAStochastic.Index.GEP.StrongApprox.LocalCLT.IntegratedLowFrequency
import PLAStochastic.Index.GEP.StrongApprox.LocalCLT.HighFrequency

/-! # A Fourier local central limit bound for Gaussian-smoothed sums -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal

/-- Gaussian smoothing factors out of the error when the target variance is also smoothed. -/
theorem norm_smoothed_fourier_error (z : ℂ) (t σ h : ℝ) :
    ‖z * (Real.exp (-(h ^ 2 * t ^ 2 / 2)) : ℂ) -
      (Real.exp (-(t ^ 2 * (σ ^ 2 + h ^ 2) / 2)) : ℂ)‖ =
    ‖z - (Real.exp (-(t ^ 2 * σ ^ 2 / 2)) : ℂ)‖ *
      Real.exp (-(h ^ 2 * t ^ 2 / 2)) := by
  have he : Real.exp (-(t ^ 2 * (σ ^ 2 + h ^ 2) / 2)) =
      Real.exp (-(t ^ 2 * σ ^ 2 / 2)) * Real.exp (-(h ^ 2 * t ^ 2 / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, Complex.ofReal_mul, ← sub_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The Gaussian tail envelope is integrable. -/
theorem integrable_abs_gaussian {v : ℝ} (hv : 0 < v) :
    Integrable (fun t : ℝ => |t| * Real.exp (-(t ^ 2 * v / 2))) := by
  have hi := integrable_rpow_mul_exp_neg_mul_sq (show 0 < v / 2 by positivity)
    (show (-1 : ℝ) < (1 : ℝ) by norm_num)
  convert hi.norm using 1
  funext t
  rw [Real.rpow_one, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  congr 2
  ring

/-- A first-moment envelope gives an explicit Gaussian Fourier tail bound. -/
theorem integral_gaussian_tail_le {v R : ℝ} (hv : 0 < v) (hR : 0 < R) :
    (∫ t : ℝ in {t : ℝ | R ≤ |t|}, Real.exp (-(t ^ 2 * v / 2))) ≤
      (∫ t : ℝ, |t| * Real.exp (-(t ^ 2 * v / 2))) / R := by
  have hg : Integrable (fun t : ℝ => Real.exp (-(t ^ 2 * v / 2))) := by
    convert integrable_exp_neg_mul_sq (show 0 < v / 2 by positivity) using 1
    funext t
    congr 1
    ring
  have hf := (integrable_abs_gaussian hv).div_const R
  have hA : MeasurableSet {t : ℝ | R ≤ |t|} := measurableSet_le measurable_const (by fun_prop)
  calc
    _ ≤ ∫ t : ℝ in {t : ℝ | R ≤ |t|},
        (|t| * Real.exp (-(t ^ 2 * v / 2))) / R := by
      apply integral_mono_ae hg.integrableOn hf.integrableOn
      filter_upwards [ae_restrict_mem hA] with t ht
      rw [le_div_iff₀ hR]
      nlinarith [Real.exp_pos (-(t ^ 2 * v / 2))]
    _ ≤ ∫ t : ℝ, (|t| * Real.exp (-(t ^ 2 * v / 2))) / R :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun t => by positivity) hf
    _ = _ := integral_div R _

/-- Rescaled, smoothed characteristic powers are integrable. -/
theorem integrable_normalized_smoothed_charFun_power (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {h : ℝ} (hh : 0 < h) (l : ℕ) :
    Integrable (fun t : ℝ => ‖charFun μ (t / Real.sqrt l)‖ ^ l *
      Real.exp (-(h ^ 2 * t ^ 2 / 2))) := by
  let : IsProbabilityMeasure (μ.map ((Real.sqrt l)⁻¹ * ·)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hi := integrable_smoothed_charFun_power (μ.map ((Real.sqrt l)⁻¹ * ·)) hh l
  simp_rw [charFun_map_mul] at hi
  simpa only [div_eq_mul_inv, mul_comm] using hi

/-- The normalized smoothed Fourier error is absolutely integrable. -/
theorem integrable_normalized_smoothed_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ) (l : ℕ) :
    Integrable (fun t : ℝ => ‖charFun μ (t / Real.sqrt l) ^ l *
      (Real.exp (-(h ^ 2 * t ^ 2 / 2)) : ℂ) -
      (Real.exp (-(t ^ 2 * (σ ^ 2 + h ^ 2) / 2)) : ℂ)‖) := by
  have hi := integrable_normalized_smoothed_charFun_power μ hh l
  have hg : Integrable (fun t : ℝ => Real.exp (-(t ^ 2 * (σ ^ 2 + h ^ 2) / 2))) := by
    convert integrable_exp_neg_mul_sq (show 0 < (σ ^ 2 + h ^ 2) / 2 by positivity) using 1
    funext t
    congr 1
    ring
  refine (hi.add hg).mono' (by fun_prop) (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  change _ ≤ ‖charFun μ (t / Real.sqrt l)‖ ^ l *
    Real.exp (-(h ^ 2 * t ^ 2 / 2)) + Real.exp (-(t ^ 2 * (σ ^ 2 + h ^ 2) / 2))
  have hb := norm_sub_le (charFun μ (t / Real.sqrt l) ^ l *
      (Real.exp (-(h ^ 2 * t ^ 2 / 2)) : ℂ))
      (Real.exp (-(t ^ 2 * (σ ^ 2 + h ^ 2) / 2)) : ℂ)
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using hb

/-- The smoothed high-frequency estimate is valid after normalization, with no Jacobian loss. -/
theorem integral_normalized_highFrequency_smoothed_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {δ κ h : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hh : 0 < h)
    (hgap : ∀ t : ℝ, δ ≤ |t| → ‖charFun μ t‖ ≤ 1 - κ)
    {l : ℕ} (hl : 1 ≤ l) (hscale : 1 / h ≤ (l : ℝ) ^ 8) :
    (∫ t : ℝ in {t : ℝ | δ * Real.sqrt l ≤ |t|},
      ‖charFun μ (t / Real.sqrt l)‖ ^ l * Real.exp (-(h ^ 2 * t ^ 2 / 2))) ≤
        (Real.sqrt (2 * Real.pi) * (Nat.factorial 9 : ℝ) / κ ^ 9) / l := by
  have hr : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hl)
  let : IsProbabilityMeasure (μ.map ((Real.sqrt l)⁻¹ * ·)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hgap' : ∀ t : ℝ, δ * Real.sqrt l ≤ |t| →
      ‖charFun (μ.map ((Real.sqrt l)⁻¹ * ·)) t‖ ≤ 1 - κ := by
    intro t ht
    rw [charFun_map_mul]
    apply hgap
    rw [abs_mul, abs_inv, abs_of_pos hr, ← div_eq_inv_mul, le_div_iff₀ hr]
    exact ht
  have hi := integral_highFrequency_smoothed_le_inv_length hκ hκ1 hh hgap' hl hscale
  simp_rw [charFun_map_mul] at hi
  simpa only [div_eq_mul_inv, mul_comm] using hi

/-- Triangle domination retains only the original Gaussian in the tail estimate. -/
theorem norm_smoothed_fourier_error_le (z : ℂ) (t σ h : ℝ) :
    ‖z * (Real.exp (-(h ^ 2 * t ^ 2 / 2)) : ℂ) -
      (Real.exp (-(t ^ 2 * (σ ^ 2 + h ^ 2) / 2)) : ℂ)‖ ≤
      ‖z‖ * Real.exp (-(h ^ 2 * t ^ 2 / 2)) + Real.exp (-(t ^ 2 * σ ^ 2 / 2)) := by
  rw [norm_smoothed_fourier_error]
  have hd : Real.exp (-(h ^ 2 * t ^ 2 / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hn := norm_sub_le z (Real.exp (-(t ^ 2 * σ ^ 2 / 2)) : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
  calc
    _ ≤ (‖z‖ + Real.exp (-(t ^ 2 * σ ^ 2 / 2))) * Real.exp (-(h ^ 2 * t ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _)
    _ ≤ _ := by nlinarith [Real.exp_pos (-(t ^ 2 * σ ^ 2 / 2))]

/-- The complete Fourier local CLT: all frequencies, an actual Cramer gap, and Gaussian smoothing. -/
theorem integral_smoothed_fourier_error_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {σ β κ h : ℝ} (h3 : MemLp id 3 μ) (hm : ∫ x : ℝ, x ∂μ = 0)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) (hβ : 1 ≤ β)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ β * σ ^ 3)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hgap : ∀ t : ℝ, 1 / (β * σ) ≤ |t| → ‖charFun μ t‖ ≤ 1 - κ)
    (hh : 0 < h) {l : ℕ} (hl : 2 ≤ l) (hscale : 1 / h ≤ (l : ℝ) ^ 8) :
    (∫ t : ℝ, ‖charFun μ (t / Real.sqrt l) ^ l *
      (Real.exp (-(h ^ 2 * t ^ 2 / 2)) : ℂ) -
      (Real.exp (-(t ^ 2 * (σ ^ 2 + h ^ 2) / 2)) : ℂ)‖) ≤
      (saLowFrequencyConstant σ β + β * σ *
        (∫ t : ℝ, |t| * Real.exp (-(t ^ 2 * σ ^ 2 / 2)))) / Real.sqrt l +
      (Real.sqrt (2 * Real.pi) * (Nat.factorial 9 : ℝ) / κ ^ 9) / l := by
  let R := Real.sqrt (l : ℝ) / (β * σ)
  let S := Icc (-R) R
  let A := {t : ℝ | R ≤ |t|}
  let f := fun t : ℝ => ‖charFun μ (t / Real.sqrt l) ^ l *
    (Real.exp (-(h ^ 2 * t ^ 2 / 2)) : ℂ) -
    (Real.exp (-(t ^ 2 * (σ ^ 2 + h ^ 2) / 2)) : ℂ)‖
  let g := fun t : ℝ => ‖charFun μ (t / Real.sqrt l)‖ ^ l *
    Real.exp (-(h ^ 2 * t ^ 2 / 2))
  let G := fun t : ℝ => Real.exp (-(t ^ 2 * σ ^ 2 / 2))
  have hr : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < l by omega))
  have hb : 0 < β * σ := mul_pos (lt_of_lt_of_le zero_lt_one hβ) hσ
  have hR : 0 < R := div_pos hr hb
  have hf : Integrable f := integrable_normalized_smoothed_error μ hh hσ l
  have hg : Integrable g := integrable_normalized_smoothed_charFun_power μ hh l
  have hG : Integrable G := by
    dsimp [G]
    convert integrable_exp_neg_mul_sq (show 0 < σ ^ 2 / 2 by positivity) using 1
    funext t
    congr 1
    ring
  have hlow : (∫ t in S, f t) ≤ saLowFrequencyConstant σ β / Real.sqrt l := by
    apply le_trans _ (integral_lowFrequency_error_le h3 hm hvar hσ hβ hthird hl)
    have hc : Continuous (fun t : ℝ =>
      ‖charFun μ (t / Real.sqrt l) ^ l - (Real.exp (-(t ^ 2 * σ ^ 2 / 2)) : ℂ)‖) := by fun_prop
    apply integral_mono_ae hf.integrableOn hc.integrableOn_Icc
    filter_upwards [] with t
    dsimp [f]
    rw [norm_smoothed_fourier_error]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
  have hsub : Sᶜ ⊆ A := by
    intro t ht
    by_contra htA
    exact ht (abs_le.mp (le_of_lt (lt_of_not_ge htA)))
  have hhigh : (∫ t in Sᶜ, f t) ≤
      (Real.sqrt (2 * Real.pi) * (Nat.factorial 9 : ℝ) / κ ^ 9) / l +
        (∫ t : ℝ, |t| * G t) / R := by
    calc
      _ ≤ ∫ t in Sᶜ, g t + G t := by
        apply integral_mono_ae hf.integrableOn (hg.add hG).integrableOn
        filter_upwards [] with t
        change f t ≤ g t + G t
        simpa only [f, g, G, norm_pow] using
          norm_smoothed_fourier_error_le (charFun μ (t / Real.sqrt l) ^ l) t σ h
      _ ≤ ∫ t in A, g t + G t := integral_mono_measure
        (Measure.restrict_mono_set volume hsub) (ae_of_all _ fun t => by dsimp [g, G]; positivity)
        (hg.add hG).integrableOn
      _ = (∫ t in A, g t) + ∫ t in A, G t := integral_add hg.integrableOn hG.integrableOn
      _ ≤ _ := by
        apply add_le_add
        · have hi := integral_normalized_highFrequency_smoothed_le hκ hκ1 hh hgap
            (show 1 ≤ l by omega) hscale
          simpa only [A, R, g, one_div, div_eq_mul_inv, mul_comm, mul_one] using hi
        · exact integral_gaussian_tail_le (sq_pos_of_pos hσ) hR
  have he : (∫ t : ℝ, |t| * G t) / R =
      (β * σ * ∫ t : ℝ, |t| * G t) / Real.sqrt l := by
    dsimp [R]
    rw [div_div_eq_mul_div]
    ring
  rw [he] at hhigh
  have hs : MeasurableSet S := measurableSet_Icc
  have hadd := add_le_add hlow hhigh
  rw [integral_add_compl hs hf] at hadd
  change (∫ t, f t) ≤ _
  dsimp [G] at hadd
  rw [add_div]
  linarith

/-- One explicit Fourier local-CLT constant for a whole variance and moment class. -/
def saFourierCLTConstant (vlo vhi β κ : ℝ) : ℝ :=
  β * Real.sqrt vhi ^ 3 * (∫ t : ℝ, |t| ^ 3 * Real.exp (-(t ^ 2 * vlo / 6))) +
  β * Real.sqrt vhi * (∫ t : ℝ, |t| * Real.exp (-(t ^ 2 * vlo / 2))) +
  Real.sqrt (2 * Real.pi) * (Nat.factorial 9 : ℝ) / κ ^ 9

theorem saFourierCLTConstant_pos {vlo vhi β κ : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) :
    0 < saFourierCLTConstant vlo vhi β κ := by
  unfold saFourierCLTConstant
  have hc : 0 ≤ ∫ t : ℝ, |t| ^ 3 * Real.exp (-(t ^ 2 * vlo / 6)) :=
    integral_nonneg fun t => by positivity
  have ha : 0 ≤ ∫ t : ℝ, |t| * Real.exp (-(t ^ 2 * vlo / 2)) :=
    integral_nonneg fun t => by positivity
  positivity

/-- The all-frequency bound has a constant independent of the law and the smoothing width. -/
theorem integral_smoothed_fourier_error_le_uniform {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {σ β κ h vlo vhi : ℝ} (h3 : MemLp id 3 μ) (hm : ∫ x : ℝ, x ∂μ = 0)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) (hβ : 1 ≤ β)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ β * σ ^ 3)
    (hvlo : 0 < vlo) (hlo : vlo ≤ σ ^ 2) (hhi : σ ^ 2 ≤ vhi)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hgap : ∀ t : ℝ, 1 / (β * σ) ≤ |t| → ‖charFun μ t‖ ≤ 1 - κ)
    (hh : 0 < h) {l : ℕ} (hl : 2 ≤ l) (hscale : 1 / h ≤ (l : ℝ) ^ 8) :
    (∫ t : ℝ, ‖charFun μ (t / Real.sqrt l) ^ l *
      (Real.exp (-(h ^ 2 * t ^ 2 / 2)) : ℂ) -
      (Real.exp (-(t ^ 2 * (σ ^ 2 + h ^ 2) / 2)) : ℂ)‖) ≤
      saFourierCLTConstant vlo vhi β κ / Real.sqrt l := by
  apply (integral_smoothed_fourier_error_le h3 hm hvar hσ hβ hthird hκ hκ1 hgap hh hl hscale).trans
  have hβ0 : 0 ≤ β := (by norm_num : (0 : ℝ) ≤ 1).trans hβ
  have hs : σ ≤ Real.sqrt vhi := (Real.le_sqrt hσ.le ((sq_nonneg σ).trans hhi)).mpr hhi
  have hc : (∫ t : ℝ, |t| ^ 3 * Real.exp (-(t ^ 2 * σ ^ 2 / 6))) ≤
      ∫ t : ℝ, |t| ^ 3 * Real.exp (-(t ^ 2 * vlo / 6)) := by
    apply integral_mono (integrable_cubic_gaussian (sq_pos_of_pos hσ)) (integrable_cubic_gaussian hvlo)
    intro t
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlo (sq_nonneg t)]
  have ha : (∫ t : ℝ, |t| * Real.exp (-(t ^ 2 * σ ^ 2 / 2))) ≤
      ∫ t : ℝ, |t| * Real.exp (-(t ^ 2 * vlo / 2)) := by
    apply integral_mono (integrable_abs_gaussian (sq_pos_of_pos hσ)) (integrable_abs_gaussian hvlo)
    intro t
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlo (sq_nonneg t)]
  have hlow : saLowFrequencyConstant σ β ≤ β * Real.sqrt vhi ^ 3 *
      (∫ t : ℝ, |t| ^ 3 * Real.exp (-(t ^ 2 * vlo / 6))) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσ.le hs 3) hβ0) hc
      (integral_nonneg fun t => by positivity) (by positivity)
  have htail : β * σ * (∫ t : ℝ, |t| * Real.exp (-(t ^ 2 * σ ^ 2 / 2))) ≤
      β * Real.sqrt vhi * (∫ t : ℝ, |t| * Real.exp (-(t ^ 2 * vlo / 2))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hs hβ0) ha
      (integral_nonneg fun t => by positivity) (by positivity)
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  have hr : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hrl : Real.sqrt (l : ℝ) ≤ l := by
    have hsqr := Real.sq_sqrt (show (0 : ℝ) ≤ l by positivity)
    nlinarith [Real.sqrt_nonneg (l : ℝ)]
  have hhigh : (Real.sqrt (2 * Real.pi) * (Nat.factorial 9 : ℝ) / κ ^ 9) / l ≤
      (Real.sqrt (2 * Real.pi) * (Nat.factorial 9 : ℝ) / κ ^ 9) / Real.sqrt l :=
    div_le_div_of_nonneg_left (by positivity) hr hrl
  unfold saFourierCLTConstant
  simpa only [add_div] using
    add_le_add (div_le_div_of_nonneg_right (add_le_add hlow htail) hr.le) hhigh

end

end PGM
