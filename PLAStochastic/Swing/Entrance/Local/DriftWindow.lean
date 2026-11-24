import PLAStochastic.Swing.Entrance.Local.Crossing
import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.DriftTilt

/-!
# A small drift is invisible on a short window (E10)

For `q` iid standard Gaussian increments and a constant shift `-c`, the finite Cameron–Martin
formula writes the shifted law as the standard product law with the likelihood ratio
`ℓ(w) = exp(∑_{i<q} (-c w_i - c²/2))`. Since `∫ ℓ = 1`,

`∫ |ℓ - 1| = 2 ∫ (1 - ℓ)⁺ ≤ 2 ∫ |log ℓ| ≤ 2 |c| q E|Z| + q c²`,

using only `1 - e^x ≤ -x`. Hence for every functional `h` of the increments that is bounded by
`C` and reads only the first `q` increments,

`|E h(X - c) - E h(X)| ≤ C (2 |c| q E|Z| + q c²)`   (`drift_window_bound`).

No Kullback–Leibler divergence or Pinsker inequality is used. On the entrance window
`q_E = ⌊E^{3/4}⌋` and for `|c| ≤ M/E` the right side is `O(E^{-1/4})`.
-/

namespace SwingRepair

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The absolute mean `E|Z|` of a standard Gaussian variable. -/
def gaussianAbsMean : ℝ := ∫ x, |x| ∂(gaussianReal 0 1)

theorem integrable_abs_gaussianReal : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) :=
  ((memLp_id_gaussianReal 1).integrable le_rfl).abs

theorem gaussianAbsMean_nonneg : 0 ≤ gaussianAbsMean :=
  integral_nonneg fun x => abs_nonneg x

/-! ## The likelihood ratio of a constant shift -/

section Vector

variable {q : ℕ}

/-- The finite Cameron–Martin likelihood ratio of the constant shift by `-c`. -/
def shiftLikelihood (q : ℕ) (c : ℝ) (w : Fin q → ℝ) : ℝ :=
  Real.exp (∑ i, ((-c) * w i - (-c) ^ 2 / 2))

theorem measurable_shiftLikelihood (c : ℝ) : Measurable (shiftLikelihood q c) := by
  unfold shiftLikelihood
  fun_prop

theorem pi_gaussian_shift (c : ℝ) :
    (Measure.pi fun _ : Fin q => gaussianReal 0 1).map (fun v i => v i - c) =
      (Measure.pi fun _ : Fin q => gaussianReal 0 1).withDensity
        (fun w => ENNReal.ofReal (shiftLikelihood q c w)) := by
  have : ∀ i : Fin q, SigmaFinite ((gaussianReal 0 1).map (fun x : ℝ => x - c)) := fun i => by
    rw [gaussianReal_map_sub_const]; infer_instance
  have hmap := Measure.pi_map_pi (μ := fun _ : Fin q => gaussianReal 0 1)
    (f := fun _ (x : ℝ) => x - c) (fun i => (measurable_sub_const c).aemeasurable)
  rw [hmap]
  simp_rw [gaussianReal_map_sub_const, zero_sub]
  rw [Fluctuation.pi_gaussian_drift_eq_withDensity (fun _ : Fin q => -c)]
  congr 1
  funext w
  unfold shiftLikelihood Fluctuation.tiltDensity
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]

/-- Finite Cameron–Martin formula for a constant shift, Bochner form. -/
theorem integral_shift_eq {F : (Fin q → ℝ) → ℝ} (hF : Measurable F) (c : ℝ) :
    ∫ v, F (fun i => v i - c) ∂(Measure.pi fun _ : Fin q => gaussianReal 0 1) =
      ∫ w, shiftLikelihood q c w * F w ∂(Measure.pi fun _ : Fin q => gaussianReal 0 1) := by
  have hshift : Measurable fun v : Fin q → ℝ => fun i => v i - c :=
    measurable_pi_lambda _ fun i =>
      (measurable_pi_apply i : Measurable fun v : Fin q → ℝ => v i).sub_const c
  rw [← integral_map hshift.aemeasurable hF.aestronglyMeasurable, pi_gaussian_shift,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_shiftLikelihood c).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext w
  rw [ENNReal.toReal_ofReal (show 0 ≤ shiftLikelihood q c w from (Real.exp_pos _).le),
    smul_eq_mul]

theorem integral_shiftLikelihood (c : ℝ) :
    ∫ w, shiftLikelihood q c w ∂(Measure.pi fun _ : Fin q => gaussianReal 0 1) = 1 := by
  have h := integral_shift_eq (q := q) (F := fun _ => (1 : ℝ)) measurable_const c
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at h
  exact h.symm

theorem integrable_shiftLikelihood (c : ℝ) :
    Integrable (shiftLikelihood q c) (Measure.pi fun _ : Fin q => gaussianReal 0 1) :=
  Integrable.of_integral_ne_zero (by rw [integral_shiftLikelihood]; exact one_ne_zero)

/-- The `L¹` distance between the likelihood ratio and `1`. -/
theorem integral_abs_shiftLikelihood_sub_one_le (c : ℝ) :
    ∫ w, |shiftLikelihood q c w - 1| ∂(Measure.pi fun _ : Fin q => gaussianReal 0 1) ≤
      2 * |c| * q * gaussianAbsMean + q * c ^ 2 := by
  set γ := Measure.pi fun _ : Fin q => gaussianReal 0 1
  set ℓ := shiftLikelihood q c
  set S : (Fin q → ℝ) → ℝ := fun w => ∑ i, ((-c) * w i - (-c) ^ 2 / 2)
  have hℓi := integrable_shiftLikelihood (q := q) c
  have hℓm := measurable_shiftLikelihood (q := q) c
  have habs : ∀ i : Fin q, Integrable (fun w : Fin q → ℝ => |w i|) γ := fun i =>
    integrable_comp_eval (μ := fun _ : Fin q => gaussianReal 0 1) integrable_abs_gaussianReal
  have hpos : Integrable (fun w => max (1 - ℓ w) 0) γ := by
    refine Integrable.of_bound ((measurable_const.sub hℓm).max measurable_const).aestronglyMeasurable
      1 (ae_of_all _ fun w => ?_)
    have h0 : 0 ≤ ℓ w := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) zero_le_one
  have hsplit : ∀ w, |ℓ w - 1| = (ℓ w - 1) + 2 * max (1 - ℓ w) 0 := by
    intro w
    rcases le_total (ℓ w) 1 with h | h
    · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
      ring
  have hbound : ∀ w, max (1 - ℓ w) 0 ≤ ∑ i, (|c| * |w i| + c ^ 2 / 2) := by
    intro w
    have hS : |S w| ≤ ∑ i, (|c| * |w i| + c ^ 2 / 2) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      calc |(-c) * w i - (-c) ^ 2 / 2| ≤ |(-c) * w i| + |(-c) ^ 2 / 2| := abs_sub _ _
        _ = |c| * |w i| + c ^ 2 / 2 := by
          rw [abs_mul, abs_neg, neg_sq, abs_of_nonneg (show (0 : ℝ) ≤ c ^ 2 / 2 by positivity)]
    refine max_le ?_ ((abs_nonneg _).trans hS)
    have h1 := Real.add_one_le_exp (S w)
    have h2 : ℓ w = Real.exp (S w) := rfl
    have h3 := neg_le_abs (S w)
    linarith
  have hsumi : Integrable (fun w : Fin q → ℝ => ∑ i, (|c| * |w i| + c ^ 2 / 2)) γ :=
    integrable_finsetSum _ fun i _ => ((habs i).const_mul |c|).add (integrable_const _)
  have hsum : ∫ w, ∑ i, (|c| * |w i| + c ^ 2 / 2) ∂γ = q * (|c| * gaussianAbsMean + c ^ 2 / 2) := by
    rw [integral_finsetSum _ (f := fun i (w : Fin q → ℝ) => |c| * |w i| + c ^ 2 / 2)
      fun i _ => ((habs i).const_mul |c|).add (integrable_const _)]
    have hi : ∀ i : Fin q, ∫ w, (|c| * |w i| + c ^ 2 / 2) ∂γ = |c| * gaussianAbsMean + c ^ 2 / 2 := by
      intro i
      rw [integral_add ((habs i).const_mul |c|) (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, smul_eq_mul, one_mul]
      congr 2
      exact integral_comp_eval (μ := fun _ : Fin q => gaussianReal 0 1)
        (f := fun x : ℝ => |x|) continuous_abs.aestronglyMeasurable
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc ∫ w, |ℓ w - 1| ∂γ = ∫ w, ((ℓ w - 1) + 2 * max (1 - ℓ w) 0) ∂γ := by simp_rw [hsplit]
    _ = (∫ w, ℓ w ∂γ - 1) + 2 * ∫ w, max (1 - ℓ w) 0 ∂γ := by
      rw [integral_add (f := fun w => ℓ w - 1) (g := fun w => 2 * max (1 - ℓ w) 0)
          (hℓi.sub (integrable_const _)) (hpos.const_mul 2),
        integral_sub (f := ℓ) (g := fun _ => (1 : ℝ)) hℓi (integrable_const _),
        integral_const_mul, integral_const, probReal_univ, smul_eq_mul, mul_one]
    _ = 2 * ∫ w, max (1 - ℓ w) 0 ∂γ := by rw [integral_shiftLikelihood]; ring
    _ ≤ 2 * ∫ w, ∑ i, (|c| * |w i| + c ^ 2 / 2) ∂γ :=
      mul_le_mul_of_nonneg_left (integral_mono hpos hsumi hbound) (by norm_num)
    _ = 2 * |c| * q * gaussianAbsMean + q * c ^ 2 := by rw [hsum]; ring

/-- Bounded functionals of a standard Gaussian vector move by at most `C ∫ |ℓ - 1|` under a
constant shift. -/
theorem integral_shift_sub_le {H : (Fin q → ℝ) → ℝ} (hH : Measurable H) {C : ℝ}
    (hC : ∀ v, |H v| ≤ C) (c : ℝ) :
    |∫ v, H (fun i => v i - c) ∂(Measure.pi fun _ : Fin q => gaussianReal 0 1) -
        ∫ v, H v ∂(Measure.pi fun _ : Fin q => gaussianReal 0 1)| ≤
      C * (2 * |c| * q * gaussianAbsMean + q * c ^ 2) := by
  set γ := Measure.pi fun _ : Fin q => gaussianReal 0 1
  set ℓ := shiftLikelihood q c
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hℓi := integrable_shiftLikelihood (q := q) c
  have hHb : ∀ᵐ v ∂γ, ‖H v‖ ≤ C := ae_of_all _ fun v => by rw [Real.norm_eq_abs]; exact hC v
  have hHi : Integrable H γ := Integrable.of_bound hH.aestronglyMeasurable C hHb
  have hℓH : Integrable (fun w => ℓ w * H w) γ := by
    have := hℓi.bdd_mul hH.aestronglyMeasurable hHb
    simpa only [mul_comm] using this
  have hdiff : Integrable (fun w => |ℓ w - 1|) γ := (hℓi.sub (integrable_const _)).abs
  rw [integral_shift_eq hH c, ← integral_sub hℓH hHi]
  calc |∫ w, (ℓ w * H w - H w) ∂γ| ≤ ∫ w, |ℓ w * H w - H w| ∂γ := abs_integral_le_integral_abs
    _ ≤ ∫ w, C * |ℓ w - 1| ∂γ := by
      refine integral_mono (hℓH.sub hHi).abs (hdiff.const_mul C) fun w => ?_
      rw [show ℓ w * H w - H w = (ℓ w - 1) * H w by ring, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC w) (abs_nonneg _)
    _ = C * ∫ w, |ℓ w - 1| ∂γ := integral_const_mul _ _
    _ ≤ C * (2 * |c| * q * gaussianAbsMean + q * c ^ 2) :=
      mul_le_mul_of_nonneg_left (integral_abs_shiftLikelihood_sub_one_le c) hC0

end Vector

/-! ## Functionals of the first `q` increments -/

/-- Extension of a finite vector by zeros. -/
def finExtend {q : ℕ} (v : Fin q → ℝ) (i : ℕ) : ℝ := if h : i < q then v ⟨i, h⟩ else 0

theorem measurable_finExtend {q : ℕ} : Measurable (finExtend (q := q)) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i < q
  · simp only [finExtend, dif_pos h]
    exact measurable_pi_apply _
  · simp only [finExtend, dif_neg h]
    exact measurable_const

theorem finExtend_restrict {q : ℕ} (x : ℕ → ℝ) : ∀ i < q, finExtend (fun i : Fin q => x i) i = x i :=
  fun i hi => by simp [finExtend, hi]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The first `q` increments of an iid standard Gaussian sequence form a standard Gaussian
vector. -/
theorem map_window_eq_pi (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (q : ℕ) :
    μ.map (fun ω (i : Fin q) => X i ω) = Measure.pi fun _ : Fin q => gaussianReal 0 1 := by
  have := hi.isProbabilityMeasure
  have hq : iIndepFun (fun i : Fin q => X i) μ := hi.precomp Fin.val_injective
  rw [(iIndepFun_iff_map_fun_eq_pi_map (f := fun i : Fin q => X i)
    (fun i => (hX i).aemeasurable)).mp hq]
  simp only [hG]

/-- (E10) A constant drift `-c` changes the expectation of a bounded functional of the first
`q` increments by at most `C (2 |c| q E|Z| + q c²)`. -/
theorem drift_window_bound (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {q : ℕ}
    {h : (ℕ → ℝ) → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (hloc : ∀ x x' : ℕ → ℝ, (∀ i < q, x i = x' i) → h x = h x') (c : ℝ) :
    |∫ ω, h (fun i => X i ω - c) ∂μ - ∫ ω, h (fun i => X i ω) ∂μ| ≤
      C * (2 * |c| * q * gaussianAbsMean + q * c ^ 2) := by
  have := hi.isProbabilityMeasure
  set H : (Fin q → ℝ) → ℝ := fun v => h (finExtend v)
  have hH : Measurable H := hh.comp measurable_finExtend
  have hHC : ∀ v, |H v| ≤ C := fun v => hC _
  have hrestrict : ∀ x : ℕ → ℝ, h x = H (fun i : Fin q => x i) := fun x =>
    hloc _ _ fun i hi => (finExtend_restrict x i hi).symm
  have hV : Measurable fun ω (i : Fin q) => X i ω := measurable_pi_lambda _ fun i => hX i
  have hshift : Measurable fun v : Fin q → ℝ => H (fun i => v i - c) :=
    hH.comp (measurable_pi_lambda _ fun i =>
      (measurable_pi_apply i : Measurable fun v : Fin q → ℝ => v i).sub_const c)
  have e1 : ∫ ω, h (fun i => X i ω - c) ∂μ =
      ∫ v, H (fun i => v i - c) ∂(Measure.pi fun _ : Fin q => gaussianReal 0 1) := by
    rw [← map_window_eq_pi hX hi hG q, integral_map hV.aemeasurable hshift.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ fun ω => hrestrict _)
  have e2 : ∫ ω, h (fun i => X i ω) ∂μ =
      ∫ v, H v ∂(Measure.pi fun _ : Fin q => gaussianReal 0 1) := by
    rw [← map_window_eq_pi hX hi hG q, integral_map hV.aemeasurable hH.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ fun ω => hrestrict _)
  rw [e1, e2]
  exact integral_shift_sub_le hH hHC c

end

end SwingRepair
