import PLAStochastic.Index.GEP.StrongApprox.Tilt.CenteredTilt
import Mathlib.Probability.Moments.Tilted
import Mathlib.Analysis.Calculus.MeanValue

/-!
# WP5: uniform cumulants of the centered gap

The cumulant generating function is Mathlib's `cgf` applied to `x - 1`.  All bounds
are uniform over `UnivClass`; no smoothness or density assumption is needed here.
The factorial moment constants are deliberately coarser than those in the blueprint.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- A convenient uniform bound for the weighted centered moment of order `k`. -/
def saMoment (B θ : ℝ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * (2 / θ) ^ k * (Real.exp θ * max B 1)

theorem saMoment_pos (B : ℝ) {θ : ℝ} (hθ : 0 < θ) (k : ℕ) : 0 < saMoment B θ k := by
  unfold saMoment
  have : 0 < max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  positivity

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

/-- Every point strictly inside the original weight lies in the analytic domain. -/
theorem UnivClass.centered_mem_interior (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) :
    lam ∈ interior (integrableExpSet (fun x : ℝ => x - 1) (ν : Measure ℝ)) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hopen : IsOpen {t : ℝ | |t| < θ} := isOpen_lt continuous_abs continuous_const
  refine Filter.mem_of_superset (hopen.mem_nhds hlam) ?_
  intro t ht
  exact h.integrable_exp_centered ht.le

theorem UnivClass.integral_exp_abs_sub_one_le (h : UnivClass vlo vhi κ₃ B θ ν)
    (hθ : 0 < θ) :
    (∫ x : ℝ, Real.exp (θ * |x - 1|) ∂(ν : Measure ℝ)) ≤ Real.exp θ * max B 1 := by
  have hb := h.lintegral_exp_abs_sub_one_le hθ.le le_rfl
  have hi := h.integrable_exp_abs_sub_one hθ.le le_rfl
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun x => Real.exp_nonneg _)] at hb
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ Real.exp θ * max B 1)).mp
  exact hb.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (le_max_left _ _) (Real.exp_nonneg _)))

/-- Polynomial factors can use half of the exponential-moment budget. -/
theorem sa_pow_mul_exp_le {θ lam y : ℝ} (hθ : 0 < θ) (hlam : |lam| ≤ θ / 2) (k : ℕ) :
    |y| ^ k * Real.exp (lam * y) ≤
      ((k.factorial : ℝ) * (2 / θ) ^ k) * Real.exp (θ * |y|) := by
  have hp : 0 < (k.factorial : ℝ) := by positivity
  have ht : 0 < θ / 2 := by positivity
  have ha := Real.pow_div_factorial_le_exp (θ / 2 * |y|)
    (show 0 ≤ θ / 2 * |y| by positivity) k
  have hpol : |y| ^ k ≤ ((k.factorial : ℝ) * (2 / θ) ^ k) * Real.exp (θ / 2 * |y|) := by
    rw [div_le_iff₀ hp, mul_pow] at ha
    have htp : 0 < (θ / 2) ^ k := pow_pos ht _
    have hi : (2 / θ) ^ k * (θ / 2) ^ k = 1 := by
      rw [← mul_pow]
      have : 2 / θ * (θ / 2) = 1 := by field_simp
      rw [this, one_pow]
    calc |y| ^ k = (2 / θ) ^ k * ((θ / 2) ^ k * |y| ^ k) := by rw [← mul_assoc, hi, one_mul]
      _ ≤ (2 / θ) ^ k * (Real.exp (θ / 2 * |y|) * (k.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left ha (by positivity)
      _ = _ := by ring
  calc
    |y| ^ k * Real.exp (lam * y) ≤
        (((k.factorial : ℝ) * (2 / θ) ^ k) * Real.exp (θ / 2 * |y|)) *
          Real.exp (lam * y) := mul_le_mul_of_nonneg_right hpol (Real.exp_nonneg _)
    _ = ((k.factorial : ℝ) * (2 / θ) ^ k) * Real.exp (θ / 2 * |y| + lam * y) := by
      rw [Real.exp_add]; ring
    _ ≤ _ := by
      gcongr
      have hm : lam * y ≤ |lam| * |y| := (le_abs_self _).trans_eq (abs_mul _ _)
      nlinarith [mul_le_mul_of_nonneg_right hlam (abs_nonneg y)]

/-- Uniform integral bounds for every weighted centered moment. -/
theorem UnivClass.centered_weighted_moment (h : UnivClass vlo vhi κ₃ B θ ν)
    (hθ : 0 < θ) {lam : ℝ} (hlam : |lam| ≤ θ / 2) (k : ℕ) :
    Integrable (fun x : ℝ => |x - 1| ^ k * Real.exp (lam * (x - 1))) (ν : Measure ℝ) ∧
      (∫ x : ℝ, |x - 1| ^ k * Real.exp (lam * (x - 1)) ∂(ν : Measure ℝ)) ≤
        saMoment B θ k := by
  have hi := h.integrable_exp_abs_sub_one hθ.le le_rfl
  have hc : 0 ≤ (k.factorial : ℝ) * (2 / θ) ^ k := by positivity
  have hpt := fun x => sa_pow_mul_exp_le hθ hlam (y := x - 1) k
  have hm : Integrable (fun x : ℝ => |x - 1| ^ k * Real.exp (lam * (x - 1)))
      (ν : Measure ℝ) := by
    refine (hi.const_mul ((k.factorial : ℝ) * (2 / θ) ^ k)).mono'
      (by fun_prop) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt x
  refine ⟨hm, ?_⟩
  calc
    _ ≤ ∫ x : ℝ, ((k.factorial : ℝ) * (2 / θ) ^ k) * Real.exp (θ * |x - 1|)
        ∂(ν : Measure ℝ) := integral_mono hm (hi.const_mul _) hpt
    _ = ((k.factorial : ℝ) * (2 / θ) ^ k) *
        ∫ x : ℝ, Real.exp (θ * |x - 1|) ∂(ν : Measure ℝ) := integral_const_mul _ _
    _ ≤ saMoment B θ k := mul_le_mul_of_nonneg_left
      (h.integral_exp_abs_sub_one_le hθ) hc

/-- Uniform derivatives of the centered moment generating function. -/
theorem UnivClass.abs_iteratedDeriv_centered_mgf_le (h : UnivClass vlo vhi κ₃ B θ ν)
    (hθ : 0 < θ) {lam : ℝ} (hlam : |lam| ≤ θ / 2) (k : ℕ) :
    |iteratedDeriv k (mgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam| ≤ saMoment B θ k := by
  have ht := h.centered_mem_interior (lt_of_le_of_lt hlam (by linarith))
  rw [iteratedDeriv_mgf ht]
  calc
    _ ≤ ∫ x : ℝ, |(x - 1) ^ k * Real.exp (lam * (x - 1))| ∂(ν : Measure ℝ) :=
      abs_integral_le_integral_abs
    _ = ∫ x : ℝ, |x - 1| ^ k * Real.exp (lam * (x - 1)) ∂(ν : Measure ℝ) := by
      congr 1; ext x
      rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    _ ≤ _ := (h.centered_weighted_moment hθ hlam k).2

/-- The third cumulant derivative written using normalized derivatives of the mgf. -/
theorem iteratedDeriv_three_cgf_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {lam : ℝ}
    (ht : lam ∈ interior (integrableExpSet X P)) :
    iteratedDeriv 3 (cgf X P) lam =
      iteratedDeriv 3 (mgf X P) lam / mgf X P lam -
        3 * (deriv (mgf X P) lam / mgf X P lam) *
          (iteratedDeriv 2 (mgf X P) lam / mgf X P lam) +
        2 * (deriv (mgf X P) lam / mgf X P lam) ^ 3 := by
  have hM : mgf X P lam ≠ 0 :=
    (mgf_pos' (NeZero.ne P) (interior_subset (s := integrableExpSet X P) ht)).ne'
  have hd (k : ℕ) : HasDerivAt (iteratedDeriv k (mgf X P))
      (iteratedDeriv (k + 1) (mgf X P) lam) lam := by
    rw [iteratedDeriv_mgf ht]
    exact hasDerivAt_iteratedDeriv_mgf ht k
  have h0 := (differentiableAt_mgf ht).hasDerivAt
  have h1 : HasDerivAt (deriv (mgf X P)) (iteratedDeriv 2 (mgf X P) lam) lam := by
    simpa only [iteratedDeriv_one] using hd 1
  have heq : iteratedDeriv 2 (cgf X P) =ᶠ[𝓝 lam]
      fun t => iteratedDeriv 2 (mgf X P) t / mgf X P t -
        (deriv (mgf X P) t / mgf X P t) ^ 2 := by
    filter_upwards [isOpen_interior.eventually_mem ht] with t ht
    rw [iteratedDeriv_two_cgf ht, deriv_cgf ht, iteratedDeriv_mgf ht, deriv_mgf ht]
  have hh := ((hd 2).div h0 hM).sub ((h1.div h0 hM).pow 2)
  change HasDerivAt (fun t => iteratedDeriv 2 (mgf X P) t / mgf X P t -
    (deriv (mgf X P) t / mgf X P t) ^ 2) _ lam at hh
  rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ, heq.deriv_eq, hh.deriv]
  simp only [Pi.div_apply]
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceSub, pow_one]
  field_simp [hM]
  ring

/-- A uniform third cumulant bound. -/
def saCumulantThird (B θ : ℝ) : ℝ :=
  saMoment B θ 3 + 3 * saMoment B θ 1 * saMoment B θ 2 + 2 * saMoment B θ 1 ^ 3

theorem saCumulantThird_pos (B : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    0 < saCumulantThird B θ := by
  unfold saCumulantThird
  have := saMoment_pos B hθ 1
  have := saMoment_pos B hθ 2
  have := saMoment_pos B hθ 3
  positivity

theorem UnivClass.abs_iteratedDeriv_three_centered_cgf_le
    (h : UnivClass vlo vhi κ₃ B θ ν) (hθ : 0 < θ) {lam : ℝ} (hlam : |lam| ≤ θ / 2) :
    |iteratedDeriv 3 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam| ≤
      saCumulantThird B θ := by
  have ht := h.centered_mem_interior (lt_of_le_of_lt hlam (by linarith))
  have hM : 1 ≤ mgf (fun x : ℝ => x - 1) (ν : Measure ℝ) lam :=
    h.one_le_integral_exp_centered (hlam.trans (by linarith))
  have hb (k : ℕ) : |iteratedDeriv k (mgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam /
      mgf (fun x : ℝ => x - 1) (ν : Measure ℝ) lam| ≤ saMoment B θ k := by
    rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hM)]
    exact (div_le_self (abs_nonneg _) hM).trans
      (h.abs_iteratedDeriv_centered_mgf_le hθ hlam k)
  rw [iteratedDeriv_three_cgf_eq ht]
  have htri (a b c : ℝ) : |a - 3 * b * c + 2 * b ^ 3| ≤
      |a| + 3 * |b| * |c| + 2 * |b| ^ 3 := by
    calc
      _ ≤ |a - 3 * b * c| + |2 * b ^ 3| := abs_add_le _ _
      _ ≤ (|a| + |3 * b * c|) + |2 * b ^ 3| :=
        add_le_add (abs_sub a (3 * b * c)) le_rfl
      _ = _ := by simp [abs_mul, abs_pow]
  calc
    _ ≤ |iteratedDeriv 3 (mgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam /
          mgf (fun x : ℝ => x - 1) (ν : Measure ℝ) lam| +
        3 * |deriv (mgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam /
          mgf (fun x : ℝ => x - 1) (ν : Measure ℝ) lam| *
          |iteratedDeriv 2 (mgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam /
            mgf (fun x : ℝ => x - 1) (ν : Measure ℝ) lam| +
        2 * |deriv (mgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam /
          mgf (fun x : ℝ => x - 1) (ν : Measure ℝ) lam| ^ 3 := by
      exact htri _ _ _
    _ ≤ _ := by
      unfold saCumulantThird
      have h1 := hb 1
      simp only [iteratedDeriv_one] at h1
      have hm1 := (saMoment_pos B hθ 1).le
      have hm2 := (saMoment_pos B hθ 2).le
      gcongr <;> first | exact hb 3 | exact h1 | exact hb 2

theorem UnivClass.integral_centered_eq_zero (h : UnivClass vlo vhi κ₃ B θ ν) :
    (∫ x : ℝ, (x - 1) ∂(ν : Measure ℝ)) = 0 := by
  have hx : Integrable (fun x : ℝ => x) (ν : Measure ℝ) := h.memLp3.integrable (by norm_num)
  rw [integral_sub hx (integrable_const 1)]
  change lawMean ν - _ = 0
  simp [h.mean]

theorem UnivClass.deriv_centered_cgf_zero (h : UnivClass vlo vhi κ₃ B θ ν) (hθ : 0 < θ) :
    deriv (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) 0 = 0 := by
  rw [deriv_cgf_zero (h.centered_mem_interior (by simpa using hθ)),
    h.integral_centered_eq_zero, zero_div]

theorem UnivClass.iteratedDeriv_two_centered_cgf_zero
    (h : UnivClass vlo vhi κ₃ B θ ν) (hθ : 0 < θ) :
    iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) 0 = lawVar ν := by
  rw [iteratedDeriv_two_cgf (h.centered_mem_interior (by simpa using hθ)),
    h.deriv_centered_cgf_zero hθ]
  simp [lawVar, h.mean]

/-- The second cumulant derivative is uniformly Lipschitz on the half-weight interval. -/
theorem UnivClass.iteratedDeriv_two_centered_cgf_lipschitz
    (h : UnivClass vlo vhi κ₃ B θ ν) (hθ : 0 < θ) {a b : ℝ}
    (ha : |a| ≤ θ / 2) (hb : |b| ≤ θ / 2) :
    |iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) b -
        iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) a| ≤
      saCumulantThird B θ * |b - a| := by
  have hd : ∀ t ∈ Icc (-θ / 2) (θ / 2),
      DifferentiableAt ℝ (iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ))) t := by
    intro t ht
    have ht' : |t| < θ := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [iteratedDeriv_eq_iterate]
    exact (analyticOnNhd_cgf.iterated_deriv 2 t (h.centered_mem_interior ht')).differentiableAt
  have hbound : ∀ t ∈ Icc (-θ / 2) (θ / 2),
      ‖deriv (iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ))) t‖ ≤
        saCumulantThird B θ := by
    intro t ht
    rw [← iteratedDeriv_succ, Real.norm_eq_abs]
    exact h.abs_iteratedDeriv_three_centered_cgf_le hθ
      (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)
  have ha' : a ∈ Icc (-θ / 2) (θ / 2) := by
    rcases abs_le.mp ha with ⟨ha1, ha2⟩
    exact ⟨by linarith, ha2⟩
  have hb' : b ∈ Icc (-θ / 2) (θ / 2) := by
    rcases abs_le.mp hb with ⟨hb1, hb2⟩
    exact ⟨by linarith, hb2⟩
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (-θ / 2) (θ / 2)).norm_image_sub_le_of_norm_deriv_le hd hbound ha' hb'

/-- The tilted variance stays close to the original variance at linear rate in the tilt. -/
theorem UnivClass.iteratedDeriv_two_centered_cgf_sub_var_le
    (h : UnivClass vlo vhi κ₃ B θ ν) (hθ : 0 < θ) {lam : ℝ} (hlam : |lam| ≤ θ / 2) :
    |iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam - lawVar ν| ≤
      saCumulantThird B θ * |lam| := by
  have hh := h.iteratedDeriv_two_centered_cgf_lipschitz hθ
    (a := 0) (b := lam) (by simpa using (half_pos hθ).le) hlam
  rwa [h.iteratedDeriv_two_centered_cgf_zero hθ, sub_zero] at hh

/-- A class-uniform interval on which the tilted variance is bounded below. -/
def saTiltRadius (vlo B θ : ℝ) : ℝ := min (θ / 4) (vlo / (4 * saCumulantThird B θ))

theorem saTiltRadius_pos {vlo B θ : ℝ} (hvlo : 0 < vlo) (hθ : 0 < θ) :
    0 < saTiltRadius vlo B θ := by
  unfold saTiltRadius
  exact lt_min (by positivity) (div_pos hvlo (mul_pos (by norm_num) (saCumulantThird_pos B hθ)))

theorem saTiltRadius_le_half (vlo B : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    saTiltRadius vlo B θ ≤ θ / 2 :=
  (min_le_left _ _).trans (by linarith)

/-- Relative variance brackets, with the same class-uniform tilt interval. -/
theorem UnivClass.centered_cgf_variance_bracket (h : UnivClass vlo vhi κ₃ B θ ν)
    (_hvlo : 0 < vlo) (hθ : 0 < θ) {lam : ℝ} (hlam : |lam| ≤ saTiltRadius vlo B θ) :
    3 / 4 * lawVar ν ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam ∧
      iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam ≤ 5 / 4 * lawVar ν := by
  have hc := saCumulantThird_pos B hθ
  have hm : |lam| ≤ vlo / (4 * saCumulantThird B θ) :=
    hlam.trans (min_le_right _ _)
  have hsmall : saCumulantThird B θ * |lam| ≤ vlo / 4 := by
    rw [le_div_iff₀ (by positivity)] at hm
    linarith
  have hbound := abs_le.mp (h.iteratedDeriv_two_centered_cgf_sub_var_le hθ
    (hlam.trans (saTiltRadius_le_half vlo B hθ)))
  have hvar := h.var_ge
  constructor <;> linarith

/-- The mean of the centered variable under the tilt is the first cumulant derivative. -/
theorem UnivClass.integral_centered_centeredTilt (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) :
    (∫ x : ℝ, (x - 1) ∂centeredTilt ν lam) =
      deriv (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam :=
  integral_tilted_mul_self (h.centered_mem_interior hlam)

/-- The variance under the tilt is the second cumulant derivative. -/
theorem UnivClass.variance_centeredTilt (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) :
    Var[(fun x : ℝ => x - 1); centeredTilt ν lam] =
      iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam :=
  variance_tilted_mul (h.centered_mem_interior hlam)

/-- The centered cumulant function after adding an independent `N(0,s²)` variable. -/
def saSmoothCGF (ν : ProbabilityMeasure ℝ) (s t : ℝ) : ℝ :=
  cgf (fun x : ℝ => x - 1) (ν : Measure ℝ) t + s ^ 2 * t ^ 2 / 2

theorem UnivClass.analyticAt_saSmoothCGF (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) (s : ℝ) : AnalyticAt ℝ (saSmoothCGF ν s) lam := by
  exact (analyticAt_cgf (h.centered_mem_interior hlam)).add (by fun_prop)

theorem UnivClass.hasDerivAt_saSmoothCGF (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) (s : ℝ) :
    HasDerivAt (saSmoothCGF ν s)
      (deriv (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam + s ^ 2 * lam) lam := by
  have hp : HasDerivAt (fun t : ℝ => s ^ 2 * t ^ 2 / 2) (s ^ 2 * lam) lam := by
    have hh := (((hasDerivAt_id lam).fun_pow 2).const_mul (s ^ 2)).div_const 2
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hh
    convert hh using 1 <;> first | rfl | ring
  exact ((analyticAt_cgf (h.centered_mem_interior hlam)).differentiableAt.hasDerivAt).add hp

theorem UnivClass.deriv_saSmoothCGF (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) (s : ℝ) :
    deriv (saSmoothCGF ν s) lam =
      deriv (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam + s ^ 2 * lam :=
  (h.hasDerivAt_saSmoothCGF hlam s).deriv

theorem UnivClass.hasDerivAt_deriv_saSmoothCGF (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) (s : ℝ) :
    HasDerivAt (deriv (saSmoothCGF ν s))
      (iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam + s ^ 2) lam := by
  have hc : DifferentiableAt ℝ (deriv (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ))) lam := by
    exact (analyticOnNhd_cgf.deriv _ (h.centered_mem_interior hlam)).differentiableAt
  have hd : HasDerivAt (deriv (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)))
      (iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam) lam := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hc.hasDerivAt
  have hs : HasDerivAt (fun t : ℝ => s ^ 2 * t) (s ^ 2) lam := by
    simpa using (hasDerivAt_id lam).const_mul (s ^ 2)
  refine (hd.add hs).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_abs continuous_const).eventually_mem hlam] with t ht
  exact h.deriv_saSmoothCGF ht s

theorem UnivClass.iteratedDeriv_two_saSmoothCGF (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) (s : ℝ) :
    iteratedDeriv 2 (saSmoothCGF ν s) lam =
      iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam + s ^ 2 := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    (h.hasDerivAt_deriv_saSmoothCGF hlam s).deriv

theorem UnivClass.iteratedDeriv_three_saSmoothCGF (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) (s : ℝ) :
    iteratedDeriv 3 (saSmoothCGF ν s) lam =
      iteratedDeriv 3 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam := by
  have hc : DifferentiableAt ℝ (iteratedDeriv 2
      (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ))) lam := by
    rw [iteratedDeriv_eq_iterate]
    exact (analyticOnNhd_cgf.iterated_deriv 2 _ (h.centered_mem_interior hlam)).differentiableAt
  have heq : iteratedDeriv 2 (saSmoothCGF ν s) =ᶠ[𝓝 lam]
      fun t => iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) t + s ^ 2 := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).eventually_mem hlam] with t ht
    exact h.iteratedDeriv_two_saSmoothCGF ht s
  rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ, heq.deriv_eq]
  conv_rhs => rw [iteratedDeriv_succ]
  exact (hc.hasDerivAt.add_const (s ^ 2)).deriv

@[simp] theorem saSmoothCGF_zero (ν : ProbabilityMeasure ℝ) (s : ℝ) :
    saSmoothCGF ν s 0 = 0 := by simp [saSmoothCGF, cgf]

theorem UnivClass.deriv_saSmoothCGF_zero (h : UnivClass vlo vhi κ₃ B θ ν)
    (hθ : 0 < θ) (s : ℝ) : deriv (saSmoothCGF ν s) 0 = 0 := by
  rw [h.deriv_saSmoothCGF (by simpa using hθ) s, h.deriv_centered_cgf_zero hθ]
  ring

/-- The Gaussian smoothing preserves the relative variance bracket. -/
theorem UnivClass.saSmoothCGF_variance_bracket (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {lam : ℝ} (hlam : |lam| ≤ saTiltRadius vlo B θ) (s : ℝ) :
    3 / 4 * (lawVar ν + s ^ 2) ≤ iteratedDeriv 2 (saSmoothCGF ν s) lam ∧
      iteratedDeriv 2 (saSmoothCGF ν s) lam ≤ 5 / 4 * (lawVar ν + s ^ 2) := by
  rw [h.iteratedDeriv_two_saSmoothCGF
    (lt_of_le_of_lt (hlam.trans (saTiltRadius_le_half vlo B hθ)) (by linarith))]
  have hh := h.centered_cgf_variance_bracket hvlo hθ hlam
  constructor <;> nlinarith [sq_nonneg s]

end

end PGM
