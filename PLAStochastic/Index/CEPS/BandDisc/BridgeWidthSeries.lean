import PLAStochastic.Index.CEPS.BandDisc.Analytic
import Mathlib.Analysis.Complex.Liouville

/-!
# True discount holomorphy of the classical bridge width derivative

The coefficients are the genuine derivatives of finite killed densities. A
summable finite width modulus at a more negative reference discount pays every
polynomial moment. Neither continuity of the density derivative nor a formal
interchange of total derivatives is used.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

/-- An exponential margin upgrades absolute summability to all time moments. -/
theorem cepsBandDisc_moments_of_margin {c : ℕ → ℂ} {b₀ b : ℝ}
    (hb : b₀ < b)
    (hs : Summable (fun n : ℕ => ‖Complex.exp (-(b₀ : ℂ) * (n + 1 : ℕ)) * c n‖)) :
    CepsDiscMoments c 1 b := by
  intro j
  let r := b - b₀
  have hr : 0 < r := sub_pos.mpr hb
  let A := (j.factorial : ℝ) * Real.exp 1 * (1 + 2 / r) ^ j
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he : ∀ n : ℕ, ‖Complex.exp (-(b : ℂ) * (n + 1 : ℕ)) * c n‖ =
      Real.exp (-r * (n + 1 : ℕ)) *
        ‖Complex.exp (-(b₀ : ℂ) * (n + 1 : ℕ)) * c n‖ := by
    intro n
    have heq : Complex.exp (-(b : ℂ) * (n + 1 : ℕ)) =
        Complex.exp (-(r : ℂ) * (n + 1 : ℕ)) *
          Complex.exp (-(b₀ : ℂ) * (n + 1 : ℕ)) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp [r]
      push_cast
      ring
    rw [heq, mul_assoc, norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
  have hp : ∀ n : ℕ, (n + 1 : ℝ) ^ j * Real.exp (-r * (n + 1 : ℕ)) ≤ A := by
    intro n
    calc
      _ ≤ (n + 1 : ℝ) ^ j * Real.exp (-r * n) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        push_cast
        nlinarith
      _ ≤ A * Real.exp (-(r / 2) * n) := Real.polynomial_mul_exp_neg_le hr j n
      _ ≤ A := mul_le_of_le_one_right hA
        (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg n)))
  exact (hs.mul_left A).of_nonneg_of_le (fun n => by positivity) (fun n => by
    rw [he, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hp n) (norm_nonneg _))

/-- Coefficients of the bridge width derivative are actual finite real derivatives. -/
def cepsBandDiscBridgeWidthCoeff (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (β a l : ℝ) (n : ℕ) : ℂ :=
  ((deriv (fun t : ℝ => krDens (Icc 0 t) ν f β a (n + 1) 0 t) l : ℝ) : ℂ)

/-- The genuine width derivative equals the series of genuine finite derivatives. -/
theorem cepsBandDisc_bridge_width_hasDerivAt_series {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    (hd : Differentiable ℝ f) {K : ℝ≥0} (hK : ∀ x, |deriv f x| ≤ K)
    {l : ℝ} (hl : 2 ≤ l) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * l ^ 2)) ≤ q.re) :
    HasDerivAt (cepsBridgeSeries ν f β a q)
      (cepsDiscJet (cepsBandDiscBridgeWidthCoeff ν f β a l) 1 0 q) l := by
  have hLip := cepsBand_density_lipschitz_of_deriv hd hK
  obtain ⟨M, hM, hfinite⟩ := cepsBand_pin_finite_lipschitz hD hθ hvlo hvhi hν hf
    hLip hl β ha hq
  let g := fun n : ℕ => fun t : ℝ => Complex.exp (-q * ((n : ℂ) + 1)) *
    (krDens (Icc 0 t) ν f β a (n + 1) 0 t : ℂ)
  let g' := fun n : ℕ => fun t : ℝ => Complex.exp (-q * ((n : ℂ) + 1)) *
    cepsBandDiscBridgeWidthCoeff ν f β a t n
  have ha0 : a ≠ 0 := abs_pos.mp (by linarith : 0 < |a|)
  have hdg : ∀ n t, t ∈ Ioo (l / 2) (2 * l) → HasDerivAt (g n) (g' n t) t := by
    intro n t ht
    simpa only [g, g', cepsBandDiscBridgeWidthCoeff] using
      ((hf.cepsBand_pin_differentiableAt hd hK β ha0
        (by linarith [ht.1] : 0 < t) n).hasDerivAt.ofReal_comp).const_mul
          (Complex.exp (-q * ((n : ℂ) + 1)))
  have hg' : ∀ n t, t ∈ Ioo (l / 2) (2 * l) → ‖g' n t‖ ≤ (M n : ℝ) := by
    intro n t ht
    rw [← (hdg n t ht).deriv]
    exact norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) (hfinite n)
  have hsum := (cepsBand_summable_density_norm hD hθ hvlo hvhi hν hf hl
    (by linarith : l / 2 ≤ l) (by linarith : l ≤ 2 * l) β ha hq 0 l).of_norm
  have h := hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioo isPreconnected_Ioo hdg hg'
    (by constructor <;> linarith : l ∈ Ioo (l / 2) (2 * l)) hsum
    (by constructor <;> linarith : l ∈ Ioo (l / 2) (2 * l))
  change HasDerivAt (fun t => ∑' n : ℕ, Complex.exp (-q * ((n : ℂ) + 1)) *
    (krDens (Icc 0 t) ν f β a (n + 1) 0 t : ℂ)) _ l
  simpa only [g, g', cepsDiscJet, pow_zero, one_mul,
    Nat.cast_add, Nat.cast_one] using h

/-- The derivative coefficients are absolutely summable at every valid reference discount. -/
theorem cepsBandDisc_bridge_width_coeff_summable {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    (hd : Differentiable ℝ f) {K : ℝ≥0} (hK : ∀ x, |deriv f x| ≤ K)
    {l : ℝ} (hl : 2 ≤ l) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * l ^ 2)) ≤ q.re) :
    Summable (fun n : ℕ => ‖Complex.exp (-q * (n + 1 : ℕ)) *
      cepsBandDiscBridgeWidthCoeff ν f β a l n‖) := by
  obtain ⟨M, hM, hfinite⟩ := cepsBand_pin_finite_lipschitz hD hθ hvlo hvhi hν hf
    (cepsBand_density_lipschitz_of_deriv hd hK) hl β ha hq
  have ha0 : a ≠ 0 := abs_pos.mp (by linarith : 0 < |a|)
  have hpoint : ∀ n, ‖Complex.exp (-q * (n + 1 : ℕ)) *
      cepsBandDiscBridgeWidthCoeff ν f β a l n‖ ≤ (M n : ℝ) := by
    intro n
    have hdg := ((hf.cepsBand_pin_differentiableAt hd hK β ha0
      (by linarith : 0 < l) n).hasDerivAt.ofReal_comp).const_mul
        (Complex.exp (-q * ((n : ℂ) + 1)))
    have h := norm_deriv_le_of_lipschitzOn
      (Icc_mem_nhds (by linarith : l / 2 < l) (by linarith : l < 2 * l)) (hfinite n)
    rw [hdg.deriv] at h
    simpa only [cepsBandDiscBridgeWidthCoeff, Nat.cast_add, Nat.cast_one] using h
  exact hM.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint

/-- The genuine classical bridge width derivative is holomorphic in the discount.
The width may be either endpoint of the closed window. -/
theorem cepsBandDisc_bridge_first_width_analyticAt {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    (hd : Differentiable ℝ f) {K : ℝ≥0} (hK : ∀ x, |deriv f x| ≤ K)
    {w l : ℝ} (hw : 4 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (64 * w ^ 2)) < q.re) :
    AnalyticAt ℂ (fun z : ℂ => deriv (cepsBridgeSeries ν f β a z) l) q := by
  let b₀ := -(krKappa D vlo vhi / (64 * w ^ 2))
  let b := (b₀ + q.re) / 2
  have hbl : -(krKappa D vlo vhi / (16 * l ^ 2)) ≤ b₀ := by
    have hl0 : 0 < l := by linarith
    have hb : krKappa D vlo vhi / (64 * w ^ 2) ≤ krKappa D vlo vhi / (16 * l ^ 2) := by
      apply div_le_div_of_nonneg_left (krKappa_pos hD hvlo hvhi).le (by positivity)
      nlinarith
    dsimp [b₀]
    linarith
  have hs := cepsBandDisc_bridge_width_coeff_summable hD hθ hvlo hvhi hν hf hd hK
    (by linarith : 2 ≤ l) β ha (q := (b₀ : ℂ)) (by change _ ≤ b₀; exact hbl)
  have hM := cepsBandDisc_moments_of_margin (by dsimp [b, b₀]; linarith : b₀ < b) hs
  have he : cepsDiscJet (cepsBandDiscBridgeWidthCoeff ν f β a l) 1 0 =ᶠ[𝓝 q]
      (fun z : ℂ => deriv (cepsBridgeSeries ν f β a z) l) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hq] with z hz
    exact (cepsBandDisc_bridge_width_hasDerivAt_series hD hθ hvlo hvhi hν hf hd hK
      (by linarith : 2 ≤ l) β ha (hbl.trans hz.le)).deriv.symm
  exact (cepsDiscJet_analyticAt (by omega : 1 ≤ 1) hM
    (by dsimp [b, b₀]; linarith : b < q.re) 0).congr he

end
end PGM
