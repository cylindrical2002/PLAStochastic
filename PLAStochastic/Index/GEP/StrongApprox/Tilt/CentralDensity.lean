import PLAStochastic.Index.GEP.StrongApprox.Tilt.Recentered

/-! # Uniform relative and logarithmic central-density errors for tilted sums -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Real

/-- The ratio of the actual central density to its matching Gaussian central density. -/
def saTiltCentralFactor (ν : ProbabilityMeasure ℝ) (lam h : ℝ) (l : ℕ) : ℝ :=
  Real.sqrt (2 * π *
    (iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam + h ^ 2)) *
  saGaussianDensity ((convPow (saRecenteredTilt ν lam) l).map ((Real.sqrt l)⁻¹ * ·))
    (Real.toNNReal (h ^ 2)) 0

/-- Near one, a relative error controls the logarithmic error. -/
theorem abs_log_le_two_mul_abs_sub_one {r : ℝ} (hr : |r - 1| ≤ 1 / 2) :
    |Real.log r| ≤ 2 * |r - 1| := by
  have hrl : 1 / 2 ≤ r := by linarith [(abs_le.mp hr).1]
  have hr0 : 0 < r := by linarith
  have hinv : r⁻¹ - 1 ≤ 2 * |r - 1| := by
    apply (mul_le_mul_iff_left₀ hr0).mp
    rw [sub_mul, inv_mul_cancel₀ hr0.ne', one_mul]
    nlinarith [abs_nonneg (r - 1), neg_abs_le (r - 1)]
  apply abs_le.mpr
  constructor
  · linarith [Real.one_sub_inv_le_log_of_pos hr0]
  · linarith [Real.log_le_sub_one_of_pos hr0, le_abs_self (r - 1), abs_nonneg (r - 1)]

/-- An absolute central-density error yields a relative error with a variance upper bound. -/
theorem central_gaussian_relative_error {q v V C r : ℝ} (hv : 0 < v) (hV : v ≤ V)
    (hC : 0 ≤ C) (hr : 0 < r)
    (hq : |q - gaussianPDFReal 0 (Real.toNNReal v) 0| ≤ C / r) :
    |Real.sqrt (2 * π * v) * q - 1| ≤ (Real.sqrt (2 * π * V) * C) / r := by
  have hs : 0 < Real.sqrt (2 * π * v) := Real.sqrt_pos.mpr (by positivity)
  have hg : gaussianPDFReal 0 (Real.toNNReal v) 0 = (Real.sqrt (2 * π * v))⁻¹ := by
    rw [gaussianPDFReal, Real.coe_toNNReal _ hv.le]
    simp
  have he : Real.sqrt (2 * π * v) * q - 1 =
      Real.sqrt (2 * π * v) * (q - gaussianPDFReal 0 (Real.toNNReal v) 0) := by
    rw [hg, mul_sub, mul_inv_cancel₀ hs.ne']
  rw [he, abs_mul, abs_of_pos hs]
  calc
    _ ≤ Real.sqrt (2 * π * v) * (C / r) := mul_le_mul_of_nonneg_left hq hs.le
    _ ≤ Real.sqrt (2 * π * V) * (C / r) := mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hV (by positivity))) (by positivity)
    _ = _ := by ring

/-- Uniform absolute density bounds become uniform central relative errors for `h ≤ 1`. -/
theorem exists_uniform_saTiltCentralFactor
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ lam : ℝ, |lam| ≤ saTiltRadius vlo B θ → ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ l : ℕ, 2 ≤ l → 1 / h ≤ (l : ℝ) ^ 8 →
        |saTiltCentralFactor ν lam h l - 1| ≤ C / Real.sqrt l := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_saRecenteredTilt_density vlo vhi κ₃ B θ D c
    hvlo hvhi hB hθ hD hc
  refine ⟨Real.sqrt (2 * π * (5 / 4 * vhi + 1)) * C, by positivity, ?_⟩
  intro ν hν hs lam hlam h hh hh1 l hl hscale
  have hvar := hν.centered_cgf_variance_bracket hvlo hθ hlam
  have hv : 0 < iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam + h ^ 2 := by
    linarith [hν.var_ge, sq_nonneg h]
  have hV : iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam + h ^ 2 ≤
      5 / 4 * vhi + 1 := by nlinarith [hν.var_le]
  have hr : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < l by omega))
  exact central_gaussian_relative_error hv hV hC.le hr
    (hbound ν hν hs lam hlam h hh l hl hscale 0)

/-- Beyond a class-uniform block length, the central log-prefactor is `O(l⁻¹/²)`. -/
theorem exists_uniform_saTiltCentralLog
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ lam : ℝ, |lam| ≤ saTiltRadius vlo B θ → ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ l : ℕ, 2 ≤ l → 1 / h ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
        0 < saTiltCentralFactor ν lam h l ∧
        |Real.log (saTiltCentralFactor ν lam h l)| ≤ (2 * C) / Real.sqrt l := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_saTiltCentralFactor vlo vhi κ₃ B θ D c
    hvlo hvhi hB hθ hD hc
  refine ⟨C, hC, ?_⟩
  intro ν hν hs lam hlam h hh hh1 l hl hscale hlarge
  have hb := hbound ν hν hs lam hlam h hh hh1 l hl hscale
  have hr : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < l by omega))
  have hhf : |saTiltCentralFactor ν lam h l - 1| ≤ 1 / 2 := by
    apply hb.trans
    rw [div_le_iff₀ hr]
    linarith
  constructor
  · linarith [(abs_le.mp hhf).1]
  · apply (abs_log_le_two_mul_abs_sub_one hhf).trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)

end

end PGM
