import PLAStochastic.ForMathlib.Analysis.Fourier.AngularInverse
import PLAStochastic.ForMathlib.Analysis.Fourier.BandBudget
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Integrable Fourier moment majorants -/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace PGM

def fourierMomentWeight (u : ℝ) : ℝ := ((1 + |u|) ^ 2)⁻¹

theorem integrable_fourierMomentWeight : Integrable fourierMomentWeight := by
  apply integrable_inv_one_add_sq.mono' (by unfold fourierMomentWeight; fun_prop)
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold fourierMomentWeight; positivity)]
    unfold fourierMomentWeight
    apply (inv_le_inv₀ (by positivity : 0 < (1 + |u|) ^ 2) (by positivity : 0 < 1 + u ^ 2)).mpr
    nlinarith [sq_abs u, abs_nonneg u]

theorem fourier_moment_le_majorant {ψ : ℝ → ℂ} {m r : ℕ} {C : ℝ}
    (hr : r ≤ m) (hb : ∀ u, (1 + |u|) ^ (m + 2) * ‖ψ u‖ ≤ C) (u : ℝ) :
    |u| ^ r * ‖ψ u‖ ≤ C * fourierMomentWeight u := by
  have hp : |u| ^ r ≤ (1 + |u|) ^ m :=
    (pow_le_pow_left₀ (abs_nonneg _) (by linarith) r).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg u]) hr)
  unfold fourierMomentWeight
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + |u|) ^ 2)).mpr
  calc
    _ ≤ ((1 + |u|) ^ m * ‖ψ u‖) * (1 + |u|) ^ 2 := by gcongr
    _ = (1 + |u|) ^ (m + 2) * ‖ψ u‖ := by rw [pow_add]; ring
    _ ≤ _ := hb u

theorem integrable_fourier_moment_of_bound {ψ : ℝ → ℂ} {m r : ℕ} {C : ℝ}
    (hψ : AEStronglyMeasurable ψ) (hr : r ≤ m)
    (hb : ∀ u, (1 + |u|) ^ (m + 2) * ‖ψ u‖ ≤ C) :
    Integrable (fun u : ℝ => |u| ^ r * ‖ψ u‖) ∧
      (∫ u : ℝ, |u| ^ r * ‖ψ u‖) ≤ C * ∫ u : ℝ, fourierMomentWeight u := by
  have hi := integrable_fourierMomentWeight.const_mul C
  have hbound := fourier_moment_le_majorant hr hb
  have hm : AEStronglyMeasurable (fun u : ℝ => |u| ^ r * ‖ψ u‖) :=
    (by fun_prop : Continuous fun u : ℝ => |u| ^ r).aestronglyMeasurable.mul hψ.norm
  have hI : Integrable (fun u : ℝ => |u| ^ r * ‖ψ u‖) :=
    hi.mono' hm (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbound u)
  refine ⟨hI, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hI hi hbound

/-- A rescaled moment estimate directly bounds derivatives of angular inversion. -/
theorem norm_deriv_angularInverse_of_bound {ψ : ℝ → ℂ} {m r : ℕ} {C : ℝ}
    (hψ : AEStronglyMeasurable ψ) (_hC : 0 ≤ C) (hr : r ≤ m)
    (hb : ∀ u, (1 + |u|) ^ (m + 2) * ‖ψ u‖ ≤ C) (x : ℝ) :
    ‖iteratedDeriv r (angularInverse ψ) x‖ ≤
      (2 * Real.pi) ^ r * C * ∫ u : ℝ, fourierMomentWeight (2 * Real.pi * u) := by
  have hm : ∀ j ≤ m, Integrable (fun u : ℝ => |u| ^ j * ‖ψ u‖) :=
    fun j hj => (integrable_fourier_moment_of_bound hψ hj hb).1
  refine (norm_iteratedDeriv_angularInverse_le hψ hm hr x).trans ?_
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hw := (integrable_fourierMomentWeight.comp_mul_left' hc).const_mul C
  have hmi := (integrable_angular_rescale_pow hψ (hm r hr)).norm
  have hbound (u : ℝ) : |u| ^ r * ‖ψ (2 * Real.pi * u)‖ ≤ C * fourierMomentWeight (2 * Real.pi * u) := by
    have hp : |u| ≤ |2 * Real.pi * u| := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      nlinarith [Real.pi_gt_three, abs_nonneg u]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hp r) (norm_nonneg _)).trans
      (fourier_moment_le_majorant hr hb (2 * Real.pi * u))
  have hi : Integrable (fun u : ℝ => |u| ^ r * ‖ψ (2 * Real.pi * u)‖) := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_pow] using hmi
  have hle := integral_mono hi hw hbound
  rw [integral_const_mul] at hle
  exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans_eq (by ring)

theorem FourierBandEstimates.coefficient_moment_bound {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    (h : FourierBandEstimates φ a) (m k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, (1 + |u|) ^ (m + 2) * ‖a k u‖ ≤ C := by
  obtain ⟨δ, -, -, c, U, K, hc, -, -, d, -, ha⟩ := h.delta
  obtain ⟨B, hB, hb⟩ := finite_stretchedExp_moment_bound hc ha (m + 2) k
  refine ⟨B, hB, fun u => ?_⟩
  have hsingle : (1 + |u|) ^ (m + 2) * ‖a k u‖ ≤
      ∑ j ∈ range (k + 1), (1 + |u|) ^ (m + 2) * ‖a j u‖ :=
    by
      apply single_le_sum (f := fun j : ℕ => (1 + |u|) ^ (m + 2) * ‖a j u‖) (a := k)
      · intro j hj; positivity
      · exact mem_range.mpr (Nat.lt_succ_self k)
  have hex : Real.exp (-(c / 2) * Real.sqrt |u|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.sqrt_nonneg |u|])
  exact (hsingle.trans (hb u)).trans ((mul_le_mul_of_nonneg_left hex hB).trans_eq (mul_one _))

theorem FourierBandEstimates.actual_moment_bound {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    (h : FourierBandEstimates φ a) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ eps in atTop, ∀ u : ℝ,
      (1 + |u|) ^ (m + 2) * ‖φ eps u‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := h.remainder_moment_bound m 0
  obtain ⟨B, hB, ha⟩ := h.coefficient_moment_bound m 0
  refine ⟨C + B, by positivity, ?_⟩
  filter_upwards [hb] with eps he u
  simp only [Nat.zero_add, sum_range_one, pow_zero, one_smul, mul_one] at he
  have htri := mul_le_mul_of_nonneg_left (norm_sub_le (φ eps u - a 0 u) (-a 0 u))
    (by positivity : 0 ≤ (1 + |u|) ^ (m + 2))
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
  rw [mul_add] at htri
  exact htri.trans (add_le_add (he u) (ha u))

end PGM
