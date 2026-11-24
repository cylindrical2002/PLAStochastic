import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Transfer of first derivatives between close functions

Two functions with a common value at `0`, close at one point `τ` and with second-order Taylor
remainders of size `M ‖τ‖²` have first derivatives within `δ/‖τ‖ + M ‖τ‖` of each other.

* `norm_sub_le_of_taylor_close`: the one-point transfer for complex increments `τ`;
* `norm_sub_sub_smul_le_of_deriv2`: `‖f x - f 0 - x f'(0)‖ ≤ M x²/2` on `[0, a]` when
  `‖f''‖ ≤ M` there;
* `norm_deriv_sub_le_two_sqrt`: the Landau–Kolmogorov transfer `‖g'(0) - ĝ'(0)‖ ≤ 2√(δM)` for
  `g(0) = ĝ(0)`, `‖g - ĝ‖ ≤ δ` and `‖g''‖, ‖ĝ''‖ ≤ M` on `[0, a]`, `δ ≤ M a²`;
* `norm_cexp_neg_I_mul_sub_le`, `norm_integral_cexp_sub_le`: the first-order Taylor bound
  `‖E e^{-iyX} - 1 + iy E X‖ ≤ y² E X²` of a characteristic function.
-/

namespace PGM

noncomputable section

open Set MeasureTheory Filter

/-- **One-point transfer of first derivatives.** If `G` and `Ĝ` are `δ`-close and both have
second-order Taylor remainders `M ‖τ‖²` around the common value `G₀`, their derivatives along
`τ` differ by at most `δ/‖τ‖ + (M₁ + M₂) ‖τ‖`. -/
theorem norm_sub_le_of_taylor_close {G Ĝ G₀ τ D D' : ℂ} {δ M₁ M₂ : ℝ} (hτ : τ ≠ 0)
    (hclose : ‖G - Ĝ‖ ≤ δ) (hG : ‖G - G₀ - τ * D‖ ≤ M₁ * ‖τ‖ ^ 2)
    (hĜ : ‖Ĝ - G₀ - τ * D'‖ ≤ M₂ * ‖τ‖ ^ 2) :
    ‖D - D'‖ ≤ δ / ‖τ‖ + (M₁ + M₂) * ‖τ‖ := by
  have hτn : 0 < ‖τ‖ := norm_pos_iff.mpr hτ
  have e : τ * (D - D') = (Ĝ - G₀ - τ * D') - (G - G₀ - τ * D) + (G - Ĝ) := by ring
  have h1 : ‖τ‖ * ‖D - D'‖ ≤ M₂ * ‖τ‖ ^ 2 + M₁ * ‖τ‖ ^ 2 + δ := by
    rw [← norm_mul, e]
    calc ‖(Ĝ - G₀ - τ * D') - (G - G₀ - τ * D) + (G - Ĝ)‖
        ≤ ‖(Ĝ - G₀ - τ * D') - (G - G₀ - τ * D)‖ + ‖G - Ĝ‖ := norm_add_le _ _
      _ ≤ (‖Ĝ - G₀ - τ * D'‖ + ‖G - G₀ - τ * D‖) + ‖G - Ĝ‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ _ := by linarith
  rw [div_add' _ _ _ hτn.ne', le_div_iff₀ hτn]
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Second-order Taylor bound** on `[0, a]` from `‖f''‖ ≤ M`. -/
theorem norm_sub_sub_smul_le_of_deriv2 {f f' f'' : ℝ → E} {a M : ℝ}
    (hf : ∀ x ∈ Icc 0 a, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc 0 a, HasDerivAt f' (f'' x) x) (hM : ∀ x ∈ Icc 0 a, ‖f'' x‖ ≤ M)
    {x : ℝ} (hx : x ∈ Icc 0 a) :
    ‖f x - f 0 - x • f' 0‖ ≤ M / 2 * x ^ 2 := by
  -- the first derivative moves by at most `M t`
  have h1 : ∀ t ∈ Icc 0 a, ‖f' t - f' 0‖ ≤ M * t := by
    intro t ht
    have hsub : Icc 0 t ⊆ Icc 0 a := Icc_subset_Icc le_rfl ht.2
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f') (f' := f'') (a := 0) (b := t)
      (C := M) (fun y hy => (hf' y (hsub hy)).hasDerivWithinAt)
      (fun y hy => hM y (hsub (Ico_subset_Icc_self hy))) t (right_mem_Icc.2 ht.1)
    simpa using this
  have hsub : Icc 0 x ⊆ Icc 0 a := Icc_subset_Icc le_rfl hx.2
  have hφ : ∀ t ∈ Icc 0 x, HasDerivAt (fun s => f s - f 0 - s • f' 0) (f' t - f' 0) t := by
    intro t ht
    have := ((hf t (hsub ht)).sub_const (f 0)).sub ((hasDerivAt_id' t).smul_const (f' 0))
    rw [one_smul] at this
    exact this
  have hB : ∀ t, HasDerivAt (fun s : ℝ => M / 2 * s ^ 2) (M * t) t := by
    intro t
    refine ((hasDerivAt_pow 2 t).const_mul (M / 2)).congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun s => f s - f 0 - s • f' 0) (f' := fun t => f' t - f' 0) (B := fun s => M / 2 * s ^ 2)
    (B' := fun t => M * t) (a := 0) (b := x)
    (fun t ht => (hφ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hφ t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (by simp) hB
    (fun t ht => h1 t (hsub (Ico_subset_Icc_self ht))) (right_mem_Icc.2 hx.1)

/-- **Landau–Kolmogorov transfer.** If `g(0) = ĝ(0)`, `‖g - ĝ‖ ≤ δ` on `[0, a]` and both second
derivatives are bounded by `M` there, then `‖g'(0) - ĝ'(0)‖ ≤ 2 √(δ M)` provided `δ ≤ M a²`. -/
theorem norm_deriv_sub_le_two_sqrt {g g' g'' ĝ ĝ' ĝ'' : ℝ → E} {a δ M : ℝ} (ha : 0 < a)
    (hg : ∀ x ∈ Icc 0 a, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Icc 0 a, HasDerivAt g' (g'' x) x)
    (hĝ : ∀ x ∈ Icc 0 a, HasDerivAt ĝ (ĝ' x) x) (hĝ' : ∀ x ∈ Icc 0 a, HasDerivAt ĝ' (ĝ'' x) x)
    (hM : ∀ x ∈ Icc 0 a, ‖g'' x‖ ≤ M) (hM' : ∀ x ∈ Icc 0 a, ‖ĝ'' x‖ ≤ M)
    (h0 : g 0 = ĝ 0) (hclose : ∀ x ∈ Icc 0 a, ‖g x - ĝ x‖ ≤ δ) (hδ : 0 < δ)
    (hfit : δ ≤ M * a ^ 2) :
    ‖g' 0 - ĝ' 0‖ ≤ 2 * Real.sqrt (δ * M) := by
  have hMpos : 0 < M := by
    by_contra hM0
    push Not at hM0
    nlinarith [sq_nonneg a]
  set q := Real.sqrt (δ * M) with hq
  have hqpos : 0 < q := Real.sqrt_pos.2 (mul_pos hδ hMpos)
  have hq2 : q ^ 2 = δ * M := Real.sq_sqrt (mul_pos hδ hMpos).le
  set x := q / M with hxdef
  have hxpos : 0 < x := div_pos hqpos hMpos
  have hx2 : x ^ 2 = δ / M := by
    rw [hxdef, div_pow, hq2]
    field_simp
  have hxa : x ≤ a := by
    have h1 : x ^ 2 ≤ a ^ 2 := by
      rw [hx2, div_le_iff₀ hMpos]
      linarith
    exact (pow_le_pow_iff_left₀ hxpos.le ha.le two_ne_zero).1 h1
  have hxI : x ∈ Icc 0 a := ⟨hxpos.le, hxa⟩
  have t1 := norm_sub_sub_smul_le_of_deriv2 hg hg' hM hxI
  have t2 := norm_sub_sub_smul_le_of_deriv2 hĝ hĝ' hM' hxI
  have e : x • (g' 0 - ĝ' 0) = (ĝ x - ĝ 0 - x • ĝ' 0) - (g x - g 0 - x • g' 0) +
      (g x - ĝ x) + (ĝ 0 - g 0) := by
    rw [smul_sub]
    abel
  have t1' : ‖g x - ĝ 0 - x • g' 0‖ ≤ M / 2 * x ^ 2 := by rw [← h0]; exact t1
  have hmain : x * ‖g' 0 - ĝ' 0‖ ≤ M * x ^ 2 + δ := by
    have hn : ‖x • (g' 0 - ĝ' 0)‖ = x * ‖g' 0 - ĝ' 0‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hxpos]
    rw [← hn, e, h0, sub_self, add_zero]
    calc ‖(ĝ x - ĝ 0 - x • ĝ' 0) - (g x - ĝ 0 - x • g' 0) + (g x - ĝ x)‖
        ≤ ‖(ĝ x - ĝ 0 - x • ĝ' 0) - (g x - ĝ 0 - x • g' 0)‖ + ‖g x - ĝ x‖ := norm_add_le _ _
      _ ≤ (‖ĝ x - ĝ 0 - x • ĝ' 0‖ + ‖g x - ĝ 0 - x • g' 0‖) + ‖g x - ĝ x‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ (M / 2 * x ^ 2 + M / 2 * x ^ 2) + δ :=
          add_le_add (add_le_add t2 t1') (hclose x hxI)
      _ = M * x ^ 2 + δ := by ring
  have hgoal : x * (2 * q) = M * x ^ 2 + δ := by
    rw [hx2, hxdef]
    field_simp
    nlinarith [hq2]
  have := hmain.trans hgoal.ge
  exact le_of_mul_le_mul_left this hxpos

/-! ## The characteristic-function Taylor bound -/

/-- `‖e^{-iθ} - 1 + iθ‖ ≤ θ²`. -/
theorem norm_cexp_neg_I_mul_sub_le (θ : ℝ) :
    ‖Complex.exp (-(Complex.I * θ)) - 1 + Complex.I * θ‖ ≤ θ ^ 2 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(Complex.I * t)) - 1 + Complex.I * t)
      (-Complex.I * Complex.exp (-(Complex.I * t)) + Complex.I) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have h2 := (((h1.const_mul Complex.I).neg).cexp.sub_const 1).add (h1.const_mul Complex.I)
    exact h2.congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hb : ∀ t ∈ uIcc 0 θ,
      ‖-Complex.I * Complex.exp (-(Complex.I * t)) + Complex.I‖ ≤ |θ| := by
    intro t ht
    have e : -Complex.I * Complex.exp (-(Complex.I * t)) + Complex.I =
        -Complex.I * (Complex.exp (Complex.I * ((-t : ℝ) : ℂ)) - 1) := by
      rw [show Complex.I * ((-t : ℝ) : ℂ) = -(Complex.I * t) by push_cast; ring]
      ring
    rw [e, norm_mul, norm_neg, Complex.norm_I, one_mul]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
    rw [Real.norm_eq_abs, abs_neg]
    simpa using abs_sub_left_of_mem_uIcc ht
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hb (convex_uIcc 0 θ) left_mem_uIcc right_mem_uIcc
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, sub_self, add_zero,
    sub_zero, Real.norm_eq_abs] at hmvt
  calc _ ≤ |θ| * |θ| := hmvt
    _ = θ ^ 2 := by rw [← abs_mul, abs_mul_self, sq]

/-- **First-order Taylor bound of a characteristic function**:
`‖E e^{-iyX} - 1 - (iy)(-E X)‖ ≤ ‖iy‖² E X²`. -/
theorem norm_integral_cexp_sub_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Integrable X P)
    (hX2 : Integrable (fun ω => X ω ^ 2) P) (y : ℝ) :
    ‖(∫ ω, Complex.exp (-(Complex.I * y) * X ω) ∂P) - 1 -
        Complex.I * y * (-((∫ ω, X ω ∂P : ℝ) : ℂ))‖ ≤
      ‖Complex.I * (y : ℂ)‖ ^ 2 * ∫ ω, X ω ^ 2 ∂P := by
  have hm : AEStronglyMeasurable (fun ω => Complex.exp (-(Complex.I * y) * X ω)) P :=
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (-(Complex.I * y) * x)).comp_aestronglyMeasurable
      hX.1
  have hexp : Integrable (fun ω => Complex.exp (-(Complex.I * y) * X ω)) P := by
    refine Integrable.of_bound hm 1 (Eventually.of_forall fun ω => ?_)
    rw [Complex.norm_exp]
    simp
  have hXc : Integrable (fun ω => Complex.I * y * (X ω : ℂ)) P := hX.ofReal.const_mul _
  have e : (∫ ω, Complex.exp (-(Complex.I * y) * X ω) ∂P) - 1 -
      Complex.I * y * (-((∫ ω, X ω ∂P : ℝ) : ℂ)) =
      ∫ ω, (Complex.exp (-(Complex.I * y) * X ω) - 1 + Complex.I * y * (X ω : ℂ)) ∂P := by
    rw [integral_add (f := fun ω => Complex.exp (-(Complex.I * y) * X ω) - 1)
      (hexp.sub (integrable_const 1)) hXc,
      integral_sub (f := fun ω => Complex.exp (-(Complex.I * y) * X ω)) (g := fun _ => (1 : ℂ))
        hexp (integrable_const 1), integral_const_mul, integral_complex_ofReal]
    simp
  rw [e]
  have hnI : ‖Complex.I * (y : ℂ)‖ ^ 2 = y ^ 2 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnI, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hX2.const_mul _) (Eventually.of_forall fun ω => ?_)
  have e2 : Complex.exp (-(Complex.I * y) * X ω) - 1 + Complex.I * y * (X ω : ℂ) =
      Complex.exp (-(Complex.I * ((y * X ω : ℝ) : ℂ))) - 1 + Complex.I * ((y * X ω : ℝ) : ℂ) := by
    push_cast
    ring_nf
  rw [e2]
  calc _ ≤ (y * X ω) ^ 2 := norm_cexp_neg_I_mul_sub_le _
    _ = y ^ 2 * X ω ^ 2 := by ring

end

end PGM
