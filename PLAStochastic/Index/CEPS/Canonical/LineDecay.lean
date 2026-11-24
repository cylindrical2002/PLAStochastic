import PLAStochastic.Index.CEPS.Canonical.LineBounds
import PLAStochastic.Index.CEPS.Family.Defs

/-!
# CEPS WP3, lemma C-3(c): line decay of `M₀` in the Sobolev class

For a density `f` in the exponentially weighted Sobolev class `CepsSobolevClass m η f` and
`|Re s| ≤ η`, integration by parts gives

  `s^k ∫ f(x) e^{s x} dx = (-1)^k ∫ f^{(k)}(x) e^{s x} dx`   (`k ≤ m`),

hence `‖s‖^k ‖∫ f e^{s x}‖ ≤ cepsSobolev m η f` (`norm_pow_mul_integral_cexp_le`). For a step law
`W` with density `f_W` this is the line decay `‖s‖^k ‖M₀(s)‖ ≤ ‖f_W‖_{m,η}`
(`norm_pow_mul_stepTransform_le`), and for `m ≥ 2` the decay hypothesis
`‖M₀(c + i y)‖ ≤ K/(1 + y²)` of the transport identity (`norm_stepTransform_line_le_of_sobolev`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Filter Topology
open PGM.WienerHopf

namespace PGM

section Generic

variable {m : ℕ} {η : ℝ} {f : ℝ → ℝ}

theorem norm_cexp_mul_ofReal_le {s : ℂ} (hs : |s.re| ≤ η) (x : ℝ) :
    ‖cexp (s * x)‖ ≤ Real.exp (η * |x|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have : (s * (x : ℂ)).re = s.re * x := by simp
  rw [this]
  calc s.re * x ≤ |s.re * x| := le_abs_self _
    _ = |s.re| * |x| := abs_mul _ _
    _ ≤ η * |x| := mul_le_mul_of_nonneg_right hs (abs_nonneg x)

theorem CepsSobolevClass.integrable_cexp (hf : CepsSobolevClass m η f) {s : ℂ}
    (hs : |s.re| ≤ η) {k : ℕ} (hk : k ≤ m) :
    Integrable (fun x : ℝ => ((iteratedDeriv k f x : ℝ) : ℂ) * cexp (s * x)) := by
  have hc : Continuous fun x : ℝ => ((iteratedDeriv k f x : ℝ) : ℂ) * cexp (s * x) :=
    (continuous_ofReal.comp (hf.continuous_iteratedDeriv hk)).mul (by fun_prop)
  refine (hf.integrable k hk).norm.mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_cexp_mul_ofReal_le hs x) (abs_nonneg _)

/-- **Integration by parts on a vertical line.** -/
theorem CepsSobolevClass.pow_mul_integral_cexp (hf : CepsSobolevClass m η f) {s : ℂ}
    (hs : |s.re| ≤ η) : ∀ k : ℕ, k ≤ m →
    s ^ k * ∫ x : ℝ, (f x : ℂ) * cexp (s * x) =
      (-1) ^ k * ∫ x : ℝ, ((iteratedDeriv k f x : ℝ) : ℂ) * cexp (s * x) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k ≤ m := by omega
    have hlt : (k : ℕ∞) < (m : ℕ∞) := by exact_mod_cast (show k < m by omega)
    have hdiff : Differentiable ℝ (iteratedDeriv k f) :=
      hf.contDiff.differentiable_iteratedDeriv k (by exact_mod_cast hlt)
    have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => ((iteratedDeriv k f x : ℝ) : ℂ))
        ((iteratedDeriv (k + 1) f x : ℝ) : ℂ) x := by
      intro x
      rw [iteratedDeriv_succ]
      exact (hdiff x).hasDerivAt.ofReal_comp
    have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (s * x)) (s * cexp (s * x)) x := by
      intro x
      have h := ((hasDerivAt_id (x : ℂ)).const_mul s).cexp.comp_ofReal
      simpa [mul_comm] using h
    have i1 : Integrable (fun x : ℝ => ((iteratedDeriv k f x : ℝ) : ℂ) * (s * cexp (s * x))) := by
      have := (hf.integrable_cexp hs hk').const_mul s
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only; ring
    have i2 := hf.integrable_cexp hs hk
    have i3 := hf.integrable_cexp hs hk'
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := fun x : ℝ => ((iteratedDeriv k f x : ℝ) : ℂ)) (v := fun x : ℝ => cexp (s * x))
      (u' := fun x : ℝ => ((iteratedDeriv (k + 1) f x : ℝ) : ℂ)) (v' := fun x : ℝ => s * cexp (s * x))
      (fun x _ => hu x) (fun x _ => hv x) i1 i2 i3
    have e1 : ∫ x : ℝ, ((iteratedDeriv k f x : ℝ) : ℂ) * (s * cexp (s * x)) =
        s * ∫ x : ℝ, ((iteratedDeriv k f x : ℝ) : ℂ) * cexp (s * x) := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [e1] at hibp
    rw [pow_succ, mul_comm (s ^ k) s, mul_assoc, ih hk', pow_succ]
    calc s * ((-1) ^ k * ∫ x : ℝ, ((iteratedDeriv k f x : ℝ) : ℂ) * cexp (s * x))
        = (-1) ^ k * (s * ∫ x : ℝ, ((iteratedDeriv k f x : ℝ) : ℂ) * cexp (s * x)) := by ring
      _ = _ := by rw [hibp]; ring

/-- `‖s‖^k ‖∫ f e^{s x}‖ ≤ ‖f‖_{m,η}` for `|Re s| ≤ η`, `k ≤ m`. -/
theorem CepsSobolevClass.norm_pow_mul_integral_cexp_le (hf : CepsSobolevClass m η f) {s : ℂ}
    (hs : |s.re| ≤ η) {k : ℕ} (hk : k ≤ m) :
    ‖s‖ ^ k * ‖∫ x : ℝ, (f x : ℂ) * cexp (s * x)‖ ≤ cepsSobolev m η f := by
  have h := hf.pow_mul_integral_cexp hs k hk
  rw [← norm_pow, ← norm_mul, h, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  calc ‖∫ x : ℝ, ((iteratedDeriv k f x : ℝ) : ℂ) * cexp (s * x)‖
      ≤ ∫ x : ℝ, ‖((iteratedDeriv k f x : ℝ) : ℂ) * cexp (s * x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, Real.exp (η * |x|) * |iteratedDeriv k f x| := by
        have hi : Integrable (fun x : ℝ => Real.exp (η * |x|) * |iteratedDeriv k f x|) := by
          refine (hf.integrable k hk).norm.congr (Eventually.of_forall fun x => ?_)
          simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        refine integral_mono (hf.integrable_cexp hs hk).norm hi fun x => ?_
        rw [norm_mul, norm_real, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (norm_cexp_mul_ofReal_le hs x) (abs_nonneg _)
    _ ≤ cepsSobolev m η f := by
        unfold cepsSobolev
        exact Finset.single_le_sum
          (f := fun r => ∫ x, Real.exp (η * |x|) * |iteratedDeriv r f x|)
          (fun _ _ => integral_nonneg fun _ => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))
          (Finset.mem_range.mpr (by omega))

end Generic

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ} {m : ℕ} {η : ℝ}

/-- **Line decay of `M₀`.** `‖s‖^k ‖M₀(s)‖ ≤ ‖f_W‖_{m,η}` for `|Re s| ≤ η`, `k ≤ m`. -/
theorem norm_pow_mul_stepTransform_le (hW : IsStepLaw ρW fW D θ v)
    (hf : CepsSobolevClass m η fW) {s : ℂ} (hs : |s.re| ≤ η) {k : ℕ} (hk : k ≤ m) :
    ‖s‖ ^ k * ‖stepTransform ρW s‖ ≤ cepsSobolev m η fW := by
  rw [stepTransform_eq_integral hW]
  have h := hf.norm_pow_mul_integral_cexp_le hs hk
  simpa only [mul_comm (cexp _)] using h

/-- For `m ≥ 2`: `‖M₀(c + i y)‖ ≤ 2 ‖f_W‖_{m,η}/(1 + y²)` for `|c| ≤ η`. This is the decay
hypothesis `hdec` of `CepsCanonDomain.cepsCanonL_transport`. -/
theorem norm_stepTransform_line_le_of_sobolev (hW : IsStepLaw ρW fW D θ v)
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) {c : ℝ} (hc : |c| ≤ η) (y : ℝ) :
    ‖stepTransform ρW (c + y * I)‖ ≤ 2 * cepsSobolev m η fW / (1 + y ^ 2) := by
  set s : ℂ := (c : ℂ) + y * I with hsdef
  have hsre : |s.re| ≤ η := by simpa [hsdef] using hc
  have h0 := norm_pow_mul_stepTransform_le hW hf hsre (Nat.zero_le m)
  have h2 := norm_pow_mul_stepTransform_le hW hf hsre hm
  have hy : y ^ 2 ≤ ‖s‖ ^ 2 := by
    have := abs_im_le_norm s
    have hsim : s.im = y := by simp [hsdef]
    rw [hsim] at this
    nlinarith [abs_nonneg y, sq_abs y]
  have hM := norm_nonneg (stepTransform ρW s)
  rw [le_div_iff₀ (by positivity)]
  rw [pow_zero, one_mul] at h0
  nlinarith [mul_le_mul_of_nonneg_right hy hM]

end PGM
