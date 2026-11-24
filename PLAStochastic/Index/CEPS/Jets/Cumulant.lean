import PLAStochastic.Index.CEPS.Jets.Basic
import PLAStochastic.ForMathlib.Analysis.Asymptotics.SeriesExpansion
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Probability.Moments.ComplexMGF

/-!
# X8: cumulants of the step law and their expansions along families

* `iteratedDeriv_mul_of_differentiableOn`: the Leibniz rule for iterated complex derivatives of
  a product of functions holomorphic on an open set;
* `iteratedDeriv_log_eq_cepsCumRec`: if `M` is holomorphic on `B(0, r)` with `M 0 = 1` and values
  in the slit plane, the derivatives of `log M` at `0` are the cumulants `cepsCumRec` of the
  derivatives of `M` at `0` (from `M' = M · (log M)'` and the Leibniz rule);
* `integral_pow_stepLaw_eq_cepsJetMoment`, `iteratedDeriv_stepTransform_zero_eq`,
  `iteratedDeriv_cepsCgf_zero_eq`: for a step law of `W = 1 - X` with `f_W(y) = f(1 - y)`, the
  moments `E W^k` are `cepsJetMoment f k`, the derivatives of `M₀ = stepTransform ρW` at `0` are
  these moments, and the derivatives of `ψ₀ = cepsCgf ρW` at `0` are the cumulants
  `cepsCumulant f k`;
* `cepsMomentSeries`, `cepsCumSeries`: the moment series of a family of densities (constant term
  from the reference density `cepsLambdaDensity`) and the cumulant recursion applied to it in the
  ring of formal power series; `coeff_cepsCumSeries_congr` (the coefficient of order `n` reads
  only the members `1, …, n` of the family), `coeff_zero_cepsCumSeries` (constant term: the
  reference cumulant), and `cepsCumulant_hasSeriesExpansion` (moment expansions of order `P`
  through `K` give cumulant expansions of order `P` with the cumulant series).
-/

noncomputable section

open MeasureTheory Complex Filter

namespace PGM

/-! ## The Leibniz rule and the logarithm -/

/-- The Leibniz rule for iterated complex derivatives on an open set. -/
theorem iteratedDeriv_mul_of_differentiableOn {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (n : ℕ) {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv n (fun w => f w * g w) z =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℂ) * iteratedDeriv k f z * iteratedDeriv (n - k) g z :=
  iteratedDeriv_fun_mul ((hf.contDiffOn hU).contDiffAt (hU.mem_nhds hz))
    ((hg.contDiffOn hU).contDiffAt (hU.mem_nhds hz))

/-- The derivatives at `0` of `log M` are the cumulants of the derivatives of `M` at `0`. -/
theorem iteratedDeriv_log_eq_cepsCumRec {M : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hM : DifferentiableOn ℂ M (Metric.ball 0 r)) (hM0 : M 0 = 1)
    (hslit : ∀ z ∈ Metric.ball (0 : ℂ) r, M z ∈ Complex.slitPlane) (n : ℕ) :
    iteratedDeriv n (fun z => Complex.log (M z)) 0 =
      cepsCumRec (fun k => iteratedDeriv k M 0) n := by
  set L : ℂ → ℂ := fun z => Complex.log (M z) with hLdef
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  have hLd : ∀ z ∈ Metric.ball (0 : ℂ) r, HasDerivAt L (deriv M z / M z) z := fun z hz =>
    ((hM z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt.clog (hslit z hz)
  have hL : DifferentiableOn ℂ L (Metric.ball 0 r) := fun z hz =>
    (hLd z hz).differentiableAt.differentiableWithinAt
  have hev : deriv M =ᶠ[nhds 0] fun w => M w * deriv L w := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with w hw
    rw [(hLd w hw).deriv, mul_div_cancel₀ _ (Complex.slitPlane_ne_zero (hslit w hw))]
  -- `M^{(n+1)}(0) = ∑_{j ≤ n} C(n, j) L^{(j+1)}(0) M^{(n-j)}(0)`
  have key : ∀ n : ℕ, iteratedDeriv (n + 1) M 0 =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * iteratedDeriv (j + 1) L 0 * iteratedDeriv (n - j) M 0 := by
    intro n
    rw [iteratedDeriv_succ', hev.iteratedDeriv_eq n,
      iteratedDeriv_mul_of_differentiableOn Metric.isOpen_ball hM
        (hL.deriv Metric.isOpen_ball) n h0, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega,
      Nat.choose_symm (by omega), ← iteratedDeriv_succ']
    ring
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [cepsCumRec_zero, hLdef, hM0]
    · have hs : ∑ k ∈ Finset.range n, (n.choose k : ℂ) *
            cepsCumRec (fun k => iteratedDeriv k M 0) (k + 1) * iteratedDeriv (n - k) M 0 =
          ∑ k ∈ Finset.range n, (n.choose k : ℂ) * iteratedDeriv (k + 1) L 0 *
            iteratedDeriv (n - k) M 0 :=
        Finset.sum_congr rfl fun k hk => by
          rw [ih (k + 1) (by have := Finset.mem_range.mp hk; omega)]
      rw [cepsCumRec_succ, hs, key n, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self,
        iteratedDeriv_zero, hM0]
      ring

/-! ## Moments and cumulants of the step law -/

/-- The moments of a step law of `W = 1 - X` are the jet moments of the density of `X`. -/
theorem integral_pow_stepLaw_eq_cepsJetMoment {ρW : Measure ℝ} {fW f : ℝ → ℝ}
    {D θ v : ℝ} (hW : WienerHopf.IsStepLaw ρW fW D θ v) (hfW : ∀ y, fW y = f (1 - y)) (k : ℕ) :
    ∫ y, y ^ k ∂ρW = cepsJetMoment f k := by
  rw [hW.eq_withDensity, integral_withDensity_eq_integral_toReal_smul
      (f := fun x => ENNReal.ofReal (fW x)) (ENNReal.measurable_ofReal.comp hW.measurable)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), cepsJetMoment,
    ← integral_sub_left_eq_self (fun x => (1 - x) ^ k * f x) volume 1]
  congr 1; funext y
  rw [ENNReal.toReal_ofReal (hW.nonneg y), smul_eq_mul, hfW y, sub_sub_cancel]
  ring

section StepLaw

variable {ρW : Measure ℝ} {fW f : ℝ → ℝ} {D θ v : ℝ}

/-- The derivatives at `0` of the step transform are the jet moments. -/
theorem iteratedDeriv_stepTransform_zero_eq (hW : WienerHopf.IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) (hfW : ∀ y, fW y = f (1 - y)) (k : ℕ) :
    iteratedDeriv k (WienerHopf.stepTransform ρW) 0 = (cepsJetMoment f k : ℂ) := by
  have h := ProbabilityTheory.iteratedDeriv_complexMGF (X := id) (μ := ρW) (z := 0)
    (stepLaw_mem_interior_integrableExpSet hW hθ hD.le (by simp; positivity)) k
  have e : ∫ y : ℝ, ((y ^ k : ℝ) : ℂ) ∂ρW = ((∫ y, y ^ k ∂ρW : ℝ) : ℂ) := integral_ofReal
  rw [show WienerHopf.stepTransform ρW = ProbabilityTheory.complexMGF id ρW from rfl, h,
    ← integral_pow_stepLaw_eq_cepsJetMoment hW hfW k, ← e]
  simp

/-- The derivatives at `0` of the cumulant generating function are the cumulants. -/
theorem iteratedDeriv_cepsCgf_zero_eq (hW : WienerHopf.IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) (hfW : ∀ y, fW y = f (1 - y)) (k : ℕ) :
    iteratedDeriv k (cepsCgf ρW) 0 = (cepsCumulant f k : ℂ) := by
  have hr := cepsCgfRadius_pos hD hθ
  have hM : DifferentiableOn ℂ (WienerHopf.stepTransform ρW)
      (Metric.ball 0 (cepsCgfRadius D θ)) :=
    (differentiableOn_stepTransform_ball hW hθ hD.le).mono
      (Metric.ball_subset_ball (by linarith [cepsCgfRadius_le (D := D) (θ := θ)]))
  have h := iteratedDeriv_log_eq_cepsCumRec hr hM (stepTransform_zero hW)
    (fun z hz => stepTransform_mem_slitPlane hW hθ hD
      (by rw [Metric.mem_ball, dist_zero_right] at hz; exact hz.le)) k
  have hm : (fun j => iteratedDeriv j (WienerHopf.stepTransform ρW) 0) =
      fun j => Complex.ofRealHom (cepsJetMoment f j) :=
    funext fun j => iteratedDeriv_stepTransform_zero_eq hW hθ hD hfW j
  rw [hm, ← map_cepsCumRec] at h
  exact h

end StepLaw

/-! ## Cumulant series along families -/

/-- The moment series of a family: constant term from the reference density `cepsLambdaDensity`,
`n`-th coefficient the moment of `g n`. -/
def cepsMomentSeries (g : ℕ → ℝ → ℝ) (k : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun n =>
    if n = 0 then cepsJetMoment cepsLambdaDensity k else cepsJetMoment (g n) k

/-- The cumulant series: the cumulant recursion applied in the ring of power series. -/
def cepsCumSeries (g : ℕ → ℝ → ℝ) (k : ℕ) : PowerSeries ℝ := cepsCumRec (cepsMomentSeries g) k

/-- The coefficient of order `n` of a cumulant series reads only the members `1, …, n`. -/
theorem coeff_cepsCumSeries_congr {g g' : ℕ → ℝ → ℝ} {n : ℕ}
    (h : ∀ j, 1 ≤ j → j ≤ n → g j = g' j) (k : ℕ) :
    PowerSeries.coeff n (cepsCumSeries g k) = PowerSeries.coeff n (cepsCumSeries g' k) := by
  set I : Ideal (PowerSeries ℝ) := Ideal.span {PowerSeries.X ^ (n + 1)}
  have hmem : ∀ F G : PowerSeries ℝ, Ideal.Quotient.mk I F = Ideal.Quotient.mk I G ↔
      ∀ i ≤ n, PowerSeries.coeff i F = PowerSeries.coeff i G := by
    intro F G
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    simp only [map_sub, sub_eq_zero, Nat.lt_add_one_iff]
  have hm : (fun j => Ideal.Quotient.mk I (cepsMomentSeries g j)) =
      fun j => Ideal.Quotient.mk I (cepsMomentSeries g' j) := by
    funext j
    rw [hmem]
    intro i hi
    simp only [cepsMomentSeries, PowerSeries.coeff_mk]
    split_ifs with hi0
    · rfl
    · rw [h i (by omega) hi]
  have hc : Ideal.Quotient.mk I (cepsCumSeries g k) = Ideal.Quotient.mk I (cepsCumSeries g' k) := by
    rw [cepsCumSeries, cepsCumSeries, map_cepsCumRec, map_cepsCumRec, hm]
  exact (hmem _ _).mp hc n le_rfl

/-- The constant term of a cumulant series is the reference cumulant. -/
theorem coeff_zero_cepsCumSeries (g : ℕ → ℝ → ℝ) (k : ℕ) :
    PowerSeries.coeff 0 (cepsCumSeries g k) = cepsCumulant cepsLambdaDensity k := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, cepsCumSeries, map_cepsCumRec,
    cepsCumulant]
  congr 1

/-- Moment expansions of order `P` through `K` give the cumulant expansions of order `P` through
`K`, with the cumulant series as coefficients. -/
theorem cepsCumulant_hasSeriesExpansion {f : ℝ → ℝ → ℝ} {g : ℕ → ℝ → ℝ} {P K : ℕ}
    (hm : ∀ k, 1 ≤ k → k ≤ K → HasSeriesExpansionAtOrder (fun eps => cepsJetMoment (f eps) k)
      (cepsMomentSeries g k) P) :
    ∀ k ≤ K, HasSeriesExpansionAtOrder (fun eps => cepsCumulant (f eps) k)
      (cepsCumSeries g k) P := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases k with _ | n
    · have e1 : (fun eps => cepsCumulant (f eps) 0) = fun _ => (0 : ℝ) :=
        funext fun _ => cepsCumRec_zero _
      have e2 : cepsCumSeries g 0 = PowerSeries.C (0 : ℝ) :=
        (cepsCumRec_zero _).trans (map_zero _).symm
      rw [e1, e2]
      exact hasSeriesExpansionAtOrder_const 0 P
    · have hsum : HasSeriesExpansionAtOrder
          (fun eps => ∑ j ∈ Finset.range n,
            (n.choose j : ℝ) * cepsCumulant (f eps) (j + 1) * cepsJetMoment (f eps) (n - j))
          (∑ j ∈ Finset.range n,
            (n.choose j : PowerSeries ℝ) * cepsCumSeries g (j + 1) * cepsMomentSeries g (n - j))
          P := by
        refine HasSeriesExpansionAtOrder.sum _ fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        have hc := hasSeriesExpansionAtOrder_const (n.choose j : ℝ) P
        rw [map_natCast] at hc
        exact (hc.mul (ih (j + 1) (by omega) (by omega))).mul (hm (n - j) (by omega) (by omega))
      have h := (hm (n + 1) (by omega) hk).sub hsum
      have e1 : (fun eps => cepsCumulant (f eps) (n + 1)) = fun eps =>
          cepsJetMoment (f eps) (n + 1) - ∑ j ∈ Finset.range n,
            (n.choose j : ℝ) * cepsCumulant (f eps) (j + 1) * cepsJetMoment (f eps) (n - j) :=
        funext fun _ => cepsCumRec_succ _ n
      have e2 : cepsCumSeries g (n + 1) = cepsMomentSeries g (n + 1) - ∑ j ∈ Finset.range n,
          (n.choose j : PowerSeries ℝ) * cepsCumSeries g (j + 1) * cepsMomentSeries g (n - j) :=
        cepsCumRec_succ _ n
      rw [e1, e2]
      exact h

end PGM
