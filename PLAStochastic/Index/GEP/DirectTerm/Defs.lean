import PLAStochastic.Index.GEP.Response.Defs

/-!
# WP4 leaf `DirectTerm`: intermediate interfaces

The direct term `H_φ = I_{φ'(·/C)} / C` (`directKernel`) is shown to be `a + O(ε⁻¹ e^{αx})` by the
route of `research/2026-09-28-gep-closure/direct-endpoint-response.md` (DT) and
`positive-direction-response.md` (PD) §2, §8, §9:

1. **(DiscInterp)** a holomorphic function on a disc of fixed radius `R`, bounded by `M` on the disc
   and by `δ` on the real segment `[0, R/8]`, has `|f'(0)| ≤ K δ (1 + log (M/δ))² / R`
   (PD (5) with `j = 1`; the proof uses the three lines theorem through `cosh`, not Chebyshev
   series).
2. **(RawDisc)** along the positive mixture path `ν_t = (1 - t) ν + t σ`, the fixed-base raw output
   test `t ↦ E_{ν_t}[F(S_T)]` has an analytic continuation to a disc whose radius does not shrink with
   `ε`, with a polynomial bound `K ε^p` on the disc, a bound `K` on the real segment, and derivative
   `∫ I_F d(σ - ν)` at `0`, where `I_F = insKernel ε ν (F ∘ S_T)` (PD (25), (33)–(35); raw-output
   (3)–(5); mixed-kernel §2–4; raw-measure-tools).  The output weight `γ` is chosen before the
   exponential moment `θσ` of the direction law (PD §9).
3. The reduction `DirectTerm ⇐ DiscInterp ∧ RawDisc` (positive directions PD §1, Lebesgue points
   PD §5, calibration DT (6), coarse tail PD (34)).

`SigmaLaw A θσ` is the class of direction laws: absolutely continuous, supported on `(0, ∞)`,
mean one, `∫ e^{θσ x} dσ ≤ A`.  No density bound: the bump directions of the Lebesgue-point
argument have unbounded densities.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- Direction laws of the positive mixture paths (PD §1, §9): absolutely continuous, supported on
`(0, ∞)`, mean one, with the exponential moment `∫ e^{θσ x} dσ ≤ A`.  No density bound. -/
structure SigmaLaw (A θσ : ℝ) (σ : ProbabilityMeasure ℝ) : Prop where
  pos : (σ : Measure ℝ) (Iic 0) = 0
  ac : (σ : Measure ℝ) ≪ volume
  mean : lawMean σ = 1
  expInt : Integrable (fun x => Real.exp (θσ * x)) (σ : Measure ℝ)
  expMom : ∫ x, Real.exp (θσ * x) ∂(σ : Measure ℝ) ≤ A

/-- **Analytic interpolation at the end of a real segment** (PD (5), `j = 1`).  An absolute constant
`K` such that a holomorphic `f` on `ball 0 R`, bounded by `M` there and by `δ` on `[0, R/8]`,
satisfies `‖f'(0)‖ ≤ K δ (1 + log (M/δ))² / R`. -/
def DiscInterp : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (f : ℂ → ℂ) (R M δ : ℝ), 0 < R → 0 < δ → δ ≤ M →
    DifferentiableOn ℂ f (Metric.ball 0 R) → (∀ z ∈ Metric.ball (0 : ℂ) R, ‖f z‖ ≤ M) →
    (∀ t : ℝ, 0 ≤ t → t ≤ R / 8 → ‖f t‖ ≤ δ) →
      ‖deriv f 0‖ ≤ K * δ * (1 + Real.log (M / δ)) ^ 2 / R

/-- **Raw analytic continuation on a fixed disc** (PD (25), (35), §9; raw-output-response (3)–(5)).
For the regular class there is an output weight `γ > 0` such that, for every exponential moment
`θσ > 0` of the direction law, there are a radius `r`, constants `K, e0` and a power `p` with: for
all `ε ≥ e0`, `ν` regular, `σ` a direction law and every test `|F(y)| ≤ e^{γ y / ε²}` (`y ≥ 0`),
some holomorphic `f` on `ball 0 r` has `‖f‖ ≤ K ε^p` there, `‖f t‖ ≤ K` on `[0, r/8]`, and
`f'(0) = ∫ I_F dσ - ∫ I_F dν` with `I_F = insKernel ε ν (F ∘ S_T)`.  On `[0, r]` the function `f`
is `t ↦ E_{(1-t)ν+tσ}[F(S_T)]`; only the three displayed properties are consumed. -/
def RawDisc : Prop :=
  ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi →
    ∃ γ : ℝ, 0 < γ ∧ ∀ A θσ : ℝ, 0 < θσ → ∃ (r K e0 : ℝ) (p : ℕ), 0 < r ∧
      ∀ eps, e0 ≤ eps → ∀ ν σ : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
        SigmaLaw A θσ σ → ∀ F : ℝ → ℝ, Measurable F →
          (∀ y, 0 ≤ y → |F y| ≤ Real.exp (γ * y / eps ^ 2)) →
          ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 r) ∧
            (∀ z ∈ Metric.ball (0 : ℂ) r, ‖f z‖ ≤ K * eps ^ p) ∧
            (∀ t : ℝ, 0 ≤ t → t ≤ r / 8 → ‖f t‖ ≤ K) ∧
            deriv f 0 = (((∫ x, insKernel eps ν (fun g => F (stopSum eps g)) x
                  ∂(σ : Measure ℝ)) -
                ∫ x, insKernel eps ν (fun g => F (stopSum eps g)) x ∂(ν : Measure ℝ) : ℝ) : ℂ)

end

end PGM
