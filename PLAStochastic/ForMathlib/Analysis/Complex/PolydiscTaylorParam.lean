import PLAStochastic.ForMathlib.Analysis.Complex.PolydiscTaylor
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricDeriv
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricHolomorphicIntegral

/-!
# Parameter dependence of the canonical polydisc Taylor coefficients

* `analyticAt_polydiscTaylorCoeff_param`: if `(q, z) ↦ G q z` is jointly analytic at `(p₀, z)`
  for every `z` in an open set `U`, then `z ↦ C α (G · z)` is analytic on `U`;
* `aestronglyMeasurable_polydiscTaylorCoeff`: if `H · a` is analytic on the polydisc
  `ball p₀ R` for a.e. `a` and its values there are measurable in `a`, then `a ↦ C α (H · a)` is
  a.e. strongly measurable.

Both follow from the finite Fourier formula `polydiscTaylorCoeff_eq_grid`, which writes each
coefficient through finitely many one-variable line derivatives.
-/

noncomputable section
open Complex Finset Metric Filter Topology MeasureTheory
namespace PGM

variable {d : ℕ}

/-- **Analytic parameters.** The canonical coefficients of a jointly analytic family depend
analytically on the parameter. -/
theorem analyticAt_polydiscTaylorCoeff_param {G : (Fin d → ℂ) → ℂ → ℂ} {p₀ : Fin d → ℂ}
    {U : Set ℂ} (hU : IsOpen U)
    (hG : ∀ z ∈ U, AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => G v.1 v.2) (p₀, z))
    (α : Fin d → ℕ) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    AnalyticAt ℂ (fun z => polydiscTaylorCoeff (fun q => G q z) p₀ α) z₀ := by
  set n := ∑ i, α i with hn
  have hslice : ∀ z ∈ U, AnalyticAt ℂ (fun q => G q z) p₀ := fun z hz =>
    (hG z hz).comp₂ (f := fun q => q) (g := fun _ => z) analyticAt_id analyticAt_const
  have hline : ∀ k : Fin d → Fin (n + 1), AnalyticAt ℂ
      (fun z => iteratedDeriv n (fun t : ℂ => G (p₀ + t • polydiscGridPoint n k) z) 0) z₀ := by
    intro k
    set v := polydiscGridPoint n k
    have h1 : AnalyticAt ℂ (fun v' : (Fin d → ℂ) × ℂ => G v'.1 v'.2)
        (p₀ + ((z₀, (0 : ℂ)) : ℂ × ℂ).2 • v, ((z₀, (0 : ℂ)) : ℂ × ℂ).1) := by
      simpa using hG z₀ hz₀
    have hH : AnalyticAt ℂ (fun w : ℂ × ℂ => G (p₀ + w.2 • v) w.1) (z₀, 0) :=
      h1.comp₂ (f := fun w : ℂ × ℂ => p₀ + w.2 • v) (g := fun w : ℂ × ℂ => w.1)
        (analyticAt_const.add (analyticAt_snd.smul analyticAt_const)) analyticAt_fst
    exact (hH.iteratedDeriv_snd n).comp (f := fun z : ℂ => (z, (0 : ℂ)))
      (analyticAt_id.prod analyticAt_const)
  have hsum : AnalyticAt ℂ (fun z => (((n + 1 : ℕ) : ℂ) ^ d)⁻¹ * (n.factorial : ℂ)⁻¹ *
      ∑ k : Fin d → Fin (n + 1),
        iteratedDeriv n (fun t : ℂ => G (p₀ + t • polydiscGridPoint n k) z) 0 *
          polydiscGridWeight n α k) z₀ := by
    refine analyticAt_const.mul ?_
    exact Finset.analyticAt_fun_sum _ fun k _ => (hline k).mul analyticAt_const
  refine hsum.congr (Filter.eventually_of_mem (hU.mem_nhds hz₀) fun z hz => ?_)
  exact (polydiscTaylorCoeff_eq_grid (hslice z hz) hn.symm).symm

/-- **Measurable parameters.** The canonical coefficients of an a.e. analytic family with
measurable values on the polydisc are measurable. -/
theorem aestronglyMeasurable_polydiscTaylorCoeff {Λ : Type*} [MeasurableSpace Λ]
    {μ : Measure Λ} {H : (Fin d → ℂ) → Λ → ℂ} {p₀ : Fin d → ℂ} {R : ℝ} (hR : 0 < R)
    (ha : ∀ᵐ a ∂μ, ∀ q ∈ ball p₀ R, AnalyticAt ℂ (fun q => H q a) q)
    (hm : ∀ q ∈ ball p₀ R, AEStronglyMeasurable (fun a => H q a) μ) (α : Fin d → ℕ) :
    AEStronglyMeasurable (fun a => polydiscTaylorCoeff (fun q => H q a) p₀ α) μ := by
  set n := ∑ i, α i with hn
  have hmem : ∀ (k : Fin d → Fin (n + 1)) (t : ℂ), t ∈ ball (0 : ℂ) R →
      p₀ + t • polydiscGridPoint n k ∈ ball p₀ R := by
    intro k t ht
    rw [mem_ball, dist_self_add_left, norm_smul]
    rw [mem_ball, dist_zero_right] at ht
    calc ‖t‖ * ‖polydiscGridPoint n k‖ ≤ ‖t‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_polydiscGridPoint_le n k) (norm_nonneg _)
      _ < R := by rwa [mul_one]
  have hk : ∀ k : Fin d → Fin (n + 1), AEStronglyMeasurable
      (fun a => iteratedDeriv n (fun t : ℂ => H (p₀ + t • polydiscGridPoint n k) a) 0) μ := by
    intro k
    refine aestronglyMeasurable_iteratedDeriv_of_ae_differentiableOn
      (f := fun a t => H (p₀ + t • polydiscGridPoint n k) a) isOpen_ball ?_
      (fun t ht => hm _ (hmem k t ht)) n 0 (mem_ball_self hR)
    filter_upwards [ha] with a ha' t ht
    exact ((ha' _ (hmem k t ht)).differentiableAt.comp t
      (differentiableAt_line p₀ _ t)).differentiableWithinAt
  have hrhs : AEStronglyMeasurable (fun a => (((n + 1 : ℕ) : ℂ) ^ d)⁻¹ * (n.factorial : ℂ)⁻¹ *
      ∑ k : Fin d → Fin (n + 1),
        iteratedDeriv n (fun t : ℂ => H (p₀ + t • polydiscGridPoint n k) a) 0 *
          polydiscGridWeight n α k) μ :=
    aestronglyMeasurable_const.mul (Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
      (hk k).mul aestronglyMeasurable_const)
  refine hrhs.congr ?_
  filter_upwards [ha] with a ha'
  exact (polydiscTaylorCoeff_eq_grid (ha' p₀ (mem_ball_self hR)) hn.symm).symm

end PGM
