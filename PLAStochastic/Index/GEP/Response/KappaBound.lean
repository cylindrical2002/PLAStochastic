import PLAStochastic.Index.GEP.Response.Defs
import PLAStochastic.Index.GEP.OrbitClosure.RegularClass
import PLAStochastic.Index.GEP.OrbitClosure.OrbitMoments

/-!
# WP4: the normalization coefficient is uniformly bounded

The exponential moment of the actual output law, proved in WP2, closes leaf 4A-κ.
For `η < θ`, the elementary inequality `x exp(η x) ≤ exp(θ x) / (θ - η)`
controls `E[Y ψ(Y)]` for every `OutTest η M ψ`.  Integrability is proved before
using the integral bound.  The output weight `θK / 2` and constant `2 CK / θK`
are absolute; only the threshold in `eps` depends on the input regular class.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- Absorb the linear factor into the gap between two exponential weights. -/
theorem mul_exp_le_exp_div {η θ x : ℝ} (hηθ : η < θ) :
    x * Real.exp (η * x) ≤ Real.exp (θ * x) / (θ - η) := by
  have hd : 0 < θ - η := sub_pos.mpr hηθ
  have hx : (θ - η) * x ≤ Real.exp ((θ - η) * x) := by
    linarith [Real.add_one_le_exp ((θ - η) * x)]
  apply (le_div_iff₀ hd).mpr
  calc x * Real.exp (η * x) * (θ - η)
      = ((θ - η) * x) * Real.exp (η * x) := by ring
    _ ≤ Real.exp ((θ - η) * x) * Real.exp (η * x) :=
      mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ = Real.exp (θ * x) := by rw [← Real.exp_add]; congr 1; ring

/-- Exponential moments give both integrability and a quantitative bound for `Y ψ(Y)`.
No continuity of `ψ` is required. -/
theorem ExpMom.integrable_mul_outTest {ρ : ProbabilityMeasure ℝ} {θ B η M : ℝ}
    {ψ : ℝ → ℝ} (hE : ExpMom θ B ρ)
    (hpos : ∀ᵐ x ∂(ρ : Measure ℝ), 0 ≤ x) (hηθ : η < θ) (hψ : OutTest η M ψ) :
    Integrable (fun x => x * ψ x) (ρ : Measure ℝ) ∧
      |∫ x, x * ψ x ∂(ρ : Measure ℝ)| ≤ M * (B / (θ - η)) := by
  have hM : 0 ≤ M := by
    have h := hψ.2 0 le_rfl
    simpa using (abs_nonneg (ψ 0)).trans h
  have hd : 0 < θ - η := sub_pos.mpr hηθ
  have hdom : ∀ᵐ x ∂(ρ : Measure ℝ),
      ‖x * ψ x‖ ≤ M / (θ - η) * Real.exp (θ * x) := by
    filter_upwards [hpos] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
    calc x * |ψ x| ≤ x * (M * Real.exp (η * x)) :=
        mul_le_mul_of_nonneg_left (hψ.2 x hx) hx
      _ = M * (x * Real.exp (η * x)) := by ring
      _ ≤ M * (Real.exp (θ * x) / (θ - η)) :=
        mul_le_mul_of_nonneg_left (mul_exp_le_exp_div hηθ) hM
      _ = M / (θ - η) * Real.exp (θ * x) := by ring
  have hI := hE.integrable.const_mul (M / (θ - η))
  have hInt : Integrable (fun x => x * ψ x) (ρ : Measure ℝ) :=
    hI.mono' (measurable_id.mul hψ.1).aestronglyMeasurable hdom
  refine ⟨hInt, ?_⟩
  calc |∫ x, x * ψ x ∂(ρ : Measure ℝ)|
      ≤ ∫ x, ‖x * ψ x‖ ∂(ρ : Measure ℝ) := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (fun x => x * ψ x) (μ := (ρ : Measure ℝ)))
    _ ≤ ∫ x, M / (θ - η) * Real.exp (θ * x) ∂(ρ : Measure ℝ) :=
      integral_mono_ae hInt.norm hI hdom
    _ = M / (θ - η) * ∫ x, Real.exp (θ * x) ∂(ρ : Measure ℝ) := integral_const_mul _ _
    _ ≤ M / (θ - η) * B := mul_le_mul_of_nonneg_left hE.le (div_nonneg hM hd.le)
    _ = M * (B / (θ - η)) := by ring

/-- **Leaf 4A-κ**: the actual output normalization coefficient is uniformly bounded,
with no unproved response or universality premise. -/
theorem kappaBound : KappaBound := by
  intro D θ vlo vhi hD hθ hvlo _hv
  obtain ⟨e2, he2⟩ := lawPhi_expMom (b := regB vhi) (β := regBeta D θ vlo)
    (regV_pos hvlo) (half_pos hθ) (show 0 < 2 * D / θ by positivity)
  refine ⟨θK / 2, half_pos θK_pos, 2 * CK / θK,
    max e2 (epsZero (regB vhi) (regBeta D θ vlo)), ?_⟩
  intro eps heps ν hν M ψ hψ
  have hm := hν.momClass hθ hvlo
  have hE := he2 eps ((le_max_left _ _).trans heps) ν hm (hν.expMom hθ)
  have hm' := lawPhi_momClass (bAbs_le_regB vhi) (βAbs_le_regBeta D θ vlo)
    (regV_pos hvlo) (regV_le_half vlo) ((le_max_right _ _).trans heps) hm
  have hpos : ∀ᵐ x ∂(lawPhi eps ν : Measure ℝ), 0 ≤ x := by
    filter_upwards [compl_mem_ae_iff.2 hm'.pos] with x hx
    exact le_of_lt (by simpa using hx)
  have h := (hE.integrable_mul_outTest hpos (show θK / 2 < θK by linarith [θK_pos]) hψ).2
  have heq : CK / (θK - θK / 2) = 2 * CK / θK := by field_simp; ring
  simpa only [outKappa, heq] using h

end

end PGM
