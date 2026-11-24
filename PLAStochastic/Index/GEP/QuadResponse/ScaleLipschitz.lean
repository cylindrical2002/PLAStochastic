import PLAStochastic.Index.GEP.PointwiseSmall.RowPhi

/-!
# WP4 leaf `QuadResponse`: the Lipschitz dependence of the fixed-base test on the scale

Along two mixture paths of *different* variances `v_t^± = (1-t) v + t v_σ±`, the fixed-base test
`φ_ψ(S_T/C₀)/(M/η) = φ_{χ_t^±}(W_t^±)`, `W = v_t^± S_T/ε²`, uses two different rescalings
`c_t^± = ε²/(v_t^± C₀)`.  (U) compares each `φ_{χ_t^±}(W_t^±)` under `ν_t^±` with `φ_{χ_t^±}(W)`
under `ν`, and the remaining term is the change of scale under the fixed law `ν`:
`|φ_ψ(c₁ W) - φ_ψ(c₂ W)| ≤ M e^{η c_M W} |c₁ - c₂| W` (`quad_lip_pointwise`), whose expectation
is `O(|c₁ - c₂|)` by the exponential moment of `W` (`quad_third_term`), and
`|c_t^+ - c_t^-| ≤ (4 b₀/vlo²) t |v_σ₊ - v_σ₋|` (`quad_c_diff`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- The pointwise Lipschitz bound in the scale. -/
theorem quad_lip_pointwise {η M : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hM : 0 < M)
    {c₁ c₂ cM W : ℝ} (hc₁ : 0 < c₁) (hc₁M : c₁ ≤ cM) (hc₂ : 0 < c₂) (hc₂M : c₂ ≤ cM)
    (hW : 0 ≤ W) :
    |testFn ψ (c₁ * W) / (M / η) - testFn ψ (c₂ * W) / (M / η)| ≤
      η * |c₁ - c₂| * (W * Real.exp (η * cM * W)) := by
  have hk : 0 < M / η := by positivity
  rw [← sub_div, abs_div, abs_of_pos hk, div_le_iff₀ hk]
  have h := hψ.abs_testFn_sub_le hη.le (by positivity : 0 ≤ c₁ * W) (by positivity : 0 ≤ c₂ * W)
  have hmax : max (c₁ * W) (c₂ * W) ≤ cM * W := by
    refine max_le ?_ ?_ <;> exact mul_le_mul_of_nonneg_right (by assumption) hW
  have hexp : Real.exp (η * max (c₁ * W) (c₂ * W)) ≤ Real.exp (η * cM * W) := by
    rw [mul_assoc η cM W]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hmax hη.le)
  have habs : |c₁ * W - c₂ * W| = |c₁ - c₂| * W := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hW]
  calc |testFn ψ (c₁ * W) - testFn ψ (c₂ * W)|
      ≤ M * Real.exp (η * max (c₁ * W) (c₂ * W)) * |c₁ * W - c₂ * W| := h
    _ ≤ M * Real.exp (η * cM * W) * (|c₁ - c₂| * W) := by rw [habs]; gcongr
    _ = η * |c₁ - c₂| * (W * Real.exp (η * cM * W)) * (M / η) := by
        rw [show η * |c₁ - c₂| * (W * Real.exp (η * cM * W)) * (M / η) =
          |c₁ - c₂| * (W * Real.exp (η * cM * W)) * (η * (M / η)) by ring,
          mul_div_cancel₀ M hη.ne']
        ring

/-- The normalised test at a scale `c ≤ cM` is bounded by `e^{2 η c_M W}`. -/
theorem quad_test_bound {η M : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hM : 0 < M)
    {c cM W : ℝ} (hc : 0 < c) (hcM : c ≤ cM) (hW : 0 ≤ W) :
    |testFn ψ (c * W) / (M / η)| ≤ Real.exp (2 * η * cM * W) := by
  have hk : 0 < M / η := by positivity
  rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
  have h1 := hψ.abs_testFn_le hη.le (by positivity : 0 ≤ c * W)
  have h2 : c * W ≤ Real.exp (η * (c * W)) / η := le_exp_div hη
  have h3 : Real.exp (2 * η * (c * W)) ≤ Real.exp (2 * η * cM * W) :=
    Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right hcM hW])
  calc |testFn ψ (c * W)| ≤ M * Real.exp (η * (c * W)) * (c * W) := h1
    _ ≤ M * Real.exp (η * (c * W)) * (Real.exp (η * (c * W)) / η) := by gcongr
    _ = Real.exp (2 * η * (c * W)) * (M / η) := by
        rw [show 2 * η * (c * W) = η * (c * W) + η * (c * W) by ring, Real.exp_add]
        ring
    _ ≤ Real.exp (2 * η * cM * W) * (M / η) := by gcongr

/-- `|ε²/(v₁ C₀) - ε²/(v₂ C₀)| ≤ (4 b₀/vlo²) |v₁ - v₂|` for `v₁, v₂ ≥ vlo/2`, `ε² ≤ b₀ C₀`. -/
theorem quad_c_diff {v₁ v₂ vlo C₀ eps b₀ : ℝ} (hvlo : 0 < vlo) (hv₁ : vlo / 2 ≤ v₁)
    (hv₂ : vlo / 2 ≤ v₂) (hC₀ : 0 < C₀) (hb₀ : 0 < b₀) (he : eps ^ 2 ≤ b₀ * C₀) :
    |eps ^ 2 / (v₁ * C₀) - eps ^ 2 / (v₂ * C₀)| ≤ 4 * b₀ / vlo ^ 2 * |v₁ - v₂| := by
  have hv₁0 : 0 < v₁ := by linarith
  have hv₂0 : 0 < v₂ := by linarith
  have e : eps ^ 2 / (v₁ * C₀) - eps ^ 2 / (v₂ * C₀) = eps ^ 2 / C₀ * ((v₂ - v₁) / (v₁ * v₂)) := by
    field_simp
  rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ eps ^ 2 / C₀), abs_div,
    abs_of_pos (by positivity : 0 < v₁ * v₂), abs_sub_comm v₂ v₁]
  have h1 : eps ^ 2 / C₀ ≤ b₀ := by rw [div_le_iff₀ hC₀]; exact he
  have h2 : vlo ^ 2 / 4 ≤ v₁ * v₂ := by nlinarith
  have h3 : |v₁ - v₂| / (v₁ * v₂) ≤ |v₁ - v₂| / (vlo ^ 2 / 4) :=
    div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) h2
  calc eps ^ 2 / C₀ * (|v₁ - v₂| / (v₁ * v₂)) ≤ b₀ * (|v₁ - v₂| / (vlo ^ 2 / 4)) :=
        mul_le_mul h1 h3 (by positivity) hb₀.le
    _ = 4 * b₀ / vlo ^ 2 * |v₁ - v₂| := by field_simp

/-- **The change of scale under the fixed law**: `|E φ(c₁ W)/k - E φ(c₂ W)/k| ≤ |c₁ - c₂| CK / c_M`
when `E e^{2 η c_M W} ≤ CK`. -/
theorem quad_third_term {η M : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hM : 0 < M)
    {c₁ c₂ cM : ℝ} (hc₁ : 0 < c₁) (hc₁M : c₁ ≤ cM) (hc₂ : 0 < c₂) (hc₂M : c₂ ≤ cM)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : Ω → ℝ} (hWm : Measurable W)
    (hW0 : ∀ᵐ g ∂P, 0 ≤ W g) (hint : Integrable (fun g => Real.exp (2 * η * cM * W g)) P)
    (hle : ∫ g, Real.exp (2 * η * cM * W g) ∂P ≤ CK) :
    Integrable (fun g => testFn ψ (c₁ * W g) / (M / η)) P ∧
    Integrable (fun g => testFn ψ (c₂ * W g) / (M / η)) P ∧
    |∫ g, testFn ψ (c₁ * W g) / (M / η) ∂P - ∫ g, testFn ψ (c₂ * W g) / (M / η) ∂P| ≤
      |c₁ - c₂| * (CK / cM) := by
  have hcM : 0 < cM := hc₁.trans_le hc₁M
  have hmeas : ∀ c : ℝ, Measurable fun g => testFn ψ (c * W g) / (M / η) := fun c =>
    (hψ.measurable_testFn.comp (measurable_const.mul hWm)).div_const _
  have hI : ∀ c : ℝ, 0 < c → c ≤ cM → Integrable (fun g => testFn ψ (c * W g) / (M / η)) P := by
    intro c hc hcM'
    refine hint.mono' (hmeas c).aestronglyMeasurable ?_
    filter_upwards [hW0] with g hg
    rw [Real.norm_eq_abs]
    exact quad_test_bound hψ hη hM hc hcM' hg
  have hI₁ := hI c₁ hc₁ hc₁M
  have hI₂ := hI c₂ hc₂ hc₂M
  refine ⟨hI₁, hI₂, ?_⟩
  rw [← integral_sub hI₁ hI₂, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbd : ∀ᵐ g ∂P, ‖testFn ψ (c₁ * W g) / (M / η) - testFn ψ (c₂ * W g) / (M / η)‖ ≤
      |c₁ - c₂| / cM * Real.exp (2 * η * cM * W g) := by
    filter_upwards [hW0] with g hg
    rw [Real.norm_eq_abs]
    refine (quad_lip_pointwise hψ hη hM hc₁ hc₁M hc₂ hc₂M hg).trans ?_
    have h := mul_exp_le_exp_div (η := η * cM) (θ := 2 * η * cM) (x := W g) (by nlinarith)
    rw [show 2 * η * cM - η * cM = η * cM by ring] at h
    calc η * |c₁ - c₂| * (W g * Real.exp (η * cM * W g))
        ≤ η * |c₁ - c₂| * (Real.exp (2 * η * cM * W g) / (η * cM)) := by gcongr
      _ = |c₁ - c₂| / cM * Real.exp (2 * η * cM * W g) := by
          field_simp
  calc ∫ g, ‖testFn ψ (c₁ * W g) / (M / η) - testFn ψ (c₂ * W g) / (M / η)‖ ∂P
      ≤ ∫ g, |c₁ - c₂| / cM * Real.exp (2 * η * cM * W g) ∂P :=
        integral_mono_ae (hI₁.sub hI₂).norm (hint.const_mul _) hbd
    _ = |c₁ - c₂| / cM * ∫ g, Real.exp (2 * η * cM * W g) ∂P := integral_const_mul _ _
    _ ≤ |c₁ - c₂| / cM * CK := by gcongr
    _ = |c₁ - c₂| * (CK / cM) := by ring

end

end PGM
