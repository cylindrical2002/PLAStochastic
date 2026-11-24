import PLAStochastic.Index.GEP.Kernel.Row.Green
import PLAStochastic.Index.GEP.Kernel.LinearSurvival.Main

/-!
# WP4 kernel rows: class-uniform assembly

This file discharges the two interfaces of the `GEPKernelRow*` chain from compiled modules and
packages the boundary row / pin / Green bounds of `influence-lipschitz.md` §3 for the actual
killed kernel `krDens` on the band `[0, w]`:

* `krLinearSurvival_exists`: `KrLinearSurvival D θ vlo vhi K` for some `K > 0`, from
  `linearSurvival_regLaw` (`GEPLinearSurvivalClass`);
* `krBand_exists`: for the class `RegLaw D θ vlo vhi` there are constants `K, L` such that every
  law of the class has a density representative `f` (`0 ≤ f ≤ D`, `f = 0` on `(-∞, 0]`,
  `f ≤ D e^{-θ x}`, `ν = f dx`) for which the standing hypotheses `KrBand` hold in both directions
  for every band width `w ≥ 1` and every slope in the window `|a - 1| ≤ A/w`, `1/2 ≤ |a| ≤ 2`;
* `krRow_bounds`: the collected statement (row), (pin) of §3 for one such band, with explicit
  constants depending only on `D, θ, vlo, vhi, K, L`.

Nothing here is an assumption: the constants are chosen before the law and the only inputs are
the compiled theorems of the `GEPKernelRow*`, `GEPKill*`, `GEPClosure*` and `GEPLinearSurvival*`
modules.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- **Interface discharge**: the one-sided linear survival bound of `linearSurvival_regLaw`. -/
theorem krLinearSurvival_exists (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hv : vlo ≤ vhi) : ∃ K : ℝ, 0 < K ∧ KrLinearSurvival D θ vlo vhi K := by
  obtain ⟨K, hK, h⟩ := linearSurvival_regLaw D θ vlo vhi hD hθ hvlo hv
  exact ⟨K, hK, h⟩

/-- **Class-uniform band hypotheses**: constants `K, L` and, for each law of the class, a density
representative `f` such that `KrBand` holds in both directions for all admissible `w, A, a`. -/
theorem krBand_exists (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hv : vlo ≤ vhi) :
    ∃ K L : ℝ, 0 < K ∧ 0 < L ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, x ≤ 0 → f x = 0) ∧ (∀ x, f x ≤ D) ∧
        (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ w A a : ℝ, 1 ≤ w → 0 ≤ A → |a - 1| ≤ A / w → 1 / 2 ≤ |a| → |a| ≤ 2 →
          KrBand D θ vlo vhi K L ν f w A a 1 a ∧ KrBand D θ vlo vhi K L ν f w A a (-1) (-a) := by
  obtain ⟨K, hK, hLS⟩ := krLinearSurvival_exists D θ vlo vhi hD hθ hvlo hv
  obtain ⟨L, hFree⟩ := krFreeBound_exists D θ vlo vhi hD hθ hvlo hv
  refine ⟨K, L, hK, hFree.1, fun ν hν => ?_⟩
  obtain ⟨f, hf, hf0, hfz, hfD, hfe, hνf⟩ := kr_regLaw_density ν hD hθ hν
  refine ⟨f, hf, hf0, hfz, hfD, hfe, hνf, fun w A a hw hA haA ha₁ ha₂ => ?_⟩
  have H : KrBand D θ vlo vhi K L ν f w A a 1 a :=
    { hD := hD, hθ := hθ, hvlo := hvlo, hvhi := hv, hLS := hLS, hFree := hFree, hν := hν,
      hK := hK.le, hf := hf, hf0 := hf0, hfz := hfz, hfD := hfD, hfe := hfe, hνf := hνf,
      hw := hw, hA := hA, haA := haA, ha₁ := ha₁, ha₂ := ha₂, hβ := Or.inl ⟨rfl, rfl⟩ }
  exact ⟨H, H.rev⟩

/-- **(row) and (pin) of `influence-lipschitz.md` §3 for the actual killed kernel.**
For a band `KrBand … w A a β a'` and boundary points `b, b' ∈ {0, w}`:

1. medium-time survival, row sup and row `L²`;
2. large-time survival, row sup and pin, with the killed `L²` gap rate `√λ`, `λ = 1 - κ/w²`;
3. medium-time pin, and the short-time opposite-side pin `≤ 6 D e^{-c₀ w}` (for `A ≤ w`);
4. the Green sums `O_b^± ≤ C_O (1 + A) w`, `‖∑_{n≥1} q_n(b,·)‖_∞ ≤ C_G (1 + A)(1 + log w)`,
   `∑_{n≥1} q_n(b, b') ≤ C_P (1 + A)² w^{-1/2}` (`b ≠ b'`, `A ≤ w`), and
   `∑_{n≥1} (n + w) q_n(b, b') ≤ C_B (1 + A)² w`. -/
theorem krRow_bounds {D θ vlo vhi K L w A a β a' : ℝ} {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w) :
    -- 1. medium time
    (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ w ^ 2 →
      krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b ≤ K * (1 + A) / Real.sqrt n) ∧
    (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ 2 * w ^ 2 → ∀ z,
      krDens (Icc 0 w) ν f β a' n b z ≤ krC₁ D K L * (1 + A) / n) ∧
    (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ w ^ 2 →
      ∫ z, krDens (Icc 0 w) ν f β a' n b z ^ 2 ≤
        krC₂ D K L * (1 + A) ^ 2 / (n * Real.sqrt n)) ∧
    -- 2. large time (`T = krT w`, `1 ≤ T ≤ w² ≤ 2T`)
    (∀ j : ℕ, krSurv (Icc 0 w) (ν : Measure ℝ) β a' (krT w + j) b ≤
      krC₃ D K L * (1 + A) * Real.sqrt (krLam D vlo vhi w) ^ j / w) ∧
    (∀ j : ℕ, ∀ z, krDens (Icc 0 w) ν f β a' (krT w + j + krT w) b z ≤
      krC₄ D K L * (1 + A) * Real.sqrt (krLam D vlo vhi w) ^ j / w ^ 2) ∧
    (∀ j : ℕ, krDens (Icc 0 w) ν f β a' (krT w + j + krT w) b b' ≤
      3 * krC₂ D K L * (1 + A) ^ 2 * Real.sqrt (krLam D vlo vhi w) ^ j / w ^ 3) ∧
    -- 3. pins
    (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ 2 * w ^ 2 →
      krDens (Icc 0 w) ν f β a' n b b' ≤ krCpin D K L * (1 + A) ^ 2 / (n * Real.sqrt n)) ∧
    (A ≤ w → b ≠ b' → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ w / 4 →
      krDens (Icc 0 w) ν f β a' n b b' ≤ 6 * D * Real.exp (-(krC₀ D θ * w))) ∧
    -- 4. Green sums
    (∑' n, krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b ≤ krCO D K L vlo vhi * (1 + A) * w) ∧
    (∀ z, ∑' n, krDens (Icc 0 w) ν f β a' (n + 1) b z ≤
      krCG D K L vlo vhi * (1 + A) * (1 + Real.log w)) ∧
    (A ≤ w → b ≠ b' → ∑' n, krDens (Icc 0 w) ν f β a' (n + 1) b b' ≤
      krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w) ∧
    (∑' n : ℕ, ((n : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (n + 1) b b' ≤
      krCB D K L vlo vhi * (1 + A) ^ 2 * w) := by
  refine ⟨fun n hn hnw => H.krSurv_medium hb hn hnw,
    fun n hn hnw z => krDens_bdry_medium ν H hb hn hnw z,
    fun n hn hnw => integral_sq_krDens_bdry_medium ν H hb hn hnw,
    fun j => krSurv_bdry_large ν H hb H.hT1 H.hTw H.hwT j,
    fun j z => krDens_bdry_row_large ν H hb H.hT1 H.hTw H.hwT j z,
    fun j => krDens_bdry_pin_large ν H hb hb' H.hT1 H.hTw H.hwT j,
    fun n hn hnw => krDens_bdry_pin_medium ν H hb hb' hn hnw,
    fun hAw hbb n hn hnw => krDens_bdry_pin_short ν H hAw hb hb' hbb hn hnw,
    tsum_krSurv_bdry_le ν H hb,
    fun z => tsum_krDens_bdry_row_le ν H hb z,
    fun hAw hbb => tsum_krDens_bdry_pin_le ν H hAw hb hb' hbb,
    tsum_weighted_krDens_bdry_pin_le ν H hb hb'⟩

end

end PGM
