import PLAStochastic.Index.GEP.RawDisc.SurvivalPolynomials
import PLAStochastic.Index.GEP.OrbitClosure.OrbitMoments
import PLAStochastic.Index.GEP.OrbitClosure.RegularClass
import PLAStochastic.Index.GEP.Response.Score.UniformBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# WP4 `RawDisc` assembly, part 3: the mixture laws `(1-t) ν + t σ` near `t = 0`

The mixture `ν_t = (1-t) ν + t σ` of a regular law and a direction law is not regular (`σ` has no
density bound), but for `t ≤ tMix A θσ` it lies in the moment class
`MomClass (vhi + 1) (βMix D θ vlo) (vlo / 2)` with the exponential moment
`ExpMom (min (θ/2) θσ) (BMix D θ A)` (`momClass_mix`, `expMom_mix`): mean one, variance
`(1-t) v(ν) + t v(σ) ∈ [vlo/2, vhi+1]`, third moments from the exponential moments
(`cube_of_expMom`).  The class constants `vhi + 1`, `βMix`, `vlo/2` do not depend on `(A, θσ)`;
only the admissible range of `t` does.

Consequences (`stopExp_mix`), for `ε` large:
* `T < ∞` a.s. and `P(T > m) ≤ (72/71) exp(-tailRate (vlo/2) m / ε²)` (`gapSegLen_tail`);
* `E e^{c S_T / ε²} ≤ CK` for every `c ≤ gamMix vlo = θK (vlo/2) / cPlus`: by `lawPhi_expMom`,
  `E e^{θK S_T / C} ≤ CK`, and `C_ε(ν_t) ≤ cPlus ε² / (vlo/2)` (`momClass_oneLayer`).  The weight
  `gamMix vlo` depends on the class only; this is how the output weight `γ` of `RawDisc` is chosen
  before `θσ`.
* `lintegral_exp_le_two`: `E e^{l X} ≤ 2` under `ν` and under `σ` for `l ≤ lamMix D θ A θσ`
  (hence along the whole segment, `SmallMgf.mix`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-! ## Moments from an exponential moment -/

theorem cube_le_exp {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    (x + 1) ^ 3 ≤ 6 * Real.exp c / c ^ 3 * Real.exp (c * x) := by
  have h := Real.pow_div_factorial_le_exp (x := c * (x + 1)) (by positivity) 3
  have h6 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6, div_le_iff₀ (by norm_num), mul_pow, show c * (x + 1) = c + c * x by ring,
    Real.exp_add] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith [h]

/-- Third moments from an exponential moment on `(0, ∞)`. -/
theorem cube_of_expMom {ρ : ProbabilityMeasure ℝ} (hpos : (ρ : Measure ℝ) (Iic 0) = 0) {c B : ℝ}
    (hc : 0 < c) (hint : Integrable (fun x => Real.exp (c * x)) (ρ : Measure ℝ))
    (hB : ∫ x, Real.exp (c * x) ∂(ρ : Measure ℝ) ≤ B) :
    Integrable (fun x : ℝ => (x + 1) ^ 3) (ρ : Measure ℝ) ∧
      ∫ x, (x + 1) ^ 3 ∂(ρ : Measure ℝ) ≤ 6 * Real.exp c / c ^ 3 * B := by
  have hae : ∀ᵐ x ∂(ρ : Measure ℝ), 0 < x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hpos] with x hx
    simpa using hx
  have hK : 0 ≤ 6 * Real.exp c / c ^ 3 := by positivity
  have hint3 : Integrable (fun x : ℝ => (x + 1) ^ 3) (ρ : Measure ℝ) := by
    refine (hint.const_mul (6 * Real.exp c / c ^ 3)).mono' (by fun_prop) ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact cube_le_exp hc hx.le
  refine ⟨hint3, ?_⟩
  calc ∫ x, (x + 1) ^ 3 ∂(ρ : Measure ℝ)
      ≤ ∫ x, 6 * Real.exp c / c ^ 3 * Real.exp (c * x) ∂(ρ : Measure ℝ) :=
        integral_mono_ae hint3 (hint.const_mul _) (hae.mono fun x hx => cube_le_exp hc hx.le)
    _ = 6 * Real.exp c / c ^ 3 * ∫ x, Real.exp (c * x) ∂(ρ : Measure ℝ) := integral_const_mul _ _
    _ ≤ 6 * Real.exp c / c ^ 3 * B := by gcongr

/-- The moments dominated by `(x + 1)³` on `(0, ∞)`. -/
theorem moments_of_cube {ρ : ProbabilityMeasure ℝ} (hpos : (ρ : Measure ℝ) (Iic 0) = 0)
    (h3 : Integrable (fun x : ℝ => (x + 1) ^ 3) (ρ : Measure ℝ)) :
    Integrable (fun x : ℝ => x) (ρ : Measure ℝ) ∧
      Integrable (fun x : ℝ => (x - 1) ^ 2) (ρ : Measure ℝ) ∧
      Integrable (fun x : ℝ => |x - 1| ^ 3) (ρ : Measure ℝ) ∧
      Integrable (fun x : ℝ => |x| ^ (3 : ℝ)) (ρ : Measure ℝ) ∧
      ∫ x, (x - 1) ^ 2 ∂(ρ : Measure ℝ) ≤ ∫ x, (x + 1) ^ 3 ∂(ρ : Measure ℝ) ∧
      ∫ x, |x - 1| ^ 3 ∂(ρ : Measure ℝ) ≤ ∫ x, (x + 1) ^ 3 ∂(ρ : Measure ℝ) := by
  have hae : ∀ᵐ x ∂(ρ : Measure ℝ), 0 < x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hpos] with x hx
    simpa using hx
  have b1 : ∀ x : ℝ, 0 < x → |x| ≤ (x + 1) ^ 3 := fun x hx => by
    rw [abs_of_pos hx]; nlinarith [sq_nonneg x, mul_pos hx hx]
  have b2 : ∀ x : ℝ, 0 < x → (x - 1) ^ 2 ≤ (x + 1) ^ 3 := fun x hx => by
    nlinarith [sq_nonneg x, mul_pos hx hx, mul_pos (mul_pos hx hx) hx]
  have b3 : ∀ x : ℝ, 0 < x → |x - 1| ^ 3 ≤ (x + 1) ^ 3 := fun x hx => by
    have : |x - 1| ≤ x + 1 := by rw [abs_le]; constructor <;> linarith
    exact pow_le_pow_left₀ (abs_nonneg _) this 3
  have b4 : ∀ x : ℝ, 0 < x → |x| ^ (3 : ℝ) ≤ (x + 1) ^ 3 := fun x hx => by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, abs_of_pos hx]
    exact pow_le_pow_left₀ hx.le (by linarith) 3
  have i1 : Integrable (fun x : ℝ => x) (ρ : Measure ℝ) :=
    h3.mono' (by fun_prop) (hae.mono fun x hx => by rw [Real.norm_eq_abs]; exact b1 x hx)
  have i2 : Integrable (fun x : ℝ => (x - 1) ^ 2) (ρ : Measure ℝ) :=
    h3.mono' (by fun_prop) (hae.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact b2 x hx)
  have i3 : Integrable (fun x : ℝ => |x - 1| ^ 3) (ρ : Measure ℝ) :=
    h3.mono' (by fun_prop) (hae.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact b3 x hx)
  have i4 : Integrable (fun x : ℝ => |x| ^ (3 : ℝ)) (ρ : Measure ℝ) :=
    h3.mono' ((continuous_abs.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable)
      (hae.mono fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact b4 x hx)
  exact ⟨i1, i2, i3, i4, integral_mono_ae i2 h3 (hae.mono fun x hx => b2 x hx),
    integral_mono_ae i3 h3 (hae.mono fun x hx => b3 x hx)⟩

/-! ## Exponential moments at small rates -/

theorem exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- `E e^{l X} ≤ 2` for small `l`, from a mean-one law with an exponential moment. -/
theorem integral_exp_le_two {ρ : ProbabilityMeasure ℝ} (hpos : (ρ : Measure ℝ) (Iic 0) = 0)
    (hmean : lawMean ρ = 1) {c B : ℝ} (hc : 0 < c)
    (hint : Integrable (fun x => Real.exp (c * x)) (ρ : Measure ℝ))
    (hB : ∫ x, Real.exp (c * x) ∂(ρ : Measure ℝ) ≤ B) {l : ℝ} (hl0 : 0 ≤ l) (hl : l ≤ c / 2)
    (hlB : l * (1 + 8 * |B| / c ^ 2) ≤ 1 / 2) :
    Integrable (fun x => Real.exp (l * x)) (ρ : Measure ℝ) ∧
      ∫ x, Real.exp (l * x) ∂(ρ : Measure ℝ) ≤ 2 ∧
      ∫⁻ x, ENNReal.ofReal (Real.exp (l * x)) ∂(ρ : Measure ℝ) ≤ 2 := by
  have hae : ∀ᵐ x ∂(ρ : Measure ℝ), 0 ≤ x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hpos] with x hx
    simp only [mem_Iic, not_le] at hx
    exact hx.le
  have hid : Integrable (fun x : ℝ => x) (ρ : Measure ℝ) :=
    Integrable.of_integral_ne_zero (by change lawMean ρ ≠ 0; rw [hmean]; norm_num)
  obtain ⟨hi, hle⟩ := integral_exp_mul_le_of_expMom (X := fun x : ℝ => x) hc hae hid
    (by change lawMean ρ ≤ 1; rw [hmean]) hint hB hl0 hl
  have hK : 0 ≤ 8 * |B| / c ^ 2 := by positivity
  have hl1 : l ≤ 1 := by nlinarith
  have hu : l + 8 * B / c ^ 2 * l ^ 2 ≤ 1 / 2 := by
    have h1 : 8 * B / c ^ 2 * l ^ 2 ≤ 8 * |B| / c ^ 2 * l := by
      have : 8 * B / c ^ 2 ≤ 8 * |B| / c ^ 2 := by gcongr; exact le_abs_self B
      calc 8 * B / c ^ 2 * l ^ 2 ≤ 8 * |B| / c ^ 2 * l ^ 2 := by gcongr
        _ ≤ 8 * |B| / c ^ 2 * l := by
            apply mul_le_mul_of_nonneg_left _ hK
            nlinarith
    nlinarith
  have h2 : ∫ x, Real.exp (l * x) ∂(ρ : Measure ℝ) ≤ 2 :=
    hle.trans ((Real.exp_le_exp.2 hu).trans exp_half_le_two)
  refine ⟨hi, h2, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  exact (ENNReal.ofReal_le_ofReal h2).trans (by norm_num)

/-! ## The constants of the mixture class -/

variable {D θ vlo vhi : ℝ}

/-- The third-moment constant of a regular law: `E(X+1)³ ≤ κν`. -/
def kapNu (D θ : ℝ) : ℝ := 6 * Real.exp (θ / 2) / (θ / 2) ^ 3 * (2 * D / θ)

/-- The third-moment constant of a direction law: `E(X+1)³ ≤ κσ`. -/
def kapSig (A θσ : ℝ) : ℝ := 6 * Real.exp θσ / θσ ^ 3 * |A|

/-- The admissible mixing range. -/
def tMix (A θσ : ℝ) : ℝ := 1 / (2 * (2 + kapSig A θσ))

/-- Third-moment constant of the mixture class. -/
def βMix (D θ vlo : ℝ) : ℝ := (kapNu D θ + 1) / Real.sqrt (vlo / 2) ^ 3

/-- Exponential rate of the mixture class. -/
def θMix (θ θσ : ℝ) : ℝ := min (θ / 2) θσ

/-- Exponential-moment constant of the mixture class. -/
def BMix (D θ A : ℝ) : ℝ := 2 * D / θ + |A| + 1

/-- The output weight of the class, `θK (vlo / 2) / cPlus`. -/
def gamMix (vlo : ℝ) : ℝ := θK * (vlo / 2) / cPlus

/-- The small rates `l` with `E e^{l X} ≤ 2` for both laws. -/
def lamMix (D θ A θσ : ℝ) : ℝ :=
  min (min (θ / 4) (θσ / 2))
    (1 / (2 * (1 + 8 * |2 * D / θ| / (θ / 2) ^ 2 + 8 * |A| / θσ ^ 2)))

theorem kapSig_nonneg (A θσ : ℝ) (hθσ : 0 < θσ) : 0 ≤ kapSig A θσ := by
  unfold kapSig; positivity

theorem tMix_pos (A θσ : ℝ) (hθσ : 0 < θσ) : 0 < tMix A θσ := by
  have := kapSig_nonneg A θσ hθσ
  unfold tMix; positivity

theorem tMix_le (A θσ : ℝ) (hθσ : 0 < θσ) : tMix A θσ ≤ 1 / 4 := by
  have := kapSig_nonneg A θσ hθσ
  unfold tMix
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem tMix_mul_le (A θσ : ℝ) (hθσ : 0 < θσ) : tMix A θσ * kapSig A θσ ≤ 1 := by
  have := kapSig_nonneg A θσ hθσ
  unfold tMix
  rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
  nlinarith

theorem gamMix_pos (hvlo : 0 < vlo) : 0 < gamMix vlo := by
  have := θK_pos
  have := cPlus_pos
  unfold gamMix; positivity

theorem lamMix_pos (hθ : 0 < θ) {A θσ : ℝ} (hθσ : 0 < θσ) : 0 < lamMix D θ A θσ := by
  unfold lamMix
  refine lt_min (lt_min (by positivity) (by positivity)) ?_
  positivity

/-! ## The two endpoint laws -/

theorem RegLaw.pos' {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    (hvlo : 0 < vlo) : (ν : Measure ℝ) (Iic 0) = 0 :=
  (h.momClass hθ hvlo).pos

theorem RegLaw.cube {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    (hvlo : 0 < vlo) :
    Integrable (fun x : ℝ => (x + 1) ^ 3) (ν : Measure ℝ) ∧
      ∫ x, (x + 1) ^ 3 ∂(ν : Measure ℝ) ≤ kapNu D θ :=
  cube_of_expMom (h.pos' hθ hvlo) (half_pos hθ) (h.expMom hθ).integrable (h.expMom hθ).le

theorem SigmaLaw.cube {A θσ : ℝ} {σ : ProbabilityMeasure ℝ} (h : SigmaLaw A θσ σ)
    (hθσ : 0 < θσ) :
    Integrable (fun x : ℝ => (x + 1) ^ 3) (σ : Measure ℝ) ∧
      ∫ x, (x + 1) ^ 3 ∂(σ : Measure ℝ) ≤ kapSig A θσ := by
  obtain ⟨h1, h2⟩ := cube_of_expMom h.pos hθσ h.expInt (h.expMom.trans (le_abs_self A))
  exact ⟨h1, h2⟩

theorem lawVar_eq_of_mean {ρ : ProbabilityMeasure ℝ} (h : lawMean ρ = 1) :
    lawVar ρ = ∫ x, (x - 1) ^ 2 ∂(ρ : Measure ℝ) := by
  rw [lawVar, h]

theorem coe_mixPM_of_mem (ν σ : ProbabilityMeasure ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (mixPM ν σ t : Measure ℝ) =
      ENNReal.ofReal (1 - t) • (ν : Measure ℝ) + ENNReal.ofReal t • (σ : Measure ℝ) := by
  rw [coe_mixPM, mixParam_of_mem ht]

theorem integral_mixPM {ν σ : ProbabilityMeasure ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {f : ℝ → ℝ} (hν : Integrable f (ν : Measure ℝ)) (hσ : Integrable f (σ : Measure ℝ)) :
    ∫ x, f x ∂(mixPM ν σ t : Measure ℝ) =
      (1 - t) * ∫ x, f x ∂(ν : Measure ℝ) + t * ∫ x, f x ∂(σ : Measure ℝ) := by
  rw [coe_mixPM_of_mem ν σ ht, integral_add_measure (hν.smul_measure ENNReal.ofReal_ne_top)
    (hσ.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by linarith [ht.2]), ENNReal.toReal_ofReal ht.1, smul_eq_mul,
    smul_eq_mul]

theorem integrable_mixPM {ν σ : ProbabilityMeasure ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {f : ℝ → ℝ} (hν : Integrable f (ν : Measure ℝ)) (hσ : Integrable f (σ : Measure ℝ)) :
    Integrable f (mixPM ν σ t : Measure ℝ) := by
  rw [coe_mixPM_of_mem ν σ ht]
  exact (hν.smul_measure ENNReal.ofReal_ne_top).add_measure
    (hσ.smul_measure ENNReal.ofReal_ne_top)

theorem lintegral_mixPM_le {ν σ : ProbabilityMeasure ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {f : ℝ → ℝ≥0∞} {M : ℝ≥0∞} (hν : ∫⁻ x, f x ∂(ν : Measure ℝ) ≤ M)
    (hσ : ∫⁻ x, f x ∂(σ : Measure ℝ) ≤ M) : ∫⁻ x, f x ∂(mixPM ν σ t : Measure ℝ) ≤ M := by
  rw [coe_mixPM_of_mem ν σ ht, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, smul_eq_mul, smul_eq_mul]
  calc ENNReal.ofReal (1 - t) * ∫⁻ x, f x ∂(ν : Measure ℝ) +
        ENNReal.ofReal t * ∫⁻ x, f x ∂(σ : Measure ℝ)
      ≤ ENNReal.ofReal (1 - t) * M + ENNReal.ofReal t * M := by gcongr
    _ = M := by
        rw [← add_mul, ← ENNReal.ofReal_add (by linarith [ht.2]) ht.1]
        simp

theorem mixPM_pos {ν σ : ProbabilityMeasure ℝ} (hν : (ν : Measure ℝ) (Iic 0) = 0)
    (hσ : (σ : Measure ℝ) (Iic 0) = 0) (t : ℝ) : (mixPM ν σ t : Measure ℝ) (Iic 0) = 0 := by
  rw [coe_mixPM, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hν, hσ]
  simp

/-! ## The mixture class -/

/-- **The mixture is in the moment class** for `t ≤ tMix`. -/
theorem momClass_mix (hθ : 0 < θ) (hvlo : 0 < vlo) {A θσ : ℝ} (hθσ : 0 < θσ)
    {ν σ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hσ : SigmaLaw A θσ σ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (tMix A θσ)) :
    MomClass (vhi + 1) (βMix D θ vlo) (vlo / 2) (mixPM ν σ t) := by
  have ht1 : t ≤ 1 / 4 := ht.2.trans (tMix_le A θσ hθσ)
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, by linarith⟩
  have htk : t * kapSig A θσ ≤ 1 :=
    (mul_le_mul_of_nonneg_right ht.2 (kapSig_nonneg A θσ hθσ)).trans (tMix_mul_le A θσ hθσ)
  obtain ⟨hν3, hν3le⟩ := hν.cube hθ hvlo
  obtain ⟨hσ3, hσ3le⟩ := hσ.cube hθσ
  obtain ⟨iν1, iν2, iν3, iν4, jν2, jν3⟩ := moments_of_cube (hν.pos' hθ hvlo) hν3
  obtain ⟨iσ1, iσ2, iσ3, iσ4, jσ2, jσ3⟩ := moments_of_cube hσ.pos hσ3
  have hmean : lawMean (mixPM ν σ t) = 1 := by
    unfold lawMean
    rw [integral_mixPM ht' iν1 iσ1]
    change (1 - t) * lawMean ν + t * lawMean σ = 1
    rw [hν.mean, hσ.mean]; ring
  have hvar : lawVar (mixPM ν σ t) =
      (1 - t) * lawVar ν + t * ∫ x, (x - 1) ^ 2 ∂(σ : Measure ℝ) := by
    rw [lawVar_eq_of_mean hmean, integral_mixPM ht' iν2 iσ2, lawVar_eq_of_mean hν.mean]
  have hvσ : 0 ≤ ∫ x, (x - 1) ^ 2 ∂(σ : Measure ℝ) := integral_nonneg fun _ => sq_nonneg _
  have hvge : vlo / 2 ≤ lawVar (mixPM ν σ t) := by
    rw [hvar]
    have h1 := hν.var_ge
    have a : (1 - t) * vlo ≤ (1 - t) * lawVar ν := mul_le_mul_of_nonneg_left h1 (by linarith)
    have b : 0 ≤ t * ∫ x, (x - 1) ^ 2 ∂(σ : Measure ℝ) := mul_nonneg ht.1 hvσ
    nlinarith [mul_le_mul_of_nonneg_right ht1 hvlo.le]
  have hvle : lawVar (mixPM ν σ t) ≤ vhi + 1 := by
    rw [hvar]
    have h1 := hν.var_le
    have h2 : t * ∫ x, (x - 1) ^ 2 ∂(σ : Measure ℝ) ≤ 1 :=
      (mul_le_mul_of_nonneg_left (jσ2.trans hσ3le) ht.1).trans htk
    have h3 : 0 ≤ lawVar ν := hvlo.le.trans hν.var_ge
    nlinarith [mul_nonneg ht.1 h3]
  have hvpos : 0 < vlo / 2 := by positivity
  refine
    { pos := mixPM_pos (hν.pos' hθ hvlo) hσ.pos t
      memLp3 := ?_
      mean := hmean
      var_ge := hvge
      var_le := hvle
      third_le := ?_ }
  · rw [← integrable_norm_rpow_iff aestronglyMeasurable_id (by norm_num) (by norm_num)]
    simp only [id, Real.norm_eq_abs, ENNReal.toReal_ofNat]
    exact integrable_mixPM ht' iν4 iσ4
  · rw [integral_mixPM ht' iν3 iσ3]
    have hs : Real.sqrt (vlo / 2) ^ 3 ≤ Real.sqrt (lawVar (mixPM ν σ t)) ^ 3 := by
      gcongr
    have hs0 : 0 < Real.sqrt (vlo / 2) ^ 3 := by positivity
    have hk0 : 0 ≤ kapNu D θ + 1 := by
      have : 0 ≤ ∫ x, (x + 1) ^ 3 ∂(ν : Measure ℝ) :=
        integral_nonneg_of_ae (by
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hν.pos' hθ hvlo)] with x hx
          simp only [mem_Iic, not_le] at hx
          show (0 : ℝ) ≤ (x + 1) ^ 3
          positivity)
      linarith
    have h1 : (1 - t) * ∫ x, |x - 1| ^ 3 ∂(ν : Measure ℝ) +
        t * ∫ x, |x - 1| ^ 3 ∂(σ : Measure ℝ) ≤ kapNu D θ + 1 := by
      have a1 : (1 - t) * ∫ x, |x - 1| ^ 3 ∂(ν : Measure ℝ) ≤ kapNu D θ := by
        have h0 : 0 ≤ ∫ x, |x - 1| ^ 3 ∂(ν : Measure ℝ) := integral_nonneg fun _ => by positivity
        nlinarith [jν3.trans hν3le, mul_nonneg ht.1 h0]
      have a2 : t * ∫ x, |x - 1| ^ 3 ∂(σ : Measure ℝ) ≤ 1 :=
        (mul_le_mul_of_nonneg_left (jσ3.trans hσ3le) ht.1).trans htk
      linarith
    calc (1 - t) * ∫ x, |x - 1| ^ 3 ∂(ν : Measure ℝ) + t * ∫ x, |x - 1| ^ 3 ∂(σ : Measure ℝ)
        ≤ kapNu D θ + 1 := h1
      _ = βMix D θ vlo * Real.sqrt (vlo / 2) ^ 3 := by
          unfold βMix; field_simp
      _ ≤ βMix D θ vlo * Real.sqrt (lawVar (mixPM ν σ t)) ^ 3 := by
          gcongr
          unfold βMix; positivity

/-- **The mixture has an exponential moment** with class-and-direction constants. -/
theorem expMom_mix (hθ : 0 < θ) (hvlo : 0 < vlo) {A θσ : ℝ}
    {ν σ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hσ : SigmaLaw A θσ σ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ExpMom (θMix θ θσ) (BMix D θ A) (mixPM ν σ t) := by
  have hνe := hν.expMom hθ
  have haeν : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hν.pos' hθ hvlo)] with x hx
    simpa using hx
  have haeσ : ∀ᵐ x ∂(σ : Measure ℝ), 0 < x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hσ.pos] with x hx
    simpa using hx
  have hm : Measurable fun x : ℝ => Real.exp (θMix θ θσ * x) := by fun_prop
  have iν : Integrable (fun x => Real.exp (θMix θ θσ * x)) (ν : Measure ℝ) :=
    hνe.integrable.mono' hm.aestronglyMeasurable (haeν.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (min_le_left _ _) hx.le))
  have iσ : Integrable (fun x => Real.exp (θMix θ θσ * x)) (σ : Measure ℝ) :=
    hσ.expInt.mono' hm.aestronglyMeasurable (haeσ.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (min_le_right _ _) hx.le))
  refine ⟨integrable_mixPM ht iν iσ, ?_⟩
  rw [integral_mixPM ht iν iσ]
  have a1 : ∫ x, Real.exp (θMix θ θσ * x) ∂(ν : Measure ℝ) ≤ 2 * D / θ :=
    (integral_mono_ae iν hνe.integrable (haeν.mono fun x hx =>
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (min_le_left _ _) hx.le))).trans hνe.le
  have a2 : ∫ x, Real.exp (θMix θ θσ * x) ∂(σ : Measure ℝ) ≤ |A| :=
    (integral_mono_ae iσ hσ.expInt (haeσ.mono fun x hx =>
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (min_le_right _ _) hx.le))).trans
      (hσ.expMom.trans (le_abs_self A))
  have p1 : 0 ≤ ∫ x, Real.exp (θMix θ θσ * x) ∂(ν : Measure ℝ) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have p2 : 0 ≤ ∫ x, Real.exp (θMix θ θσ * x) ∂(σ : Measure ℝ) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hD : 0 ≤ 2 * D / θ := p1.trans a1
  unfold BMix
  have ht0 := ht.1
  have ht1 := ht.2
  nlinarith [abs_nonneg A]

theorem BMix_pos (hD : 0 < D) (hθ : 0 < θ) (A : ℝ) : 0 < BMix D θ A := by
  unfold BMix; positivity

theorem θMix_pos (hθ : 0 < θ) {θσ : ℝ} (hθσ : 0 < θσ) : 0 < θMix θ θσ :=
  lt_min (by positivity) hθσ

/-- **`E e^{l X} ≤ 2`** at small rates, for both endpoint laws and along the segment. -/
theorem lintegral_exp_le_two (hθ : 0 < θ) (hvlo : 0 < vlo) {A θσ : ℝ} (hθσ : 0 < θσ)
    {ν σ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hσ : SigmaLaw A θσ σ) {l : ℝ}
    (hl0 : 0 ≤ l) (hl : l ≤ lamMix D θ A θσ) :
    (Integrable (fun x => Real.exp (l * x)) (ν : Measure ℝ) ∧
      ∫ x, Real.exp (l * x) ∂(ν : Measure ℝ) ≤ 2 ∧
      ∫⁻ x, ENNReal.ofReal (Real.exp (l * x)) ∂(ν : Measure ℝ) ≤ 2) ∧
    (Integrable (fun x => Real.exp (l * x)) (σ : Measure ℝ) ∧
      ∫ x, Real.exp (l * x) ∂(σ : Measure ℝ) ≤ 2 ∧
      ∫⁻ x, ENNReal.ofReal (Real.exp (l * x)) ∂(σ : Measure ℝ) ≤ 2) := by
  have hl1 : l ≤ min (θ / 4) (θσ / 2) := hl.trans (min_le_left _ _)
  have hl2 : l ≤ 1 / (2 * (1 + 8 * |2 * D / θ| / (θ / 2) ^ 2 + 8 * |A| / θσ ^ 2)) :=
    hl.trans (min_le_right _ _)
  have hK1 : 0 ≤ 8 * |2 * D / θ| / (θ / 2) ^ 2 := by positivity
  have hK2 : 0 ≤ 8 * |A| / θσ ^ 2 := by positivity
  have hden : 0 < 2 * (1 + 8 * |2 * D / θ| / (θ / 2) ^ 2 + 8 * |A| / θσ ^ 2) := by positivity
  have hl2' : l * (2 * (1 + 8 * |2 * D / θ| / (θ / 2) ^ 2 + 8 * |A| / θσ ^ 2)) ≤ 1 := by
    rwa [le_div_iff₀ hden] at hl2
  refine ⟨integral_exp_le_two (hν.pos' hθ hvlo) hν.mean (half_pos hθ) (hν.expMom hθ).integrable
    (hν.expMom hθ).le hl0 (by linarith [min_le_left (θ / 4) (θσ / 2)]) ?_,
    integral_exp_le_two hσ.pos hσ.mean hθσ hσ.expInt hσ.expMom hl0
      (by linarith [min_le_right (θ / 4) (θσ / 2)]) ?_⟩
  · nlinarith
  · nlinarith

/-! ## Stopped exponential moments along the segment -/

/-- **Stopped exponential moments along the segment** `t ∈ [0, tMix]`, for `ε` large. -/
theorem stopExp_mix (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) {A θσ : ℝ} (hθσ : 0 < θσ) :
    ∃ e₁ : ℝ, 1 ≤ e₁ ∧ ∀ eps, e₁ ≤ eps → ∀ ν σ : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → SigmaLaw A θσ σ → ∀ t ∈ Icc (0 : ℝ) (tMix A θσ),
        (∀ᵐ g ∂(iidLaw (mixPM ν σ t)), gapSegLen eps g ≠ ⊤) ∧
        (∀ m : ℕ, iidLaw (mixPM ν σ t) {g | (m : ℕ∞) < gapSegLen eps g} ≤
          ENNReal.ofReal (72 / 71 * Real.exp (-(tailRate * (vlo / 2)) * m / eps ^ 2))) ∧
        ∀ c : ℝ, 0 ≤ c → c ≤ gamMix vlo →
          Integrable (fun g => Real.exp (c * stopSum eps g / eps ^ 2))
            (iidLaw (mixPM ν σ t)) ∧
          ∫ g, Real.exp (c * stopSum eps g / eps ^ 2) ∂(iidLaw (mixPM ν σ t)) ≤ CK := by
  have hv2 : 0 < vlo / 2 := by positivity
  obtain ⟨e₂, he₂⟩ := lawPhi_expMom (b := vhi + 1) (β := βMix D θ vlo) hv2
    (θMix_pos hθ hθσ) (BMix_pos hD hθ A)
  refine ⟨max (max 1 (epsZero (vhi + 1) (βMix D θ vlo))) e₂, le_trans (le_max_left _ _)
    (le_max_left _ _), fun eps heps ν σ hν hσ t ht => ?_⟩
  have hez : epsZero (vhi + 1) (βMix D θ vlo) ≤ eps :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have he2 : e₂ ≤ eps := le_trans (le_max_right _ _) heps
  have heps1 : 1 ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ((tMix_le A θσ hθσ).trans (by norm_num))⟩
  set ρ := mixPM ν σ t with hρdef
  have hm := momClass_mix hθ hvlo hθσ hν hσ ht
  have hexp := expMom_mix hθ hvlo hν hσ ht'
  obtain ⟨hfin, hCm, hCp⟩ := momClass_oneLayer hv2 hez hm
  refine ⟨hfin, fun m => gapSegLen_tail hv2 hez hm m, fun c hc0 hc => ?_⟩
  have hK := he₂ eps he2 ρ hm hexp
  set C := lawC eps ρ with hCdef
  set P := iidLaw ρ with hPdef
  have hb0 : 0 < vhi + 1 := by linarith [hm.var_le, hm.var_ge]
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) hCm
  have hmap : ((lawPhi eps ρ : ProbabilityMeasure ℝ) : Measure ℝ) =
      P.map (fun g => stopSum eps g / C) := rfl
  have hSm : Measurable fun g => stopSum eps g / C := (measurable_stopSum eps).div_const _
  have he : Measurable fun x : ℝ => Real.exp (θK * x) := by fun_prop
  have hint : Integrable (fun g => Real.exp (θK * (stopSum eps g / C))) P := by
    have h := hK.integrable
    rw [hmap] at h
    exact (integrable_map_measure he.aestronglyMeasurable hSm.aemeasurable).1 h
  have hval : ∫ g, Real.exp (θK * (stopSum eps g / C)) ∂P ≤ CK := by
    have h := hK.le
    rw [hmap, integral_map hSm.aemeasurable he.aestronglyMeasurable] at h
    exact h
  have hSnn : ∀ᵐ g ∂P, 0 ≤ stopSum eps g := by
    filter_upwards [ae_pos_iidLaw hm.pos] with g hg
    unfold stopSum gapKeys
    exact Finset.sum_nonneg fun i _ => (hg i).le
  have hcC : c * C ≤ θK * eps ^ 2 := by
    have h1 : c * C ≤ gamMix vlo * (cPlus * eps ^ 2 / (vlo / 2)) :=
      mul_le_mul hc hCp hCpos.le (gamMix_pos hvlo).le
    have h2 : gamMix vlo * (cPlus * eps ^ 2 / (vlo / 2)) = θK * eps ^ 2 := by
      unfold gamMix
      have := cPlus_pos
      field_simp
    linarith
  have hpt : ∀ᵐ g ∂P, Real.exp (c * stopSum eps g / eps ^ 2) ≤
      Real.exp (θK * (stopSum eps g / C)) := by
    filter_upwards [hSnn] with g hg
    refine Real.exp_le_exp.2 ?_
    have heps2 : 0 < eps ^ 2 := by positivity
    rw [div_le_iff₀ heps2, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hCpos]
    nlinarith [mul_le_mul_of_nonneg_left hcC hg]
  have hm' : Measurable fun g => Real.exp (c * stopSum eps g / eps ^ 2) := by
    have := measurable_stopSum eps
    fun_prop
  have hint' : Integrable (fun g => Real.exp (c * stopSum eps g / eps ^ 2)) P :=
    hint.mono' hm'.aestronglyMeasurable (hpt.mono fun g hg => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hg)
  exact ⟨hint', (integral_mono_ae hint' hint hpt).trans hval⟩

end

end PGM
