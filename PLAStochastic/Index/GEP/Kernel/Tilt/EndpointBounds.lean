import PLAStochastic.Index.GEP.Kernel.Tilt.Rate
import PLAStochastic.Index.GEP.Kernel.Tilt.Conjugacy
import PLAStochastic.Index.GEP.SurvivalBound.KilledRow.RegularClass

/-! # Actual tilted killed rows with explicit endpoint factors -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- Changing the gap coordinate by its true mean changes the slope by that mean. -/
theorem kernel_kStep_map_div (J : Set ℝ) (μ : Measure ℝ) (β a : ℝ)
    {m : ℝ} (hm : m ≠ 0) :
    kStep J (μ.map (fun x => x / m)) β (a * m) = kStep J μ β a := by
  funext f y
  by_cases hy : y ∈ J
  · simp only [kStep, indicator_of_mem hy, div_eq_mul_inv]
    rw [(measurableEmbedding_mulRight₀ (inv_ne_zero hm)).integral_map]
    congr 1
    funext x
    congr 1
    field_simp
  · simp only [kStep, indicator_of_notMem hy]

/-- A pure probability row inherits the class spectral gap at any fixed slope floor. -/
theorem kernel_norm_pure_row_regLaw (D θ vlo vhi a₀ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (ha₀ : 0 < a₀) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ α w β a : ℝ, 1 ≤ w → a₀ ≤ |a| →
      ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ,
        ‖((kStep (Icc α (α + w)) (ν : Measure ℝ) β a)^[n]
          ((Icc α (α + w)).indicator φ)) y‖ ≤
          3 * Real.sqrt (D * w / a₀) * Real.exp (-(c * ((n : ℝ) - 1) / (2 * w ^ 2))) := by
  let c₀ := min (killCnu D vlo vhi) 1
  have hc₀ : 0 < c₀ := lt_min (killCnu_pos hD hvlo hv) one_pos
  refine ⟨killGapConst c₀ a₀, killGapConst_pos hc₀ ha₀, ?_⟩
  intro ν hν α w β a hw ha φ hφ hφ1 n hn y
  obtain ⟨f, hf, hf0, hfD, hνf⟩ := hν.kill_density_le hθ
  have hgap (t : ℝ) :
      ‖(1 - (0 : ℂ)) * charFun (ν : Measure ℝ) t + 0 * charFun (ν : Measure ℝ) t‖ ^ 2 ≤
        1 - c₀ * min (t ^ 2) 1 := by
    have hh := kill_regLaw_charFun_gap hD hθ hvlo hν (a := 1) (by norm_num) t
    simp only [one_mul] at hh
    have hc := mul_le_mul_of_nonneg_right (min_le_left (killCnu D vlo vhi) 1)
      (le_min (sq_nonneg t) zero_le_one)
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    linarith
  have hh := norm_kRow_le_gap_exp (ν := (ν : Measure ℝ)) (σ := (ν : Measure ℝ))
    (z := 0) (β := β) (α := α) hw hf hf0 hfD hνf ha₀ ha hc₀ (min_le_right _ _) hgap
    (by norm_num) hφ hφ1 hn y
  have he : kStepZ (Icc α (α + w)) (ν : Measure ℝ) (ν : Measure ℝ) 0 β a =
      kStep (Icc α (α + w)) (ν : Measure ℝ) β a := by
    funext u x
    simp [kStepZ]
  rw [kRow, he] at hh
  simpa only [norm_zero, zero_pow (by omega : n ≠ 0), add_zero] using hh

/-- Pure killed iterates retain the sup norm bound, without measurability assumptions. -/
theorem kernel_norm_killed_le {J : Set ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {β a M : ℝ} {f : ℝ → ℂ} (hf : ∀ y, ‖f y‖ ≤ M) (n : ℕ) (x : ℝ) :
    ‖((kStep J μ β a)^[n] f) x‖ ≤ M := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact norm_kStep_le ih x

/-- The exponential endpoint weight on an interval has a translation-free bound. -/
theorem kernel_endpoint_weight_bound {α w a lam x : ℝ} (hx : x ∈ Icc α (α + w))
    {φ : ℝ → ℂ} (hφ : ∀ y, ‖φ y‖ ≤ 1) (y : ℝ) :
    ‖(Icc α (α + w)).indicator
      (fun z => Real.exp (lam * (z - x) / a) • φ z) y‖ ≤
        Real.exp (|lam| * w / |a|) := by
  by_cases hy : y ∈ Icc α (α + w)
  · rw [indicator_of_mem hy, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hd : |y - x| ≤ w := abs_le.mpr ⟨by linarith [hx.2, hy.1], by linarith [hy.2, hx.1]⟩
    have he : lam * (y - x) / a ≤ |lam| * w / |a| := by
      calc
        _ ≤ |lam * (y - x) / a| := le_abs_self _
        _ = |lam| * |y - x| / |a| := by rw [abs_div, abs_mul]
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hd (abs_nonneg lam)) (abs_nonneg a)
    exact (mul_le_of_le_one_right (Real.exp_nonneg _) (hφ y)).trans (Real.exp_le_exp.mpr he)
  · rw [indicator_of_notMem hy, norm_zero]
    exact Real.exp_nonneg _


/-- Centering the terminal exponential at the actual start removes interval location. -/
theorem kernel_killed_eq_tilt_endpoint (J : Set ℝ) (ν : ProbabilityMeasure ℝ)
    {a lam : ℝ} (ha : a ≠ 0)
    (hM : Integrable (fun t : ℝ => Real.exp (lam * t)) (ν : Measure ℝ))
    (f : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    ((kStep J (ν : Measure ℝ) 1 a)^[n] f) x =
      Real.exp (-(n : ℝ) * kernelTiltRate ν a lam) •
        ((kStep J ((ν : Measure ℝ).tilted (fun t => lam * t)) 1 a)^[n]
          (fun y => Real.exp (lam * (y - x) / a) • f y)) x := by
  have he : (fun y => Real.exp (lam * (y - x) / a) • f y) =
      fun y => Real.exp (-(lam * x / a)) • (Real.exp (lam * y / a) • f y) := by
    funext y
    rw [smul_smul, ← Real.exp_add]
    congr 2
    ring
  rw [he, kernel_killed_const_smul, smul_smul, ← Real.exp_add,
    kernel_killed_eq_tilt J (ν : Measure ℝ) 1 ha hM]
  congr 2
  dsimp [kernelTiltRate]
  ring

/-- One deterministic inserted gap leaves `l+r` random cumulant normalizers. -/
theorem kernel_killed_marked_eq_tilt_endpoint (J : Set ℝ) (ν : ProbabilityMeasure ℝ)
    {a lam : ℝ} (ha : a ≠ 0)
    (hM : Integrable (fun t : ℝ => Real.exp (lam * t)) (ν : Measure ℝ))
    (t : ℝ) (f : ℝ → ℂ) (l r : ℕ) (x : ℝ) :
    ((kStep J (ν : Measure ℝ) 1 a)^[l]
      (kernelMarkedStep J 1 a t ((kStep J (ν : Measure ℝ) 1 a)^[r] f))) x =
      Real.exp (-((l : ℝ) + r) * kernelTiltRate ν a lam + lam * t - lam / a) •
        ((kStep J ((ν : Measure ℝ).tilted (fun y => lam * y)) 1 a)^[l]
          (kernelMarkedStep J 1 a t
            ((kStep J ((ν : Measure ℝ).tilted (fun y => lam * y)) 1 a)^[r]
              (fun y => Real.exp (lam * (y - x) / a) • f y)))) x := by
  have he : (fun y => Real.exp (lam * (y - x) / a) • f y) =
      fun y => Real.exp (-(lam * x / a)) • (Real.exp (lam * y / a) • f y) := by
    funext y
    rw [smul_smul, ← Real.exp_add]
    congr 2
    ring
  rw [he, kernel_killed_const_smul, kernel_markedStep_const_smul,
    kernel_killed_const_smul, smul_smul, ← Real.exp_add,
    kernel_killed_marked_eq_tilt J (ν : Measure ℝ) 1 t ha hM]
  congr 2
  dsimp [kernelTiltRate]
  ring

/-- A deterministic projected step also preserves sup norm bounds. -/
theorem kernel_norm_marked_le {J : Set ℝ} {β a t M : ℝ} {f : ℝ → ℂ}
    (hf : ∀ y, ‖f y‖ ≤ M) (x : ℝ) : ‖kernelMarkedStep J β a t f x‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf 0)
  by_cases hx : x ∈ J
  · simpa only [kernelMarkedStep, indicator_of_mem hx] using hf (x + β - a * t)
  · simp only [kernelMarkedStep, indicator_of_notMem hx, norm_zero]
    exact hM

/-- The actual row has the full Cramer rate with an explicit interval endpoint cost. -/
theorem RegLaw.kernel_killed_tilt_bound {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    {a lam α w x : ℝ} (ha : a ≠ 0)
    (hlam : |lam| ≤ kernelTiltClassRadius D θ vlo vhi)
    (hx : x ∈ Icc α (α + w)) (φ : ℝ → ℂ) (hφ : ∀ y, ‖φ y‖ ≤ 1) (n : ℕ) :
    ‖((kStep (Icc α (α + w)) (ν : Measure ℝ) 1 a)^[n]
        ((Icc α (α + w)).indicator φ)) x‖ ≤
      Real.exp (-(n : ℝ) * kernelTiltRate ν a lam + |lam| * w / |a|) := by
  have hU := hν.univClass hθ hvlo
  have hl : |lam| ≤ θ / 2 := (hlam.trans (min_le_left _ _)).trans
    ((saTiltRadius_le_half _ _ (by positivity)).trans (by linarith))
  let := hU.isProbabilityMeasure_centeredTilt hl
  have hp : IsProbabilityMeasure ((ν : Measure ℝ).tilted (fun t => lam * t)) := by
    rw [← kernel_centeredTilt_eq_raw]
    infer_instance
  let := hp
  rw [kernel_killed_eq_tilt_endpoint _ ν ha (hU.kernel_integrable_exp_raw hl),
    norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply kernel_norm_killed_le
  intro y
  have he : (Real.exp (lam * (y - x) / a) • (Icc α (α + w)).indicator φ y) =
      (Icc α (α + w)).indicator (fun z => Real.exp (lam * (z - x) / a) • φ z) y := by
    by_cases hy : y ∈ Icc α (α + w) <;> simp [hy]
  rw [he]
  exact kernel_endpoint_weight_bound hx hφ y

/-- The marked bound retains the extra deterministic exponent and the missing random step. -/
theorem RegLaw.kernel_killed_marked_tilt_bound {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    {a lam α w x : ℝ} (ha : a ≠ 0)
    (hlam : |lam| ≤ kernelTiltClassRadius D θ vlo vhi)
    (hx : x ∈ Icc α (α + w)) (φ : ℝ → ℂ) (hφ : ∀ y, ‖φ y‖ ≤ 1)
    (t : ℝ) (l r : ℕ) :
    ‖((kStep (Icc α (α + w)) (ν : Measure ℝ) 1 a)^[l]
      (kernelMarkedStep (Icc α (α + w)) 1 a t
        ((kStep (Icc α (α + w)) (ν : Measure ℝ) 1 a)^[r]
          ((Icc α (α + w)).indicator φ)))) x‖ ≤
      Real.exp (-((l : ℝ) + r) * kernelTiltRate ν a lam + lam * t - lam / a +
        |lam| * w / |a|) := by
  have hU := hν.univClass hθ hvlo
  have hl : |lam| ≤ θ / 2 := (hlam.trans (min_le_left _ _)).trans
    ((saTiltRadius_le_half _ _ (by positivity)).trans (by linarith))
  let := hU.isProbabilityMeasure_centeredTilt hl
  have hp : IsProbabilityMeasure ((ν : Measure ℝ).tilted (fun y => lam * y)) := by
    rw [← kernel_centeredTilt_eq_raw]
    infer_instance
  let := hp
  rw [kernel_killed_marked_eq_tilt_endpoint _ ν ha (hU.kernel_integrable_exp_raw hl),
    norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply kernel_norm_killed_le
  intro y
  apply kernel_norm_marked_le
  intro z
  apply kernel_norm_killed_le
  intro u
  have he : (Real.exp (lam * (u - x) / a) • (Icc α (α + w)).indicator φ u) =
      (Icc α (α + w)).indicator (fun z => Real.exp (lam * (z - x) / a) • φ z) u := by
    by_cases hu : u ∈ Icc α (α + w) <;> simp [hu]
  rw [he]
  exact kernel_endpoint_weight_bound hx hφ u


/-- The pure spectral row estimate with arbitrary positive terminal bound. -/
theorem kernel_norm_pure_row_regLaw_scaled (D θ vlo vhi a₀ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (ha₀ : 0 < a₀) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ α w β a : ℝ, 1 ≤ w → a₀ ≤ |a| →
      ∀ φ : ℝ → ℂ, Measurable φ → ∀ M : ℝ, 0 < M → (∀ y, ‖φ y‖ ≤ M) →
      ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ,
        ‖((kStep (Icc α (α + w)) (ν : Measure ℝ) β a)^[n]
          ((Icc α (α + w)).indicator φ)) y‖ ≤
          M * (3 * Real.sqrt (D * w / a₀) *
            Real.exp (-(c * ((n : ℝ) - 1) / (2 * w ^ 2)))) := by
  obtain ⟨c, hc, hb⟩ := kernel_norm_pure_row_regLaw D θ vlo vhi a₀ hD hθ hvlo hv ha₀
  refine ⟨c, hc, ?_⟩
  intro ν hν α w β a hw ha φ hφ M hM hφM n hn y
  let ψ : ℝ → ℂ := fun z => M⁻¹ • φ z
  have hψ : Measurable ψ := by fun_prop
  have hψ1 (z : ℝ) : ‖ψ z‖ ≤ 1 := by
    change ‖M⁻¹ • φ z‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
    calc
      M⁻¹ * ‖φ z‖ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (hφM z) (by positivity)
      _ = 1 := inv_mul_cancel₀ hM.ne'
  have hh := hb ν hν α w β a hw ha ψ hψ hψ1 n hn y
  have he : (Icc α (α + w)).indicator φ =
      fun z => M • (Icc α (α + w)).indicator ψ z := by
    funext z
    by_cases hz : z ∈ Icc α (α + w) <;> simp [hz, ψ, hM.ne']
  rw [he, kernel_killed_const_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hM]
  exact mul_le_mul_of_nonneg_left hh hM.le

/-- The actual tilted law has a uniform spectral row estimate after normalization.
The original slope floor `1/2` becomes `1/4` under the true tilted mean. -/
theorem kernel_norm_tilted_row_regLaw (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ lam : ℝ, |lam| ≤ kernelTiltClassRadius D θ vlo vhi →
      ∀ α w β a : ℝ, 1 ≤ w → 1 / 2 ≤ a →
      ∀ φ : ℝ → ℂ, Measurable φ → ∀ M : ℝ, 0 < M → (∀ y, ‖φ y‖ ≤ M) →
      ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ,
        ‖((kStep (Icc α (α + w)) ((ν : Measure ℝ).tilted (fun x => lam * x)) β a)^[n]
          ((Icc α (α + w)).indicator φ)) y‖ ≤
          M * (3 * Real.sqrt (8 * D * Real.exp θ * w) *
            Real.exp (-(c * ((n : ℝ) - 1) / (2 * w ^ 2)))) := by
  obtain ⟨c, hc, hb⟩ := kernel_norm_pure_row_regLaw_scaled
    (2 * D * Real.exp θ) (θ / 4) (3 * vlo / 16) (5 * vhi) (1 / 4)
    (by positivity) (by positivity) (by positivity) (by linarith) (by norm_num)
  refine ⟨c, hc, ?_⟩
  intro ν hν lam hlam α w β a hw ha φ hφ M hM hφM n hn y
  obtain ⟨hm, ρ, hρ, hreg⟩ :=
    (kernel_regLaw_normalized_tilt D θ vlo vhi hD hθ hvlo hv).2 ν hν lam hlam
  have hmpos : 0 < kernelTiltMean ν lam := by linarith [hm.1]
  have ham : 1 / 4 ≤ |a * kernelTiltMean ν lam| := by
    rw [abs_of_pos (mul_pos (by linarith) hmpos)]
    nlinarith [hm.1]
  have he : kStep (Icc α (α + w)) (ρ : Measure ℝ) β (a * kernelTiltMean ν lam) =
      kStep (Icc α (α + w)) ((ν : Measure ℝ).tilted (fun x => lam * x)) β a := by
    rw [hρ, kernelTiltNormalized, kernel_kStep_map_div _ _ _ _ hmpos.ne',
      kernel_centeredTilt_eq_raw]
  have hh := hb ρ hreg α w β (a * kernelTiltMean ν lam) hw ham φ hφ M hM hφM n hn y
  rw [he] at hh
  have hcoeff : (2 * D * Real.exp θ) * w / (1 / 4) = 8 * D * Real.exp θ * w := by ring
  rwa [hcoeff] at hh

/-- Class-uniform Cramer and spectral exponents for the actual original killed row. -/
theorem kernel_killed_tilt_gap_bound (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ lam : ℝ, |lam| ≤ kernelTiltClassRadius D θ vlo vhi →
      ∀ α w a x : ℝ, 1 ≤ w → 1 / 2 ≤ a → x ∈ Icc α (α + w) →
      ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      ∀ n : ℕ, 1 ≤ n →
        ‖((kStep (Icc α (α + w)) (ν : Measure ℝ) 1 a)^[n]
          ((Icc α (α + w)).indicator φ)) x‖ ≤
          Real.exp (-(n : ℝ) * kernelTiltRate ν a lam + |lam| * w / a) *
            (3 * Real.sqrt (8 * D * Real.exp θ * w) *
              Real.exp (-(c * ((n : ℝ) - 1) / (2 * w ^ 2)))) := by
  obtain ⟨c, hc, hb⟩ := kernel_norm_tilted_row_regLaw D θ vlo vhi hD hθ hvlo hv
  refine ⟨c, hc, ?_⟩
  intro ν hν lam hlam α w a x hw ha hx φ hφ hφ1 n hn
  have ha0 : 0 < a := by linarith
  have hU := hν.univClass hθ hvlo
  have hl : |lam| ≤ θ / 2 := (hlam.trans (min_le_left _ _)).trans
    ((saTiltRadius_le_half _ _ (by positivity)).trans (by linarith))
  let ψ : ℝ → ℂ := (Icc α (α + w)).indicator
    (fun y => Real.exp (lam * (y - x) / a) • φ y)
  have hψ : Measurable ψ := (by fun_prop : Measurable
    (fun y => Real.exp (lam * (y - x) / a) • φ y)).indicator measurableSet_Icc
  have hψM (y : ℝ) : ‖ψ y‖ ≤ Real.exp (|lam| * w / a) := by
    simpa only [ψ, abs_of_pos ha0] using
      kernel_endpoint_weight_bound (a := a) (lam := lam) hx hφ1 y
  have he : (fun y => Real.exp (lam * (y - x) / a) • (Icc α (α + w)).indicator φ y) =
      (Icc α (α + w)).indicator ψ := by
    funext y
    by_cases hy : y ∈ Icc α (α + w) <;> simp [hy, ψ]
  rw [kernel_killed_eq_tilt_endpoint _ ν ha0.ne' (hU.kernel_integrable_exp_raw hl), he,
    norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_add, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  exact hb ν hν lam hlam α w 1 a hw ha ψ hψ _ (Real.exp_pos _) hψM n hn x


/-- Measurability is preserved by each genuine killed iterate. -/
theorem kernel_measurable_killed {J : Set ℝ} (hJ : MeasurableSet J)
    (μ : Measure ℝ) [SFinite μ] (β a : ℝ) {f : ℝ → ℂ} (hf : Measurable f) (n : ℕ) :
    Measurable ((kStep J μ β a)^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact measurable_kStep hJ μ ih

/-- A marked tilted row retains the spectral decay of its longer random segment. -/
theorem kernel_norm_tilted_marked_regLaw (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ lam : ℝ, |lam| ≤ kernelTiltClassRadius D θ vlo vhi →
      ∀ α w β a t : ℝ, 1 ≤ w → 1 / 2 ≤ a →
      ∀ φ : ℝ → ℂ, Measurable φ → ∀ M : ℝ, 0 < M → (∀ y, ‖φ y‖ ≤ M) →
      ∀ l r : ℕ, 1 ≤ max l r → ∀ y : ℝ,
        ‖((kStep (Icc α (α + w)) ((ν : Measure ℝ).tilted (fun x => lam * x)) β a)^[l]
          (kernelMarkedStep (Icc α (α + w)) β a t
            ((kStep (Icc α (α + w)) ((ν : Measure ℝ).tilted (fun x => lam * x)) β a)^[r]
              ((Icc α (α + w)).indicator φ)))) y‖ ≤
          M * (3 * Real.sqrt (8 * D * Real.exp θ * w) *
            Real.exp (-(c * ((max l r : ℕ) - (1 : ℝ)) / (2 * w ^ 2)))) := by
  obtain ⟨c, hc, hb⟩ := kernel_norm_tilted_row_regLaw D θ vlo vhi hD hθ hvlo hv
  refine ⟨c, hc, ?_⟩
  intro ν hν lam hlam α w β a t hw ha φ hφ M hM hφM l r hn y
  have hU := hν.univClass hθ hvlo
  have hl : |lam| ≤ θ / 2 := (hlam.trans (min_le_left _ _)).trans
    ((saTiltRadius_le_half _ _ (by positivity)).trans (by linarith))
  let := hU.isProbabilityMeasure_centeredTilt hl
  have hp : IsProbabilityMeasure ((ν : Measure ℝ).tilted (fun z => lam * z)) := by
    rw [← kernel_centeredTilt_eq_raw]
    infer_instance
  let := hp
  by_cases hlr : l ≤ r
  · rw [max_eq_right hlr] at hn ⊢
    apply kernel_norm_killed_le
    intro z
    apply kernel_norm_marked_le
    intro u
    exact hb ν hν lam hlam α w β a hw ha φ hφ M hM hφM r hn u
  · have hrl : r ≤ l := by omega
    rw [max_eq_left hrl] at hn ⊢
    let u := (kStep (Icc α (α + w)) ((ν : Measure ℝ).tilted (fun z => lam * z)) β a)^[r]
      ((Icc α (α + w)).indicator φ)
    let G := kernelMarkedStep (Icc α (α + w)) β a t u
    have hu : Measurable u := kernel_measurable_killed measurableSet_Icc _ _ _
      (hφ.indicator measurableSet_Icc) r
    have hG : Measurable G :=
      (hu.comp (by fun_prop : Measurable (fun z : ℝ => z + β - a * t))).indicator measurableSet_Icc
    have huM (z : ℝ) : ‖u z‖ ≤ M := by
      apply kernel_norm_killed_le
      intro v
      by_cases hv : v ∈ Icc α (α + w)
      · simpa only [indicator_of_mem hv] using hφM v
      · simp only [indicator_of_notMem hv, norm_zero]
        exact hM.le
    have hGM (z : ℝ) : ‖G z‖ ≤ M := kernel_norm_marked_le huM z
    have hJG : (Icc α (α + w)).indicator G = G := by
      funext z
      by_cases hz : z ∈ Icc α (α + w) <;> simp [hz, G, kernelMarkedStep]
    have hh := hb ν hν lam hlam α w β a hw ha G hG M hM hGM l hn y
    rwa [hJG] at hh

/-- The actual marked row has both the exact Cramer factor and a class spectral factor. -/
theorem kernel_killed_marked_tilt_gap_bound (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ lam : ℝ, |lam| ≤ kernelTiltClassRadius D θ vlo vhi →
      ∀ α w a x t : ℝ, 1 ≤ w → 1 / 2 ≤ a → x ∈ Icc α (α + w) →
      ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      ∀ l r : ℕ, 1 ≤ max l r →
        ‖((kStep (Icc α (α + w)) (ν : Measure ℝ) 1 a)^[l]
          (kernelMarkedStep (Icc α (α + w)) 1 a t
            ((kStep (Icc α (α + w)) (ν : Measure ℝ) 1 a)^[r]
              ((Icc α (α + w)).indicator φ)))) x‖ ≤
          Real.exp (-((l : ℝ) + r) * kernelTiltRate ν a lam + lam * t - lam / a +
            |lam| * w / a) *
            (3 * Real.sqrt (8 * D * Real.exp θ * w) *
              Real.exp (-(c * ((max l r : ℕ) - (1 : ℝ)) / (2 * w ^ 2)))) := by
  obtain ⟨c, hc, hb⟩ := kernel_norm_tilted_marked_regLaw D θ vlo vhi hD hθ hvlo hv
  refine ⟨c, hc, ?_⟩
  intro ν hν lam hlam α w a x t hw ha hx φ hφ hφ1 l r hn
  have ha0 : 0 < a := by linarith
  have hU := hν.univClass hθ hvlo
  have hl : |lam| ≤ θ / 2 := (hlam.trans (min_le_left _ _)).trans
    ((saTiltRadius_le_half _ _ (by positivity)).trans (by linarith))
  let ψ : ℝ → ℂ := (Icc α (α + w)).indicator
    (fun y => Real.exp (lam * (y - x) / a) • φ y)
  have hψ : Measurable ψ := (by fun_prop : Measurable
    (fun y => Real.exp (lam * (y - x) / a) • φ y)).indicator measurableSet_Icc
  have hψM (y : ℝ) : ‖ψ y‖ ≤ Real.exp (|lam| * w / a) := by
    simpa only [ψ, abs_of_pos ha0] using
      kernel_endpoint_weight_bound (a := a) (lam := lam) hx hφ1 y
  have he : (fun y => Real.exp (lam * (y - x) / a) • (Icc α (α + w)).indicator φ y) =
      (Icc α (α + w)).indicator ψ := by
    funext y
    by_cases hy : y ∈ Icc α (α + w) <;> simp [hy, ψ]
  rw [kernel_killed_marked_eq_tilt_endpoint _ ν ha0.ne' (hU.kernel_integrable_exp_raw hl), he,
    norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_add, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  exact hb ν hν lam hlam α w 1 a t hw ha ψ hψ _ (Real.exp_pos _) hψM l r hn x

end
end PGM
