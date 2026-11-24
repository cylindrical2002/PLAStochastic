import PLAStochastic.Index.GEP.Kernel.Marked.Pin.AllSlopes
import PLAStochastic.Index.GEP.Kernel.Row.Green

/-! # Coarse genuine outer Green bounds over all slopes -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 800000

/-- Exact conversion of the real survival mass to the existing pure complex
killed iterate, for all times including zero. -/
theorem kernel_surv_eq_norm_killed {J : Set ℝ} (hJ : MeasurableSet J)
    (ν : ProbabilityMeasure ℝ) (β a : ℝ) (n : ℕ) (y : ℝ) :
    krSurv J (ν : Measure ℝ) β a n y =
      ‖((kStep J (ν : Measure ℝ) β a)^[n] (J.indicator (fun _ => (1 : ℂ)))) y‖ := by
  have he : J.indicator (fun _ => (1 : ℂ)) =
      fun u => ((J.indicator (fun _ => (1 : ℝ)) u : ℝ) : ℂ) := by
    funext u
    by_cases hu : u ∈ J <;> simp [hu]
  rw [he, kernel_killed_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact (abs_of_nonneg (krSurv_nonneg hJ ν β a n y)).symm

/-- Reflection changes the actual direction of every step, including all
intermediate killing tests. -/
theorem kernel_surv_reflect (ν : ProbabilityMeasure ℝ) (α w β a : ℝ) (n : ℕ) (y : ℝ) :
    krSurv (Icc α (α + w)) (ν : Measure ℝ) (-β) (-a) n y =
      krSurv (Icc (-α - w) (-α)) (ν : Measure ℝ) β a n (-y) := by
  rw [krSurv_eq_integral measurableSet_Icc, krSurv_eq_integral measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with g
  unfold krAlive
  apply Finset.prod_congr rfl
  intro j hj
  have he : kWalk (-y) β a g j = -kWalk y (-β) (-a) g j := by
    unfold kWalk
    ring
  rw [he]
  have hm : kWalk y (-β) (-a) g j ∈ Icc α (α + w) ↔
      -kWalk y (-β) (-a) g j ∈ Icc (-α - w) (-α) := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  by_cases hj' : kWalk y (-β) (-a) g j ∈ Icc α (α + w)
  · simp only [indicator_of_mem hj', indicator_of_mem (hm.mp hj')]
  · simp only [indicator_of_notMem hj', indicator_of_notMem (not_iff_not.mpr hm |>.mp hj')]

/-- The actual survival sequence has a pure exponential bound with a fixed
linear width prefactor at every slope above a fixed positive floor. -/
theorem kernel_regLaw_surv_spectral_all (D θ vlo vhi a₀ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (ha₀ : 0 < a₀) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ α w β a : ℝ, 1 ≤ w → a₀ ≤ |a| → ∀ n : ℕ, ∀ y : ℝ,
        krSurv (Icc α (α + w)) (ν : Measure ℝ) β a n y ≤
          K * w * Real.exp (-c * n / w ^ 2) := by
  obtain ⟨c, hc, hb⟩ := kernel_norm_pure_row_regLaw D θ vlo vhi a₀ hD hθ hvlo hv ha₀
  let K := 1 + 3 * (1 + D / a₀) * Real.exp (c / 2)
  have hK : 0 < K := by positivity
  refine ⟨c / 2, K, by positivity, hK, ?_⟩
  intro ν hν α w β a hw ha n y
  have hw0 : 0 < w := by linarith
  cases n with
  | zero =>
    have hcoef : 1 ≤ K * w := by
      have hK1 : 1 ≤ K := by
        have h0 : 0 ≤ 3 * (1 + D / a₀) * Real.exp (c / 2) := by positivity
        dsimp [K]
        linarith
      nlinarith
    simpa only [Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one] using
      (krSurv_le_one measurableSet_Icc ν β a 0 y).trans hcoef
  | succ n =>
    rw [kernel_surv_eq_norm_killed measurableSet_Icc]
    have hh := hb ν hν α w β a hw ha (fun _ => (1 : ℂ)) measurable_const (by simp)
      (n + 1) (by omega) y
    have hs : Real.sqrt (D * w / a₀) ≤ (1 + D / a₀) * w := by
      have hs0 := Real.sqrt_nonneg (D * w / a₀)
      have hs2 := Real.sq_sqrt (show 0 ≤ D * w / a₀ by positivity)
      have hDw : 0 ≤ D * w / a₀ := by positivity
      have hs1 : Real.sqrt (D * w / a₀) ≤ 1 + D * w / a₀ := by
        nlinarith [sq_nonneg (Real.sqrt (D * w / a₀) - 1)]
      calc _ ≤ 1 + D * w / a₀ := hs1
        _ ≤ (1 + D / a₀) * w := by
          have he : (1 + D / a₀) * w = w + D * w / a₀ := by ring
          rw [he]
          linarith
    have he : -(c * (((n + 1 : ℕ) : ℝ) - 1) / (2 * w ^ 2)) ≤
        c / 2 + (-(c / 2) * (n + 1 : ℕ) / w ^ 2) := by
      apply (mul_le_mul_iff_right₀ (show 0 < 2 * w ^ 2 by positivity)).mp
      field_simp
      nlinarith [show 1 ≤ w ^ 2 by nlinarith]
    have hh' := mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num : 0 ≤ (3 : ℝ)))
      (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (by positivity : 0 ≤ 3 * ((1 + D / a₀) * w))
    apply hh.trans (hh'.trans ?_)
    rw [Real.exp_add]
    dsimp [K]
    nlinarith [Real.exp_pos (-(c / 2) * (n + 1 : ℕ) / w ^ 2)]

/-- The geometric denominator costs at most one inverse rate. This convenient
coarse form keeps polynomial width exponents explicit. -/
theorem kernel_one_div_one_sub_exp_neg_le {u : ℝ} (hu : 0 < u) :
    1 / (1 - Real.exp (-u)) ≤ 1 + 1 / u := by
  have he : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
  have hlo : 0 < 1 - Real.exp (-u) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hex : 1 + u ≤ Real.exp u := by simpa [add_comm] using Real.add_one_le_exp u
  rw [div_le_iff₀ hlo, Real.exp_neg]
  apply (mul_le_mul_iff_right₀ (mul_pos hu (Real.exp_pos u))).mp
  field_simp
  nlinarith

/-- Summing a class-uniform spectral survival bound gives a fixed cubic width
budget, independent of every later input-tail weight. -/
theorem kernel_regLaw_outer_green_large (D θ vlo vhi a₀ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (ha₀ : 0 < a₀) :
    ∃ K : ℝ, 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ α w β a : ℝ, 1 ≤ w → a₀ ≤ |a| → ∀ y : ℝ,
        Summable (fun n : ℕ => krSurv (Icc α (α + w)) (ν : Measure ℝ) β a n y) ∧
        (∑' n : ℕ, krSurv (Icc α (α + w)) (ν : Measure ℝ) β a n y) ≤ K * w ^ 3 := by
  obtain ⟨c, K, hc, hK, hb⟩ := kernel_regLaw_surv_spectral_all D θ vlo vhi a₀ hD hθ hvlo hv ha₀
  refine ⟨K * (1 + 1 / c), by positivity, ?_⟩
  intro ν hν α w β a hw ha y
  have hw0 : 0 < w := by linarith
  let u := c / w ^ 2
  have hu : 0 < u := by positivity
  have hr : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : Summable (fun n : ℕ => K * w * Real.exp (-u) ^ n) :=
    (summable_geometric_of_lt_one (Real.exp_nonneg _) hr).mul_left (K * w)
  have hmaj (n : ℕ) : krSurv (Icc α (α + w)) (ν : Measure ℝ) β a n y ≤
      K * w * Real.exp (-u) ^ n := by
    rw [← Real.exp_nat_mul]
    convert hb ν hν α w β a hw ha n y using 1
    dsimp [u]
    congr 2
    ring
  have hs := Summable.of_nonneg_of_le (fun n => krSurv_nonneg measurableSet_Icc ν β a n y) hmaj hgeom
  refine ⟨hs, ?_⟩
  apply (hs.tsum_le_tsum hmaj hgeom).trans
  rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_nonneg _) hr]
  have hh := mul_le_mul_of_nonneg_left (kernel_one_div_one_sub_exp_neg_le hu)
    (show 0 ≤ K * w by positivity)
  rw [← one_div]
  apply hh.trans
  dsimp [u]
  have he : 1 / (c / w ^ 2) = w ^ 2 / c := by field_simp
  rw [he]
  have hw2 : 1 ≤ w ^ 2 := by nlinarith
  calc
    _ ≤ K * w * (w ^ 2 + w ^ 2 / c) :=
      mul_le_mul_of_nonneg_left (by linarith : 1 + w ^ 2 / c ≤ w ^ 2 + w ^ 2 / c) (by positivity)
    _ = _ := by ring

/-- Below slope one half, a fixed small positive tilt gives exponential
survival decay as soon as time exceeds eight band widths. -/
theorem kernel_regLaw_surv_small_slope (D θ vlo vhi : ℝ)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ α w a : ℝ, 0 < w → 0 < a → a ≤ 1 / 2 →
      ∀ β a' : ℝ, (β = 1 ∧ a' = a) ∨ (β = -1 ∧ a' = -a) →
      ∀ n : ℕ, 8 * w ≤ (n : ℝ) → ∀ y : ℝ,
        krSurv (Icc α (α + w)) (ν : Measure ℝ) β a' n y ≤ Real.exp (-c * n) := by
  obtain ⟨lam, hlam, _, hlθ, hlR, hrate⟩ :=
    kernel_regLaw_arbitrary_small_tilt D θ vlo vhi 1 hθ hvlo hv (by norm_num)
  refine ⟨lam / 4, by positivity, ?_⟩
  intro ν hν α w a hw ha halo β a' hdir n hn y
  have hforward (α y : ℝ) :
      krSurv (Icc α (α + w)) (ν : Measure ℝ) 1 a n y ≤ Real.exp (-(lam / 4) * n) := by
    by_cases hy : y ∈ Icc α (α + w)
    · have hb := hν.kernel_killed_tilt_bound hθ hvlo ha.ne'
        (by rwa [abs_of_pos hlam]) hy (fun _ => (1 : ℂ)) (by simp) n
      rw [← kernel_surv_eq_norm_killed measurableSet_Icc ν 1 a n y] at hb
      apply hb.trans
      apply Real.exp_le_exp.mpr
      rw [abs_of_pos hlam, abs_of_pos ha]
      have hr := mul_le_mul_of_nonneg_left (hrate ν hν a ha halo) (Nat.cast_nonneg (α := ℝ) n)
      have he : -((n : ℝ) * (lam / (4 * a))) + lam * w / a ≤ -(lam / 4) * n := by
        apply (mul_le_mul_iff_right₀ (show 0 < 4 * a by positivity)).mp
        field_simp
        have h₁ := mul_le_mul_of_nonneg_left hn hlam.le
        have h₂ := mul_le_mul_of_nonneg_left halo (show 0 ≤ lam * n by positivity)
        nlinarith
      linarith
    · rw [krSurv_eq_zero_of_notMem hy]
      exact Real.exp_nonneg _
  rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hforward α y
  · have hh := kernel_surv_reflect ν α w 1 a n y
    have he : -α - w + w = -α := by ring
    rw [hh]
    simpa only [he] using hforward (-α - w) (-y)

/-- Summation of a bounded head followed by an exponential tail, with an
explicit linear width budget. -/
theorem kernel_sum_head_exp_le {F : ℕ → ℝ} (hF : ∀ n, 0 ≤ F n) (hF1 : ∀ n, F n ≤ 1)
    {A c w : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hw : 1 ≤ w)
    (hb : ∀ n : ℕ, A * w ≤ n → F n ≤ Real.exp (-c * n)) (M : ℕ) :
    ∑ n ∈ Finset.range M, F n ≤ (A + 2 + 1 / c) * w := by
  let N : ℕ := ⌈A * w⌉₊
  have hN : A * w ≤ (N : ℝ) := Nat.le_ceil _
  have hNhi : (N : ℝ) ≤ A * w + 1 := by
    exact (Nat.ceil_lt_add_one (mul_nonneg hA (by linarith))).le
  have hhead : ∑ n ∈ Finset.range N, F n ≤ N := by
    simpa using Finset.sum_le_sum (s := Finset.range N) (fun n _ => hF1 n)
  have htail : ∑ j ∈ Finset.range (M - N), F (N + j) ≤ 1 + 1 / c := by
    have hr : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    apply (Finset.sum_le_sum (fun j _ => show F (N + j) ≤ Real.exp (-c) ^ j from ?_)).trans
      ((kr_geom_sum_le (Real.exp_nonneg _) hr (M - N)).trans (kernel_one_div_one_sub_exp_neg_le hc))
    apply (hb (N + j) (by push_cast; linarith)).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hh := kr_sum_split hF N M
  have hcoef : 0 ≤ 1 + 1 / c := by positivity
  have hbudget := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2 + 1 / c by positivity)
  nlinarith

/-- The two genuine directions have a linear outer Green bound at every
small positive slope, uniformly down to slope zero. -/
theorem kernel_regLaw_outer_green_small (D θ vlo vhi : ℝ)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ K : ℝ, 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ α w a : ℝ, 1 ≤ w → 0 < a → a ≤ 1 / 2 →
      ∀ β a' : ℝ, (β = 1 ∧ a' = a) ∨ (β = -1 ∧ a' = -a) → ∀ y : ℝ,
        Summable (fun n : ℕ => krSurv (Icc α (α + w)) (ν : Measure ℝ) β a' n y) ∧
        (∑' n : ℕ, krSurv (Icc α (α + w)) (ν : Measure ℝ) β a' n y) ≤ K * w := by
  obtain ⟨c, hc, hb⟩ := kernel_regLaw_surv_small_slope D θ vlo vhi hθ hvlo hv
  refine ⟨10 + 1 / c, by positivity, ?_⟩
  intro ν hν α w a hw ha halo β a' hdir y
  have hF n := krSurv_nonneg (J := Icc α (α + w)) measurableSet_Icc ν β a' n y
  have hsum (M : ℕ) :
      ∑ n ∈ Finset.range M, krSurv (Icc α (α + w)) (ν : Measure ℝ) β a' n y ≤ (10 + 1 / c) * w := by
    have hh := kernel_sum_head_exp_le hF (fun n => krSurv_le_one measurableSet_Icc ν β a' n y)
      (show 0 ≤ (8 : ℝ) by norm_num) hc hw
      (fun n hn => hb ν hν α w a (by linarith) ha halo β a' hdir n hn y) M
    norm_num at hh ⊢
    exact hh
  exact ⟨summable_of_sum_range_le hF hsum, Real.tsum_le_of_sum_range_le hF hsum⟩

end
end PGM
