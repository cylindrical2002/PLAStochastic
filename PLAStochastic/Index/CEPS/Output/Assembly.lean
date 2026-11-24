import PLAStochastic.Index.CEPS.Output.PerLength
import PLAStochastic.Index.GEP.OrbitClosure.RegularClass

/-!
# Track O: from the canonical iid space to cones, and the stopping weights

* `setIntegral_stop_eq_cone`: on `{T = n}` the stopped sum is `S_n`, the event depends on the
  first `n` gaps only, and the first `n` gaps have the density `∏_l f(x_l)`; hence
  `∫_{T = n} e^{iτ S_n} = ∫ coneIntegrand {stopsAt eps} f τ`.
* `not_stopsAt_of_le`: no stop happens at `n ≤ 2ε` (the constant line fits).
* `outMeasure_stop_le_min`: for high parts of size at most `r`, the long and short tails of
  `Tails` combine into `μ{T = n} ≤ W^{|H|} min(L_n, S_n)` with explicit `L_n = stopLong` and
  `S_n = stopShort` (`regular class` constants of `RegLaw`).
* `min_stop_rpow_le`: for `n > 2ε ≥ 2`, `min(L_n, S_n)^{1/4} ≤ K e^{-a n/ε²} e^{-b ε²/n}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal

namespace PGM

variable {r : ℕ} {E κ : ℝ} {f : ℝ → ℝ} {ν : ProbabilityMeasure ℝ}

/-- **The stopped integral on `{T = n}` is a cone integral.** -/
theorem setIntegral_stop_eq_cone (hpos : ∀ x, 0 ≤ f x) (hfm : Measurable f)
    (hν : (ν : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f x)) (eps τ : ℝ)
    (n : ℕ) :
    ∫ g in {g : ℕ → ℝ | gapSegLen eps g = n},
        Complex.exp (↑(τ * gapKeys g n) * Complex.I) ∂(iidLaw ν) =
      ∫ x, coneIntegrand {z : Fin n → ℝ | stopsAt eps z} f τ x := by
  classical
  set A := {z : Fin n → ℝ | stopsAt eps z} with hAdef
  have hA : MeasurableSet A := measurableSet_stopsAt eps n
  set G : (Fin n → ℝ) → ℂ :=
    A.indicator fun z => Complex.exp (↑(τ * ∑ l, z l) * Complex.I) with hG
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ hA
    exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_const.mul (Finset.measurable_sum _ fun l _ => measurable_pi_apply l))).mul_const _)
  have hT : MeasurableSet {g : ℕ → ℝ | gapSegLen eps g = n} :=
    (isStoppingRule_gapSegLen eps).measurable (measurableSet_singleton _)
  have hres : Measurable fun (g : ℕ → ℝ) (i : Fin n) => g i :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have h1 : ∫ g in {g : ℕ → ℝ | gapSegLen eps g = n},
      Complex.exp (↑(τ * gapKeys g n) * Complex.I) ∂(iidLaw ν) =
      ∫ g, G (fun i : Fin n => g i) ∂(iidLaw ν) := by
    rw [← integral_indicator hT]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [hG]
    by_cases hg : gapSegLen eps g = n
    · have hmem : (fun i : Fin n => g i) ∈ A := (stopsAt_iff_segLen g n).mpr hg
      rw [indicator_of_mem (show g ∈ {g : ℕ → ℝ | gapSegLen eps g = n} from hg),
        indicator_of_mem hmem]
      simp only
      rw [Fin.sum_univ_eq_sum_range (fun i => g i) n]
      rfl
    · have hmem : (fun i : Fin n => g i) ∉ A := fun h => hg ((stopsAt_iff_segLen g n).mp h)
      rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | gapSegLen eps g = n} from hg),
        indicator_of_notMem hmem]
  have h2 : ∫ g, G (fun i : Fin n => g i) ∂(iidLaw ν) =
      ∫ z, G z ∂(Measure.pi fun _ => (ν : Measure ℝ)) := by
    rw [← iidLaw_map_fin ν n, integral_map hres.aemeasurable hGm.aestronglyMeasurable]
  have hρ : ∀ _ : Fin n, Measurable fun x => ENNReal.ofReal (f x) := fun _ => hfm.ennreal_ofReal
  have h3 : (Measure.pi fun _ : Fin n => (ν : Measure ℝ)) =
      volume.withDensity fun z : Fin n → ℝ => ∏ l, ENNReal.ofReal (f (z l)) := by
    have e : (fun _ : Fin n => (ν : Measure ℝ)) =
        fun _ => volume.withDensity fun x => ENNReal.ofReal (f x) := funext fun _ => hν
    rw [e, pi_withDensity_fin volume (fun _ x => ENNReal.ofReal (f x)) hρ, ← volume_pi]
  have hpm : Measurable fun z : Fin n → ℝ => ∏ l, ENNReal.ofReal (f (z l)) :=
    Finset.measurable_fun_prod (f := fun l (z : Fin n → ℝ) => ENNReal.ofReal (f (z l))) _
      fun l _ => (hρ l).comp (measurable_pi_apply l)
  rw [h1, h2, h3, integral_withDensity_eq_integral_toReal_smul hpm
    (Eventually.of_forall fun z => ENNReal.prod_lt_top fun l _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hG, coneIntegrand]
  rw [ENNReal.toReal_prod]
  simp_rw [ENNReal.toReal_ofReal (hpos _)]
  by_cases hz : z ∈ A
  · rw [indicator_of_mem hz, indicator_of_mem hz, Complex.real_smul, mul_comm]
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, smul_zero]

/-- No stop happens at a length `n ≤ 2ε`. -/
theorem not_stopsAt_of_le {eps : ℝ} (heps : 0 ≤ eps) {n : ℕ} (hn : (n : ℝ) ≤ 2 * eps)
    (z : Fin n → ℝ) : ¬ stopsAt eps z := by
  intro hz
  set C := ConstantLineLengthCertificate.of_nonneg heps
  have hq : n + 1 ≤ C.q := by
    have : (n : ℝ) < C.q := lt_of_le_of_lt hn C.lower
    exact_mod_cast this
  exact hz.2 (prefixAffineFeasible_constantLine C hq)

/-! ## The stopping weights -/

/-- The long-tail weight `L_n`. -/
def stopLong (r : ℕ) (vlo eps : ℝ) (n : ℕ) : ℝ :=
  72 / 71 * Real.exp (-(tailRate * regV vlo) * ((n - 1) / (r + 1) : ℕ) / eps ^ 2)

/-- The short-tail weight `S_n`. -/
def stopShort (r : ℕ) (D θ E κ eps : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(κ / 2 * (eps / 2))) +
    2 * Real.exp (-(bernsteinRate (θ / 2) (2 * D / θ) * min ((eps / 4) ^ 2 / n) (eps / 4))) +
    Real.exp (-(κ / 2 * (eps / 4))) * max 1 (outWeightBound E κ) ^ r

theorem stopLong_nonneg (r : ℕ) (vlo eps : ℝ) (n : ℕ) : 0 ≤ stopLong r vlo eps n := by
  unfold stopLong; positivity

theorem stopShort_nonneg (r : ℕ) (D θ E κ eps : ℝ) (n : ℕ) : 0 ≤ stopShort r D θ E κ eps n := by
  unfold stopShort
  have : 0 ≤ max 1 (outWeightBound E κ) := le_trans zero_le_one (le_max_left _ _)
  positivity

/-- **The stopping weight of a product with inserted factors.** -/
theorem outMeasure_stop_le_min (h : OutInput r E κ f ν) {D θ vlo vhi : ℝ}
    (hreg : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo) {eps : ℝ}
    (heps : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps) {n : ℕ} (hn : 1 ≤ n) (β : Fin n → ℕ)
    (hβ : ∀ l, β l ≤ r) (hH : #(outSupp β) ≤ r) :
    outMeasure f β {z | stopsAt eps z} ≤
      ENNReal.ofReal (outWeightBound E κ ^ #(outSupp β) *
        min (stopLong r vlo eps n) (stopShort r D θ E κ eps n)) := by
  set Wb := outWeightBound E κ with hWbdef
  have hWb : 0 ≤ Wb := h.outWeightBound_nonneg
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps
  have hmom := hreg.momClass hθ hvlo
  have hexp := hreg.expMom hθ
  have hκ2 : 0 ≤ κ / 2 := by have := h.κpos; positivity
  have hβ1 : ∀ l, β l ≤ max r 1 := fun l => (hβ l).trans (le_max_left _ _)
  have hM : ∏ l ∈ outSupp β, outMass f (β l) ≤ ENNReal.ofReal (Wb ^ #(outSupp β)) := by
    rw [ENNReal.ofReal_pow hWb, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun l _ =>
      (outMass_le_outWeight f hκ2 _).trans (h.outWeight_le (hβ1 l))
  have hW : ∏ l ∈ outSupp β, outWeight f (κ / 2) (β l) ≤ ENNReal.ofReal (Wb ^ #(outSupp β)) := by
    rw [ENNReal.ofReal_pow hWb, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun l _ => h.outWeight_le (hβ1 l)
  have hlong := outMeasure_stop_le_long h.pos h.density (regV_pos hvlo) heps hmom hn β hH
  have hshort := outMeasure_stop_le_short (eps := eps) h.pos h.measurable_f h.density hκ2
    (by positivity : 0 < θ / 2) h.measure_Iic hreg.mean hexp hn (by linarith) β
  have hL : outMeasure f β {z | stopsAt eps z} ≤
      ENNReal.ofReal (Wb ^ #(outSupp β) * stopLong r vlo eps n) := by
    refine hlong.trans ?_
    rw [ENNReal.ofReal_mul (pow_nonneg hWb _)]
    exact mul_le_mul' hM le_rfl
  have hW0 : (∫⁻ x, ENNReal.ofReal (Real.exp (κ / 2 * |x - 1|)) ∂(ν : Measure ℝ)) ^
      #(outSupp β) ≤ ENNReal.ofReal (max 1 Wb ^ r) := by
    refine (pow_le_pow_left' h.lintegral_exp_le _).trans ?_
    rw [← ENNReal.ofReal_pow hWb]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Wb ^ #(outSupp β) ≤ (max 1 Wb) ^ #(outSupp β) :=
          pow_le_pow_left₀ hWb (le_max_right _ _) _
      _ ≤ (max 1 Wb) ^ r := pow_le_pow_right₀ (le_max_left _ _) hH
  have hS : outMeasure f β {z | stopsAt eps z} ≤
      ENNReal.ofReal (Wb ^ #(outSupp β) * stopShort r D θ E κ eps n) := by
    refine hshort.trans ?_
    have hw0 : 0 ≤ Wb ^ #(outSupp β) := pow_nonneg hWb _
    have hm0 : 0 ≤ max 1 Wb ^ r := pow_nonneg (le_trans zero_le_one (le_max_left _ _)) r
    calc ENNReal.ofReal (Real.exp (-(κ / 2 * (eps / 2)))) *
          ∏ l ∈ outSupp β, outWeight f (κ / 2) (β l) +
        (∏ l ∈ outSupp β, outMass f (β l)) *
          (ENNReal.ofReal (2 * Real.exp (-(bernsteinRate (θ / 2) (2 * D / θ) *
            min ((eps / 4) ^ 2 / n) (eps / 4)))) +
          ENNReal.ofReal (Real.exp (-(κ / 2 * (eps / 4)))) *
            (∫⁻ x, ENNReal.ofReal (Real.exp (κ / 2 * |x - 1|)) ∂(ν : Measure ℝ)) ^
              #(outSupp β))
        ≤ ENNReal.ofReal (Real.exp (-(κ / 2 * (eps / 2)))) * ENNReal.ofReal (Wb ^ #(outSupp β)) +
          ENNReal.ofReal (Wb ^ #(outSupp β)) *
            (ENNReal.ofReal (2 * Real.exp (-(bernsteinRate (θ / 2) (2 * D / θ) *
              min ((eps / 4) ^ 2 / n) (eps / 4)))) +
            ENNReal.ofReal (Real.exp (-(κ / 2 * (eps / 4)))) *
              ENNReal.ofReal (max 1 Wb ^ r)) := by
          gcongr
      _ = ENNReal.ofReal (Wb ^ #(outSupp β) * stopShort r D θ E κ eps n) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [stopShort, ← hWbdef]
          ring
  rw [mul_min_of_nonneg _ _ (pow_nonneg hWb _), ENNReal.ofReal_min]
  exact le_min hL hS

/-! ## The two-scale majorant of the stopping weight -/

/-- The long-time rate. -/
def stopRateLong (r : ℕ) (vlo : ℝ) : ℝ := tailRate * regV vlo / (8 * (r + 1))

/-- The short-time rate. -/
def stopRateShort (D θ κ : ℝ) : ℝ := min (κ / 4) (bernsteinRate (θ / 2) (2 * D / θ) / 16) / 8

/-- The constant of the two-scale majorant. -/
def stopConst (r : ℕ) (vlo E κ : ℝ) : ℝ :=
  (72 / 71 * Real.exp (tailRate * regV vlo)) ^ (1 / 8 : ℝ) *
    (3 + max 1 (outWeightBound E κ) ^ r) ^ (1 / 8 : ℝ)

theorem stopRateLong_pos (r : ℕ) {vlo : ℝ} (hvlo : 0 < vlo) : 0 < stopRateLong r vlo := by
  have := regV_pos hvlo
  have := tailRate_pos
  unfold stopRateLong; positivity

theorem stopRateShort_pos {D θ κ : ℝ} (hD : 0 < D) (hθ : 0 < θ) (hκ : 0 < κ) :
    0 < stopRateShort D θ κ := by
  have hc := bernsteinRate_pos (by positivity : 0 < θ / 2) (by positivity : 0 < 2 * D / θ)
  unfold stopRateShort
  exact div_pos (lt_min (by positivity) (by positivity)) (by norm_num)

theorem stopConst_nonneg (r : ℕ) (vlo E κ : ℝ) : 0 ≤ stopConst r vlo E κ := by
  unfold stopConst
  have : 0 ≤ max 1 (outWeightBound E κ) := le_trans zero_le_one (le_max_left _ _)
  positivity

theorem exp_rpow_eighth (x : ℝ) : Real.exp x ^ (1 / 8 : ℝ) = Real.exp (x / 8) := by
  rw [← Real.exp_mul]; ring_nf

/-- **The two-scale majorant** of `min(L_n, S_n)^{1/4}`. -/
theorem min_stop_rpow_le {D θ vlo : ℝ} (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) {eps : ℝ}
    (heps : 1 ≤ eps) {n : ℕ} (hn : 2 * eps < n) (hκ : 0 < κ) :
    min (stopLong r vlo eps n) (stopShort r D θ E κ eps n) ^ (1 / 4 : ℝ) ≤
      stopConst r vlo E κ * (Real.exp (-(stopRateLong r vlo * n / eps ^ 2)) *
        Real.exp (-(stopRateShort D θ κ * eps ^ 2 / n))) := by
  set L := stopLong r vlo eps n with hLdef
  set S := stopShort r D θ E κ eps n with hSdef
  set lam := tailRate * regV vlo with hlam
  have hlam0 : 0 < lam := mul_pos tailRate_pos (regV_pos hvlo)
  set c := bernsteinRate (θ / 2) (2 * D / θ) with hc
  have hc0 : 0 < c := bernsteinRate_pos (by positivity) (by positivity)
  set M' := max 1 (outWeightBound E κ) ^ r with hM'
  have hM'0 : 0 ≤ M' := pow_nonneg (le_trans zero_le_one (le_max_left _ _)) r
  have heps0 : 0 < eps := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hL0 : 0 ≤ L := stopLong_nonneg r vlo eps n
  have hS0 : 0 ≤ S := stopShort_nonneg r D θ E κ eps n
  -- the long weight
  set KL := 72 / 71 * Real.exp lam with hKL
  have hL : L ≤ KL * Real.exp (-(8 * stopRateLong r vlo) * n / eps ^ 2) := by
    set w := (n - 1) / (r + 1) with hw
    have hdiv := Nat.div_add_mod (n - 1) (r + 1)
    rw [← hw] at hdiv
    have hmod := Nat.mod_lt (n - 1) (show 0 < r + 1 by omega)
    have hnw : (n : ℝ) ≤ (r + 1) * (w + 1) := by
      have : n ≤ (r + 1) * (w + 1) := by
        have : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
        rw [mul_add, mul_one]; omega
      exact_mod_cast this
    have hw' : (n : ℝ) / (r + 1) - 1 ≤ w := by
      rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
      linarith
    rw [hLdef, stopLong, hKL, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h8 : 8 * stopRateLong r vlo = lam / (r + 1) := by
      unfold stopRateLong; rw [← hlam]; field_simp
    rw [h8, ← hw]
    have he2 : 1 ≤ eps ^ 2 := by nlinarith
    have h1 : -lam * w / eps ^ 2 ≤ -lam * ((n : ℝ) / (r + 1) - 1) / eps ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    have h2 : -lam * ((n : ℝ) / (r + 1) - 1) / eps ^ 2 =
        -(lam / (r + 1)) * n / eps ^ 2 + lam / eps ^ 2 := by ring
    have h3 : lam / eps ^ 2 ≤ lam := div_le_self hlam0.le he2
    linarith
  -- the short weight
  set KS := 3 + M' with hKS
  have hS : S ≤ KS * Real.exp (-(8 * stopRateShort D θ κ) * (eps ^ 2 / n)) := by
    set t := eps ^ 2 / n with ht
    have ht0 : 0 ≤ t := by positivity
    have htε : t ≤ eps / 2 := by
      rw [ht, div_le_iff₀ hn0]; nlinarith
    have h8 : 8 * stopRateShort D θ κ = min (κ / 4) (c / 16) := by
      unfold stopRateShort; rw [← hc]; ring
    rw [h8]
    set m := min (κ / 4) (c / 16) with hm
    have hm1 : m ≤ κ / 4 := min_le_left _ _
    have hm2 : m ≤ c / 16 := min_le_right _ _
    have hm0 : 0 ≤ m := le_min (by positivity) (by positivity)
    have e1 : Real.exp (-(κ / 2 * (eps / 2))) ≤ Real.exp (-m * t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hmin : min ((eps / 4) ^ 2 / n) (eps / 4) = t / 16 := by
      have : (eps / 4) ^ 2 / n = t / 16 := by rw [ht]; ring
      rw [this]
      exact min_eq_left (by linarith)
    have e2 : Real.exp (-(c * min ((eps / 4) ^ 2 / n) (eps / 4))) ≤ Real.exp (-m * t) := by
      rw [hmin]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have e3 : Real.exp (-(κ / 2 * (eps / 4))) ≤ Real.exp (-m * t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [hSdef, stopShort, ← hc, ← hM', hKS]
    calc Real.exp (-(κ / 2 * (eps / 2))) + 2 * Real.exp (-(c * min ((eps / 4) ^ 2 / n) (eps / 4)))
          + Real.exp (-(κ / 2 * (eps / 4))) * M'
        ≤ Real.exp (-m * t) + 2 * Real.exp (-m * t) + Real.exp (-m * t) * M' := by
          gcongr
      _ = (3 + M') * Real.exp (-m * t) := by ring
  -- combine
  have hmin : min L S ≤ L ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) := by
    have h0 : 0 ≤ min L S := le_min hL0 hS0
    have e : min L S = min L S ^ (1 / 2 : ℝ) * min L S ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add' h0 (by norm_num)]; norm_num
    rw [e]
    exact mul_le_mul (Real.rpow_le_rpow h0 (min_le_left _ _) (by norm_num))
      (Real.rpow_le_rpow h0 (min_le_right _ _) (by norm_num)) (Real.rpow_nonneg h0 _)
      (Real.rpow_nonneg hL0 _)
  have h4 : min L S ^ (1 / 4 : ℝ) ≤ L ^ (1 / 8 : ℝ) * S ^ (1 / 8 : ℝ) := by
    refine (Real.rpow_le_rpow (le_min hL0 hS0) hmin (by norm_num)).trans (le_of_eq ?_)
    rw [Real.mul_rpow (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hS0 _), ← Real.rpow_mul hL0,
      ← Real.rpow_mul hS0]
    norm_num
  have hL8 : L ^ (1 / 8 : ℝ) ≤ KL ^ (1 / 8 : ℝ) *
      Real.exp (-(stopRateLong r vlo * n / eps ^ 2)) := by
    refine (Real.rpow_le_rpow hL0 hL (by norm_num)).trans (le_of_eq ?_)
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, exp_rpow_eighth]
    congr 2; ring
  have hS8 : S ^ (1 / 8 : ℝ) ≤ KS ^ (1 / 8 : ℝ) *
      Real.exp (-(stopRateShort D θ κ * eps ^ 2 / n)) := by
    refine (Real.rpow_le_rpow hS0 hS (by norm_num)).trans (le_of_eq ?_)
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, exp_rpow_eighth]
    congr 2; ring
  calc min L S ^ (1 / 4 : ℝ) ≤ L ^ (1 / 8 : ℝ) * S ^ (1 / 8 : ℝ) := h4
    _ ≤ (KL ^ (1 / 8 : ℝ) * Real.exp (-(stopRateLong r vlo * n / eps ^ 2))) *
        (KS ^ (1 / 8 : ℝ) * Real.exp (-(stopRateShort D θ κ * eps ^ 2 / n))) :=
        mul_le_mul hL8 hS8 (Real.rpow_nonneg hS0 _) (by positivity)
    _ = _ := by rw [stopConst, ← hlam, ← hKL, ← hM', ← hKS]; ring

end PGM
