import PLAStochastic.ForMathlib.Analysis.SpecificLimits.CoupledResidual
import PLAStochastic.Index.CEPS.OrbitLimit

/-!
# A posteriori error of the actual finite-layer compression proxy

This is Proposition 1 of `finite-layer-approximation.md`. It uses the qualitative
joint response on a common class and the unchanged exact compression limit.
Fixed-depth expansions and stabilization will supply the small residuals later.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

/-- The actual variance-corrected compression proxy at a fixed depth. -/
def cepsProxy (eps : ℝ) (ν : ProbabilityMeasure ℝ) (j : ℕ) : ℝ :=
  lawVar ((lawPhi eps)^[j] ν) * lawC eps ((lawPhi eps)^[j] ν) /
    lawVar ((lawPhi eps)^[j + 1] ν)

/-- The logarithm of the variance-corrected proxy, before positivity is used. -/
def cepsProxyLog (eps : ℝ) (ν : ProbabilityMeasure ℝ) (j : ℕ) : ℝ :=
  Real.log (lawVar ((lawPhi eps)^[j] ν)) + Real.log (lawC eps ((lawPhi eps)^[j] ν)) -
    Real.log (lawVar ((lawPhi eps)^[j + 1] ν))

/-- The existing moment-class bracket supplies positivity of the actual mean. -/
theorem RegLaw.lawC_pos {D θ vlo vhi eps : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (heps : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps) : 0 < lawC eps ν := by
  have hM := hν.momClass hθ hvlo
  obtain ⟨-, he1, -, -, -, -, hC, -⟩ := momClass_setup (regV_pos hvlo) heps hM
  have hepos : 0 < eps := by linarith
  have hvpos : 0 < lawVar ν := hvlo.trans_le hν.var_ge
  exact lt_of_lt_of_le (by positivity) hC

theorem exp_cepsProxyLog {eps : ℝ} {ν : ProbabilityMeasure ℝ} {j : ℕ}
    (hv : 0 < lawVar ((lawPhi eps)^[j] ν))
    (hv' : 0 < lawVar ((lawPhi eps)^[j + 1] ν))
    (hC : 0 < lawC eps ((lawPhi eps)^[j] ν)) :
    Real.exp (cepsProxyLog eps ν j) = cepsProxy eps ν j := by
  rw [cepsProxyLog, Real.exp_sub, Real.exp_add, Real.exp_log hv, Real.exp_log hv', Real.exp_log hC]
  rfl

/-- A small logarithmic error gives a scalar error at the same order after scaling. -/
theorem abs_scaled_gepC_sub_cepsProxy_le {eps B E : ℝ} {ν : ProbabilityMeasure ℝ} {j : ℕ}
    (heps : 0 < eps)
    (hv : 0 < lawVar ((lawPhi eps)^[j] ν))
    (hv' : 0 < lawVar ((lawPhi eps)^[j + 1] ν))
    (hC : 0 < lawC eps ((lawPhi eps)^[j] ν))
    (hsmall : |gepLogC eps - cepsProxyLog eps ν j| ≤ 1)
    (herror : |gepLogC eps - cepsProxyLog eps ν j| ≤ E)
    (hB : cepsProxy eps ν j / eps ^ 2 ≤ B) :
    |gepC eps / eps ^ 2 - cepsProxy eps ν j / eps ^ 2| ≤ 2 * B * E := by
  have hproxy := exp_cepsProxyLog hv hv' hC
  have hproxy0 : 0 < cepsProxy eps ν j := by rw [← hproxy]; positivity
  have hE : 0 ≤ E := (abs_nonneg _).trans herror
  have hexp := Real.abs_exp_sub_one_le hsmall
  have heq : gepC eps / eps ^ 2 - cepsProxy eps ν j / eps ^ 2 =
      (cepsProxy eps ν j / eps ^ 2) * (Real.exp (gepLogC eps - cepsProxyLog eps ν j) - 1) := by
    rw [Real.exp_sub, hproxy, gepC]
    field_simp
  rw [heq, abs_mul, abs_of_pos (div_pos hproxy0 (sq_pos_of_pos heps))]
  calc
    (cepsProxy eps ν j / eps ^ 2) * |Real.exp (gepLogC eps - cepsProxyLog eps ν j) - 1| ≤
        (cepsProxy eps ν j / eps ^ 2) * (2 * E) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hexp.trans (mul_le_mul_of_nonneg_left herror (by norm_num))
    _ ≤ B * (2 * E) := mul_le_mul_of_nonneg_right hB (by positivity)
    _ = 2 * B * E := by ring

/-- The distance and variance residuals pay for the entire infinite tail. -/
theorem abs_gepLogC_sub_cepsProxyLog_le {D θ vlo vhi η K r eps : ℝ}
    (hvlo : 0 < vlo) (hη : 0 ≤ η) (hηθ : η < θ)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hsmall : (2 * K + 2) * r ≤ 1 / 2)
    (hJ : ∀ μ ρ : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi μ → RegLaw D θ vlo vhi ρ →
      |(Real.log (lawVar ρ) + Real.log (lawC eps ρ)) -
        (Real.log (lawVar μ) + Real.log (lawC eps μ))| ≤ r * dEta η μ ρ ∧
      |lawVar (lawPhi eps ρ) - lawVar (lawPhi eps μ)| ≤ r * dEta η μ ρ ∧
      dEta η (lawPhi eps μ) (lawPhi eps ρ) ≤ r * dEta η μ ρ + K * |lawVar ρ - lawVar μ|)
    (ν : ProbabilityMeasure ℝ)
    (hν : ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] ν))
    (hexp : ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] expPM)) (j : ℕ) :
    |gepLogC eps - cepsProxyLog eps ν j| ≤
      ((1 + vlo⁻¹) * r / (1 - (K + 1) * r)) *
        (dEta η ((lawPhi eps)^[j] ν) ((lawPhi eps)^[j + 1] ν) +
          K * |lawVar ((lawPhi eps)^[j + 1] ν) - lawVar ((lawPhi eps)^[j] ν)|) := by
  let ρ : ℕ → ProbabilityMeasure ℝ := fun n => (lawPhi eps)^[n] ν
  have hstep (n : ℕ) : ρ (n + 1) = lawPhi eps (ρ n) := Function.iterate_succ_apply' _ _ _
  let dist : ℕ → ℝ := fun n => dEta η (ρ n) (ρ (n + 1))
  let varDiff : ℕ → ℝ := fun n => |lawVar (ρ (n + 1)) - lawVar (ρ n)|
  have hrec (n : ℕ) := hJ (ρ n) (ρ (n + 1)) (hν n) (hν (n + 1))
  have hDr (n : ℕ) : dist (n + 1) ≤ r * dist n + K * varDiff n := by
    simpa only [dist, varDiff, hstep] using (hrec n).2.2
  have hVr (n : ℕ) : varDiff (n + 1) ≤ r * dist n := by
    simpa only [varDiff, dist, hstep] using (hrec n).2.1
  have hu (n : ℕ) : |Real.log (lawVar (ρ (n + 2))) - Real.log (lawVar (ρ (n + 1)))| ≤
      (r / vlo) * dist n := by
    have hlog := abs_log_sub_log_le hvlo (hν (n + 2)).var_ge (hν (n + 1)).var_ge
    have hv := hVr n
    change |lawVar (ρ (n + 1 + 1)) - lawVar (ρ (n + 1))| ≤ r * dist n at hv
    calc
      |Real.log (lawVar (ρ (n + 2))) - Real.log (lawVar (ρ (n + 1)))| ≤
          |lawVar (ρ (n + 2)) - lawVar (ρ (n + 1))| / vlo := hlog
      _ ≤ (r * dist n) / vlo := by gcongr
      _ = (r / vlo) * dist n := by ring
  have hlimit := tendsto_log_lawC_of_regular_orbits hvlo hη hηθ hK hr hsmall hJ ν hν hexp
  have hq : (K + 1) * r < 1 := by nlinarith
  have h := coupled_residual_limit_error (D := dist) (V := varDiff)
    (c := fun n => Real.log (lawC eps (ρ n))) (u := fun n => Real.log (lawVar (ρ n)))
    (fun n => dEta_nonneg _ _ _) (fun n => abs_nonneg _) hK hr (div_nonneg hr hvlo.le) hq
    hDr hVr (fun n => (hrec n).1) hu hlimit j
  change |gepLogC eps - cepsProxyLog eps ν j| ≤ _ at h
  convert h using 1
  dsimp [dist, varDiff, ρ]
  ring

/-- Qualitative response gives a uniform posterior constant, at an arbitrarily
small fixed positive weight. The class and constants may depend on that weight. -/
theorem ceps_log_error_on_regular_class {D θ vlo vhi eOrbit : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ)
    (hν : ∀ eps, eOrbit ≤ eps → ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] ν))
    (hexp : ∀ eps, eOrbit ≤ eps → ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] expPM))
    {ηMax : ℝ} (hηMax : 0 < ηMax) :
    ∃ η H e0 : ℝ, 0 < η ∧ η < ηMax ∧ 0 ≤ H ∧ 1 ≤ e0 ∧
      (∀ eps, e0 ≤ eps → ∀ j, 0 < lawC eps ((lawPhi eps)^[j] ν)) ∧
      ∀ eps, e0 ≤ eps → ∀ j,
        |gepLogC eps - cepsProxyLog eps ν j| ≤ H *
          (dEta η ((lawPhi eps)^[j] ν) ((lawPhi eps)^[j + 1] ν) +
            |lawVar ((lawPhi eps)^[j + 1] ν) - lawVar ((lawPhi eps)^[j] ν)|) := by
  let θs : ℝ := min θ ηMax
  have hθs : 0 < θs := lt_min hθ hηMax
  have inc {ρ : ProbabilityMeasure ℝ} (hρ : RegLaw D θ vlo vhi ρ) : RegLaw D θs vlo vhi ρ :=
    hρ.mono le_rfl (min_le_left _ _) hθs.le le_rfl le_rfl
  obtain ⟨η, K, eJ, a, hη, hηθs, hK, ha0, haT, hJs⟩ :=
    jointResponse D θs vlo vhi hD hθs hvlo hv
  obtain ⟨eSmall, heSmall⟩ : ∃ eSmall : ℝ, ∀ eps, eSmall ≤ eps → (2 * K + 2) * a eps ≤ 1 / 2 := by
    have hp : (0 : ℝ) < 1 / (2 * (2 * K + 2)) := by positivity
    obtain ⟨eSmall, he⟩ := eventually_atTop.mp (haT.eventually_le_const hp)
    refine ⟨eSmall, fun eps heps => ?_⟩
    calc
      (2 * K + 2) * a eps ≤ (2 * K + 2) * (1 / (2 * (2 * K + 2))) :=
        mul_le_mul_of_nonneg_left (he eps heps) (by positivity)
      _ = 1 / 2 := by field_simp
  let H : ℝ := 2 * (1 + vlo⁻¹) * (1 + K)
  let e0 : ℝ := max 1 (max eOrbit (max eJ (max eSmall (epsZero (regB vhi) (regBeta D θ vlo)))))
  have he0 : 1 ≤ e0 := le_max_left _ _
  have hηMax' : η < ηMax := by
    have ht : θs ≤ ηMax := min_le_right _ _
    linarith
  refine ⟨η, H, e0, hη, hηMax', by dsimp [H]; positivity, he0, ?_, ?_⟩
  · intro eps heps j
    have he := heps
    simp only [e0, max_le_iff] at he
    exact (hν eps he.2.1 j).lawC_pos hθ hvlo he.2.2.2.2
  · intro eps heps j
    have he := heps
    simp only [e0, max_le_iff] at he
    obtain ⟨-, heOrbit, heJ, heS, -⟩ := he
    have hsmall := heSmall eps heS
    have hr := ha0 eps
    have hr1 : a eps ≤ 1 := by nlinarith
    have hden : 1 / 2 ≤ 1 - (K + 1) * a eps := by nlinarith
    have hcoef : (1 + vlo⁻¹) * a eps / (1 - (K + 1) * a eps) ≤ 2 * (1 + vlo⁻¹) := by
      calc
        (1 + vlo⁻¹) * a eps / (1 - (K + 1) * a eps) ≤ ((1 + vlo⁻¹) * a eps) / (1 / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
        _ = 2 * (1 + vlo⁻¹) * a eps := by ring
        _ ≤ 2 * (1 + vlo⁻¹) := mul_le_of_le_one_right (by positivity) hr1
    have hpost := abs_gepLogC_sub_cepsProxyLog_le hvlo hη.le (by linarith) hK hr hsmall (hJs eps heJ) ν
      (fun n => inc (hν eps heOrbit n)) (fun n => inc (hexp eps heOrbit n)) j
    have hd : 0 ≤ dEta η ((lawPhi eps)^[j] ν) ((lawPhi eps)^[j + 1] ν) := dEta_nonneg _ _ _
    have hvd : 0 ≤ |lawVar ((lawPhi eps)^[j + 1] ν) - lawVar ((lawPhi eps)^[j] ν)| := abs_nonneg _
    calc
      |gepLogC eps - cepsProxyLog eps ν j| ≤ _ := hpost
      _ ≤ 2 * (1 + vlo⁻¹) *
          (dEta η ((lawPhi eps)^[j] ν) ((lawPhi eps)^[j + 1] ν) +
            K * |lawVar ((lawPhi eps)^[j + 1] ν) - lawVar ((lawPhi eps)^[j] ν)|) := by
        apply mul_le_mul_of_nonneg_right hcoef
        positivity
      _ ≤ H * (dEta η ((lawPhi eps)^[j] ν) ((lawPhi eps)^[j + 1] ν) +
            |lawVar ((lawPhi eps)^[j + 1] ν) - lawVar ((lawPhi eps)^[j] ν)|) := by
        have hpair : dEta η ((lawPhi eps)^[j] ν) ((lawPhi eps)^[j + 1] ν) +
            K * |lawVar ((lawPhi eps)^[j + 1] ν) - lawVar ((lawPhi eps)^[j] ν)| ≤
            (1 + K) * (dEta η ((lawPhi eps)^[j] ν) ((lawPhi eps)^[j + 1] ν) +
              |lawVar ((lawPhi eps)^[j + 1] ν) - lawVar ((lawPhi eps)^[j] ν)|) := by nlinarith
        have ht := mul_le_mul_of_nonneg_left hpair (by positivity : 0 ≤ 2 * (1 + vlo⁻¹))
        simpa only [H, mul_assoc] using ht

end

end PGM
