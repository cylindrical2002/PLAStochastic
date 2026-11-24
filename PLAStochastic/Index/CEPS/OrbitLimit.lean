import PLAStochastic.ForMathlib.Analysis.SpecificLimits.ContractionLimit
import PLAStochastic.Index.GEP.Additive.UnconditionalHeight

/-!
# The exact compression limit from any regular reference law

The reference law may be changed without changing `gepC`. This uses the
proved qualitative joint response and orbit closure, without a quantitative rate.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

/-- A regular input and the Exp reference have a common regular orbit class. -/
theorem exists_common_regular_orbits {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ) (hν : RegLaw D θ vlo vhi ν) :
    ∃ Ds θs vlos vhis e0 : ℝ, 0 < Ds ∧ 0 < θs ∧ 0 < vlos ∧ vlos ≤ vhis ∧
      (∀ eps, e0 ≤ eps → ∀ j, RegLaw Ds θs vlos vhis ((lawPhi eps)^[j] ν)) ∧
      (∀ eps, e0 ≤ eps → ∀ j, RegLaw Ds θs vlos vhis ((lawPhi eps)^[j] expPM)) := by
  obtain ⟨D1, θ1, vlo1, vhi1, e1, hD1, hθ1, hvlo1, hv1, hC1⟩ :=
    orbitClosure D θ vlo vhi hD hθ hvlo hv
  obtain ⟨D2, θ2, vlo2, vhi2, e2, -, hθ2, hvlo2, -, hC2⟩ :=
    orbitClosure 1 1 1 1 one_pos one_pos one_pos le_rfl
  obtain ⟨Ds, θs, vlos, vhis, hDs, hθs, hvlos, hvs, inc1, inc2⟩ :=
    exists_regLaw_join hD1 hθ1 hθ2 hvlo1 hvlo2 hv1
  exact ⟨Ds, θs, vlos, vhis, max e1 e2, hDs, hθs, hvlos, hvs,
    fun eps heps j => inc1 _ (hC1 eps ((le_max_left _ _).trans heps) ν hν j),
    fun eps heps j => inc2 _ (hC2 eps ((le_max_right _ _).trans heps) expPM regLaw_expPM j)⟩

/-- Two orbits in one regular class have the same scalar limit. -/
theorem tendsto_log_lawC_of_regular_orbits {D θ vlo vhi η K r eps : ℝ}
    (hvlo : 0 < vlo) (hη : 0 ≤ η) (hηθ : η < θ)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hsmall : (2 * K + 2) * r ≤ 1 / 2)
    (hJ : ∀ ν ρ : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν → RegLaw D θ vlo vhi ρ →
      |(Real.log (lawVar ρ) + Real.log (lawC eps ρ)) -
        (Real.log (lawVar ν) + Real.log (lawC eps ν))| ≤ r * dEta η ν ρ ∧
      |lawVar (lawPhi eps ρ) - lawVar (lawPhi eps ν)| ≤ r * dEta η ν ρ ∧
      dEta η (lawPhi eps ν) (lawPhi eps ρ) ≤ r * dEta η ν ρ + K * |lawVar ρ - lawVar ν|)
    (ν : ProbabilityMeasure ℝ)
    (hν : ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] ν))
    (hexp : ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] expPM)) :
    Tendsto (fun j : ℕ => Real.log (lawC eps ((lawPhi eps)^[j] ν))) atTop (𝓝 (gepLogC eps)) := by
  let lam : ℝ := 2 * K + 1
  have hlam : 0 < lam := by dsimp [lam]; linarith
  let Lc : ℝ := 1 + 1 / (lam * vlo)
  have hLc1 : 1 ≤ Lc := by dsimp [Lc]; linarith [one_div_pos.mpr (mul_pos hlam hvlo)]
  have hLc2 : 1 / (lam * vlo) ≤ Lc := by dsimp [Lc]; linarith
  have hr1 : r ≤ 1 := by nlinarith
  apply contraction_scalar_tendsto_reference (lawPhi eps) (gepDist lam η)
    (fun ρ => Real.log (lawC eps ρ)) (RegLaw D θ vlo vhi) (Lc := Lc)
    (Dst := lam * (vhi - vlo) + D / (θ * (θ - η))) (by linarith)
    (fun x y hx hy => ?_) (fun x y hx hy => ?_) (fun x y hx hy => ?_) expPM ν hexp hν
  · obtain ⟨-, hv, hd⟩ := hJ x y hx hy
    apply gepDist_lawPhi_le hlam.le (by dsimp [lam]; linarith) ?_ hv hd
    convert hsmall using 1
    dsimp [lam]
    ring
  · exact gepDist_le_diam hx hy hlam.le hη hηθ
  · obtain ⟨hc, -, -⟩ := hJ x y hx hy
    exact abs_log_lawC_sub_le hvlo hlam hLc1 hLc2 hx.var_ge hy.var_ge hr1 hc

/-- Every regular input orbit converges to the unchanged Exp reference limit,
uniformly in the choice of input in a fixed regular class. -/
theorem tendsto_log_lawC_orbit {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ e0 : ℝ, ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      Tendsto (fun j : ℕ => Real.log (lawC eps ((lawPhi eps)^[j] ν))) atTop (𝓝 (gepLogC eps)) := by
  obtain ⟨D1, θ1, vlo1, vhi1, e1, hD1, hθ1, hvlo1, hv1, hC1⟩ :=
    orbitClosure D θ vlo vhi hD hθ hvlo hv
  obtain ⟨D2, θ2, vlo2, vhi2, e2, -, hθ2, hvlo2, -, hC2⟩ :=
    orbitClosure 1 1 1 1 one_pos one_pos one_pos le_rfl
  obtain ⟨Ds, θs, vlos, vhis, hDs, hθs, hvlos, hvs, inc1, inc2⟩ :=
    exists_regLaw_join hD1 hθ1 hθ2 hvlo1 hvlo2 hv1
  obtain ⟨η, K, eJ, a, hη, hηθ, hK, ha0, haT, hJs⟩ :=
    jointResponse Ds θs vlos vhis hDs hθs hvlos hvs
  obtain ⟨e3, he3⟩ : ∃ e3 : ℝ, ∀ eps, e3 ≤ eps → (2 * K + 2) * a eps ≤ 1 / 2 := by
    have hp : (0 : ℝ) < 1 / (2 * (2 * K + 2)) := by positivity
    obtain ⟨e3, he3⟩ := eventually_atTop.mp (haT.eventually_le_const hp)
    refine ⟨e3, fun eps heps => ?_⟩
    calc
      (2 * K + 2) * a eps ≤ (2 * K + 2) * (1 / (2 * (2 * K + 2))) :=
        mul_le_mul_of_nonneg_left (he3 eps heps) (by positivity)
      _ = 1 / 2 := by field_simp
  refine ⟨max e1 (max e2 (max eJ e3)), fun eps heps ν hν => ?_⟩
  simp only [max_le_iff] at heps
  obtain ⟨he1, he2, heJ, he3'⟩ := heps
  exact tendsto_log_lawC_of_regular_orbits hvlos hη.le (by linarith) hK (ha0 eps)
    (he3 eps he3') (hJs eps heJ) ν
    (fun j => inc1 _ (hC1 eps he1 ν hν j))
    (fun j => inc2 _ (hC2 eps he2 expPM regLaw_expPM j))

end

end PGM
