import PLAStochastic.Index.CEPS.Family.Projection
import PLAStochastic.Index.CEPS.AssemblyOfInputs

/-!
# The one-layer family interface supplies the fixed-depth inputs

The constant family `Λ` expands in every budget with zero coefficients. For a fixed
depth the budgets are assigned backwards and the interface is iterated forwards along
the actual orbit, whose regularity comes from the proved orbit closure. The layer
coefficients are `G^[k] 0`; triangularity makes consecutive layers share their
polynomial through the depth, which pays the coupled residual. Finite arithmetic
turns the scalar expansions into the proxy expansion.

This is a conditional assembly: `CepsOneLayerFamily` is still an open interface.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- The actual orbit of the Brownian reference law at a fixed depth. -/
def cepsOrbit (k : ℕ) (eps : ℝ) : ProbabilityMeasure ℝ := (lawPhi eps)^[k] cepsLambda

/-- The density coefficients at depth `k`, starting from the zero coefficients of `Λ`. -/
def cepsLayerCoeff (G : (ℕ → ℝ → ℝ) → ℕ → ℝ → ℝ) (k : ℕ) : ℕ → ℝ → ℝ :=
  G^[k] (fun _ _ => 0)

theorem cepsOrbit_succ (k : ℕ) (eps : ℝ) :
    cepsOrbit (k + 1) eps = lawPhi eps (cepsOrbit k eps) :=
  Function.iterate_succ_apply' _ _ _

theorem cepsLayerCoeff_succ (G : (ℕ → ℝ → ℝ) → ℕ → ℝ → ℝ) (k : ℕ) :
    cepsLayerCoeff G (k + 1) = G (cepsLayerCoeff G k) :=
  Function.iterate_succ_apply' _ _ _

/-- Triangularity: the coefficients through order `j` are stable from depth `j` on. -/
theorem cepsLayerCoeff_stable {G : (ℕ → ℝ → ℝ) → ℕ → ℝ → ℝ} (hG : CepsTriangular G) :
    ∀ j n : ℕ, 1 ≤ n → n ≤ j → cepsLayerCoeff G (j + 1) n = cepsLayerCoeff G j n := by
  intro j
  induction j with
  | zero => intro n h1 h2; omega
  | succ j ih =>
    intro n h1 h2
    rw [cepsLayerCoeff_succ G (j + 1)]
    conv_rhs => rw [cepsLayerCoeff_succ G j]
    exact hG _ _ n fun i hi1 hi2 => ih i hi1 (by omega)

/-- Every layer of the actual orbit lies in one regular class for large `ε`. -/
theorem exists_regLaw_cepsOrbit : ∃ D θ vlo vhi e0 : ℝ, 0 < D ∧ 0 < θ ∧ 0 < vlo ∧
    vlo ≤ vhi ∧ ∀ eps, e0 ≤ eps → ∀ k, RegLaw D θ vlo vhi (cepsOrbit k eps) := by
  obtain ⟨D, θ, hD, hθ, hν⟩ := exists_regLaw_cepsLambda
  obtain ⟨Ds, θs, vlos, vhis, e0, hDs, hθs, hvlos, hvs, hνs, -⟩ :=
    exists_common_regular_orbits hD hθ BrownianAffine.optimalDispersionConstant_pos le_rfl
      cepsLambda hν
  exact ⟨Ds, θs, vlos, vhis, e0, hDs, hθs, hvlos, hvs, hνs⟩

theorem cepsOrbit_eventuallyRegular (k : ℕ) : CepsEventuallyRegular (cepsOrbit k) := by
  obtain ⟨D, θ, vlo, vhi, e0, hD, hθ, hvlo, hv, h⟩ := exists_regLaw_cepsOrbit
  exact ⟨D, θ, vlo, vhi, hD, hθ, hvlo, hv, eventually_atTop.mpr ⟨e0, fun eps he => h eps he k⟩⟩

theorem cepsOrbit_mean (k : ℕ) : ∀ᶠ eps in atTop, lawMean (cepsOrbit k eps) = 1 := by
  obtain ⟨D, θ, vlo, vhi, e0, -, -, -, -, h⟩ := exists_regLaw_cepsOrbit
  exact eventually_atTop.mpr ⟨e0, fun eps he => (h eps he k).mean⟩

/-- The constant reference family expands in every budget inside the envelope of `Λ`. -/
theorem cepsFamilyExpansion_cepsLambda {m : ℕ} {η : ℝ}
    (hΛ : CepsSobolevClass m η cepsLambdaDensity) (P : ℕ) :
    CepsFamilyExpansion (fun _ => cepsLambda) m η P (fun _ _ => 0) where
  reference := hΛ
  coeff _ _ := cepsSobolevClass_zero m η
  density := ⟨fun _ => cepsLambdaDensity,
    Eventually.of_forall fun _ => ⟨cepsLambdaDensity_nonneg, hΛ, cepsLambda_eq_withDensity⟩,
    0, 0, fun eps _ => by simp [cepsSobolev]⟩

/-- Iterating the interface along the actual orbit, with budgets assigned backwards. -/
theorem cepsOrbit_familyExpansion {G : (ℕ → ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hstep : CepsOneLayerStep G) (k : ℕ) :
    ∀ P m : ℕ, ∃ η : ℝ, 0 < η ∧
      CepsFamilyExpansion (cepsOrbit k) m η P (cepsLayerCoeff G k) := by
  induction k with
  | zero =>
    intro P m
    obtain ⟨η, hη, hΛ⟩ := exists_cepsSobolevClass_cepsLambdaDensity m
    exact ⟨η, hη, cepsFamilyExpansion_cepsLambda hΛ P⟩
  | succ k ih =>
    intro P' m'
    obtain ⟨P, m, hPm⟩ := hstep P' m'
    obtain ⟨η, hη, hk⟩ := ih P m
    obtain ⟨η', hη', hout, -⟩ :=
      hPm (cepsOrbit k) (cepsLayerCoeff G k) η (cepsOrbit_eventuallyRegular k) hη hk
    refine ⟨η', hη', ?_⟩
    have he : cepsOrbit (k + 1) = fun eps => lawPhi eps (cepsOrbit k eps) :=
      funext fun eps => cepsOrbit_succ k eps
    rw [he, cepsLayerCoeff_succ]
    exact hout

theorem cepsOrbit_lawC_hasInverseExpansion {G : (ℕ → ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hstep : CepsOneLayerStep G) (k : ℕ) :
    ∃ b : ℕ → ℝ, HasInverseExpansion (fun eps => lawC eps (cepsOrbit k eps) / eps ^ 2) b := by
  obtain ⟨b, hb, -⟩ := existsUnique_inverseExpansion_of_finite_orders
    (f := fun eps => lawC eps (cepsOrbit k eps) / eps ^ 2) fun M => by
      obtain ⟨P, m, hPm⟩ := hstep M 0
      obtain ⟨η, hη, hk⟩ := cepsOrbit_familyExpansion hstep k P m
      obtain ⟨-, -, -, c, hc⟩ :=
        hPm (cepsOrbit k) (cepsLayerCoeff G k) η (cepsOrbit_eventuallyRegular k) hη hk
      exact ⟨c, hc⟩
  exact ⟨b, hb⟩

theorem cepsOrbit_lawVar_hasInverseExpansion {G : (ℕ → ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hstep : CepsOneLayerStep G) (k : ℕ) :
    ∃ a : ℕ → ℝ, HasInverseExpansion (fun eps => lawVar (cepsOrbit k eps)) a ∧
      a 0 = lawVar cepsLambda := by
  obtain ⟨a, ha, -⟩ := existsUnique_inverseExpansion_of_finite_orders
    (f := fun eps => lawVar (cepsOrbit k eps)) fun M => by
      obtain ⟨η, hη, hk⟩ := cepsOrbit_familyExpansion hstep k M 0
      exact ⟨_, hk.lawVar_hasInverseExpansionAtOrder hη (cepsOrbit_mean k)⟩
  refine ⟨a, ha, ?_⟩
  obtain ⟨η, hη, hk⟩ := cepsOrbit_familyExpansion hstep k 0 0
  have h0 := hk.lawVar_hasInverseExpansionAtOrder hη (cepsOrbit_mean k)
  rw [inverseExpansion_coeff_eq_of_orders (ha 0) h0 le_rfl le_rfl, cepsVarianceCoeff_zero]

theorem cepsOrbit_residual {G : (ℕ → ℝ → ℝ) → ℕ → ℝ → ℝ} (hG : CepsTriangular G)
    (hstep : CepsOneLayerStep G) (j : ℕ) :
    ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 < η → η < ηMax →
      IsInverseOrder (fun eps =>
        dEta η ((lawPhi eps)^[j] cepsLambda) ((lawPhi eps)^[j + 1] cepsLambda) +
          |lawVar ((lawPhi eps)^[j + 1] cepsLambda) - lawVar ((lawPhi eps)^[j] cepsLambda)|)
        (j + 1) := by
  obtain ⟨ηa, hηa, ha⟩ := cepsOrbit_familyExpansion hstep j j 0
  obtain ⟨ηb, hηb, hb⟩ := cepsOrbit_familyExpansion hstep (j + 1) j 0
  refine ⟨min ηa ηb, lt_min hηa hηb, fun η hη hηm => ?_⟩
  exact ceps_residual_inverseOrder_of_familyExpansion ha hb
    (fun n hn => cepsLayerCoeff_stable hG j n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2)
    (cepsOrbit_mean j) (cepsOrbit_mean (j + 1)) hη
    (lt_of_lt_of_le hηm (min_le_left _ _)) (lt_of_lt_of_le hηm (min_le_right _ _))

/-- **Reduction (track R).** The one-layer family interface gives the fixed-depth inputs
of the Brownian reference orbit. -/
theorem cepsFixedDepthInputs_of_oneLayerFamily (h : CepsOneLayerFamily) :
    CepsFixedDepthInputs cepsLambda := by
  obtain ⟨G, hG, hstep⟩ := h
  refine ⟨fun j => ?_, cepsOrbit_residual hG hstep⟩
  obtain ⟨a, ha, -⟩ := cepsOrbit_lawVar_hasInverseExpansion hstep j
  obtain ⟨b, hb⟩ := cepsOrbit_lawC_hasInverseExpansion hstep j
  obtain ⟨c, hc, hc0⟩ := cepsOrbit_lawVar_hasInverseExpansion hstep (j + 1)
  obtain ⟨d, hd, -⟩ := cepsProxy_hasInverseExpansion_of_components cepsLambda j ha hb hc
    (by rw [hc0]; exact lawVar_cepsLambda_pos.ne')
  exact ⟨d, hd⟩

/-- The target expansion of P-CEPS, conditional on the one-layer family interface. -/
theorem gepC_asymptoticExpansion_of_oneLayerFamily (h : CepsOneLayerFamily) :
    ∃! a : ℕ → ℝ, ∀ M : ℕ, ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps →
      |gepC eps / eps ^ 2 - ∑ j ∈ Finset.range (M + 1), a j * eps ^ (-(j : ℤ))| ≤
        K * eps ^ (-((M : ℤ) + 1)) :=
  gepC_asymptoticExpansion_of_cepsLambda_fixed_depth (cepsFixedDepthInputs_of_oneLayerFamily h)

/-- The conditional expansion together with its unconditional leading value `κ / α`. -/
theorem gepC_asymptoticExpansion_coeff_zero_of_oneLayerFamily (h : CepsOneLayerFamily) :
    ∃! a : ℕ → ℝ, (∀ M : ℕ, ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps →
      |gepC eps / eps ^ 2 - ∑ j ∈ Finset.range (M + 1), a j * eps ^ (-(j : ℤ))| ≤
        K * eps ^ (-((M : ℤ) + 1))) ∧
      a 0 = BrownianAffine.optimalMeanConstant / BrownianAffine.optimalDispersionConstant := by
  obtain ⟨a, ha, huniq⟩ := gepC_asymptoticExpansion_of_oneLayerFamily h
  exact ⟨a, ⟨ha, gepC_coeff_zero ((hasInverseExpansion_iff_zpow _ a).mpr ha)⟩,
    fun b hb => huniq b hb.1⟩

end

end PGM
