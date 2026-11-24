import PLAStochastic.Index.CEPS.Assembly.Output
import PLAStochastic.Index.CEPS.Assembly.FiniteInversion

/-!
# Track F: the analytic interfaces give the one-layer family expansion

`cepsOneLayerFamily_of_interfaces`: the bundle `CepsTransformInterfaces` (T1-mid, T1-low, T3,
T5, JF) implies `CepsOneLayerFamily`, with the output coefficient map
`G g n = angularRealInverse (a_n)`, `a_n = ∑_{k ≤ n} A_{k,n-k}` (`CepsJetData.outDensityCoeff`).

Budgets for a target `(P', m')`: the low-band order `Q = 2P' + 2` and the high-band order
`R = fourierHighOrder δ (m' + 1) Q` of the finite inversion; the input order is `Q` and the input
derivative budget `m` is the maximum of `R + 3` (T2), the T1-mid budget, the T1-low budgets
through `Q`, the T5 budget at `P'`, and the JF budgets of the jet coordinates read through
order `Q`. Along an expanding family, JF and T3 give the low band through every order
`P ≤ Q`, T1-mid and T3 the mid band, T2 the high band, and orbit closure a continuous output
density with a common envelope; the finite inversion then gives the weighted Sobolev
expansion, whose zeroth coefficient is the inverse of `φ_Λ`, i.e. the density of `Λ`.

`gepC_asymptoticExpansion_of_interfaces` is the conditional final theorem.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace CepsJetData

theorem outCoeff_zero (J : CepsJetData) (g : ℕ → ℝ → ℝ) : J.outCoeff g 0 = cepsLambdaChar := by
  funext u
  simp [outCoeff, phiTerm]

theorem outDensityCoeff_zero (J : CepsJetData) (g : ℕ → ℝ → ℝ) :
    J.outDensityCoeff g 0 = cepsLambdaDensity := by
  rw [outDensityCoeff, outCoeff_zero, angularRealInverse_cepsLambdaChar]

end CepsJetData

/-- **Track F.** The analytic interfaces give one layer of the family expansion with the
coefficient map `J.outDensityCoeff`. -/
theorem cepsOneLayerStep_of_interfaces {J : CepsJetData} (hmid : CepsT1Mid)
    (hlow : CepsT1Low J) (hT3 : CepsT3 J) (hT5 : CepsT5 J) (hJF : CepsJF J) :
    CepsOneLayerStep J.outDensityCoeff := by
  classical
  intro P' m'
  obtain ⟨δ, hδ, hδ1, mmid, hmidb⟩ := hmid
  choose mlow hmlow using hlow
  choose m5 hm5 using hT5
  choose mJF hmJF using hJF.expansion
  set Q : ℕ := 2 * P' + 2 with hQdef
  set R : ℕ := fourierHighOrder δ (m' + 1) Q with hRdef
  set Dmax : ℕ := (range (Q + 1)).sup J.dim with hDmax
  set m : ℕ := max (R + 3) (max mmid (max ((range (Q + 1)).sup mlow)
    (max (m5 P') ((range Dmax).sup fun i => mJF i Q)))) with hmdef
  refine ⟨Q, m, fun ν g η hν hη hfam => ?_⟩
  obtain ⟨D, θ, vlo, vhi, hD, hθ, hvlo, hv, hreg⟩ := hν
  -- the budgets
  have hmR : R + 3 ≤ m := le_max_left _ _
  have hmmid : mmid ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hmlowP : ∀ P ≤ Q, mlow P ≤ m := fun P hP =>
    (le_sup (f := mlow) (mem_range.mpr (by omega))).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hm5P : m5 P' ≤ m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hmJFi : ∀ i < Dmax, mJF i Q ≤ m := fun i hi =>
    (le_sup (f := fun i => mJF i Q) (mem_range.mpr hi)).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _))))
  have hdim : ∀ k ≤ Q, J.dim k ≤ Dmax := fun k hk => le_sup (f := J.dim) (mem_range.mpr (by omega))
  have hR2 : 2 ≤ R := by simp only [hRdef, fourierHighOrder]; omega
  -- the jets along the family
  have hjet : ∀ i < Dmax, HasSeriesExpansionAtOrder (fun eps => J.jet (ν eps) i - J.ref i)
      (J.jetSeries i g) Q := fun i hi =>
    CepsJetData.jetSeries_expansion hJF (hmJF i Q ν g η ⟨D, θ, vlo, vhi, hD, hθ, hvlo, hv, hreg⟩
      hη (hfam.mono_order (hmJFi i hi)))
  have hy : ∀ k ≤ Q, ∀ N ≤ Q, ∀ i : Fin (J.dim k),
      HasSeriesExpansionAtOrder (fun eps => J.disp k (J.jet (ν eps)) i) (J.jetSeries i g) N :=
    fun k hk N hN i => (hjet i (lt_of_lt_of_le i.isLt (hdim k hk))).truncate hN
  -- the actual characteristic functions and the coefficients
  set φ : ℝ → ℝ → ℂ := fun eps => cepsOutChar eps (ν eps) with hφdef
  set a : ℕ → ℝ → ℂ := J.outCoeff g with hadef
  -- low band
  have hlowband : ∀ P ≤ Q, ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧ ∃ d : ℕ,
      ∀ᶠ eps in atTop, ∀ u : ℝ, |u| ≤ (A * Real.log eps) ^ 2 →
        ‖φ eps u - ∑ k ∈ range (P + 1), ((eps⁻¹) ^ k : ℝ) • a k u‖ ≤
          K * (eps⁻¹) ^ (P + 1) * (1 + |u|) ^ d := by
    intro P hP A hA
    obtain ⟨r, hr, K, e0, d, hb⟩ := hmlow P D θ vlo vhi η hD hθ hvlo hv hη A hA
    obtain ⟨K', hK', d', hd'⟩ := CepsJetData.outChar_sum_expansion hT3 (ν := ν) (g := g)
      (P := P) fun k _ hkP i => hy k (by omega) (P - k) (by omega) i
    refine ⟨|K| + K', by positivity, max d d', ?_⟩
    filter_upwards [hfam.eventually_inputClass hreg (hmlowP P hP) hr, eventually_ge_atTop e0,
      hd', eventually_gt_atTop (0 : ℝ)] with eps hcl he hbd hpos u hu
    have h1 := hb eps he (ν eps) hcl u hu
    have h2 := hbd u
    have hh : 0 ≤ (eps⁻¹) ^ (P + 1) := by positivity
    have hp1 : (1 + |u|) ^ d ≤ (1 + |u|) ^ max d d' := one_add_abs_pow_le (le_max_left _ _)
    have hp2 : (1 + |u|) ^ d' ≤ (1 + |u|) ^ max d d' := one_add_abs_pow_le (le_max_right _ _)
    have hp0 : 0 ≤ (1 + |u|) ^ d := by positivity
    calc
      _ ≤ ‖φ eps u - ∑ k ∈ range (P + 1), ((eps⁻¹) ^ k : ℝ) • J.phi k u (J.jet (ν eps))‖ +
          ‖∑ k ∈ range (P + 1), ((eps⁻¹) ^ k : ℝ) • J.phi k u (J.jet (ν eps)) -
            ∑ k ∈ range (P + 1), ((eps⁻¹) ^ k : ℝ) • a k u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ K * (eps⁻¹) ^ (P + 1) * (1 + |u|) ^ d + K' * (1 + |u|) ^ d' * (eps⁻¹) ^ (P + 1) :=
        add_le_add h1 h2
      _ ≤ |K| * (eps⁻¹) ^ (P + 1) * (1 + |u|) ^ max d d' +
          K' * (1 + |u|) ^ max d d' * (eps⁻¹) ^ (P + 1) := by
        refine add_le_add ?_ ?_
        · calc
            K * (eps⁻¹) ^ (P + 1) * (1 + |u|) ^ d ≤ |K| * (eps⁻¹) ^ (P + 1) * (1 + |u|) ^ d := by
              gcongr; exact le_abs_self K
            _ ≤ _ := mul_le_mul_of_nonneg_left hp1 (by positivity)
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hK') hh
      _ = (|K| + K') * (eps⁻¹) ^ (P + 1) * (1 + |u|) ^ max d d' := by ring
  -- mid band
  have hmidband : ∃ c U K : ℝ, 0 < c ∧ 0 ≤ U ∧ 0 ≤ K ∧ ∃ d : ℕ,
      (∀ᶠ eps in atTop, ∀ u : ℝ, U ≤ |u| → |u| ≤ eps ^ (1 + δ) →
        ‖φ eps u‖ ≤ K * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|) +
          K * eps ^ d * Real.exp (-c * eps)) ∧
      (∀ k ≤ Q, ∃ B : ℝ, 0 ≤ B ∧ ∃ d : ℕ, ∀ u : ℝ,
        ‖a k u‖ ≤ B * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|)) := by
    obtain ⟨r, hr, c, U, K, e0, hc, d, hb⟩ := hmidb D θ vlo vhi η hD hθ hvlo hv hη
    obtain ⟨c₂, hc₂, hcoef⟩ := StretchedBounded.common_rate (range (Q + 1))
      (fun k _ => CepsJetData.outCoeff_stretched hT3 g k)
    set c' := min c c₂ with hc'
    have hc'c : c' ≤ c := min_le_left _ _
    have hc'2 : c' ≤ c₂ := min_le_right _ _
    refine ⟨c', max U 0, |K|, lt_min hc hc₂, le_max_right _ _, abs_nonneg _, d, ?_, ?_⟩
    · filter_upwards [hfam.eventually_inputClass hreg hmmid hr, eventually_ge_atTop e0,
        eventually_ge_atTop (0 : ℝ)] with eps hcl he he0 u hU hu
      have h := hb eps he (ν eps) hcl u ((le_max_left _ _).trans hU) hu
      have hs : Real.exp (-c * Real.sqrt |u|) ≤ Real.exp (-c' * Real.sqrt |u|) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg |u|])
      have he' : Real.exp (-c * eps) ≤ Real.exp (-c' * eps) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hK := le_abs_self K
      have hp0 : 0 ≤ (1 + |u|) ^ d := by positivity
      have hq0 : 0 ≤ eps ^ d := by positivity
      refine h.trans (add_le_add ?_ ?_)
      · calc
          K * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|) ≤
              |K| * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|) := by gcongr
          _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
      · calc
          K * eps ^ d * Real.exp (-c * eps) ≤ |K| * eps ^ d * Real.exp (-c * eps) := by gcongr
          _ ≤ _ := mul_le_mul_of_nonneg_left he' (by positivity)
    · intro k hk
      obtain ⟨B, hB, d', hb'⟩ := hcoef k (mem_range.mpr (by omega))
      refine ⟨B, hB, d', fun u => (hb' u).trans ?_⟩
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg |u|])) (by positivity)
  -- high band
  have hhighband : ∀ r ≤ R, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ eps in atTop, ∀ u : ℝ,
      |u| ^ r * ‖φ eps u‖ ≤ K * eps ^ (r + 2) :=
    fun r hr => hfam.eventually_high hη hD hθ hvlo hreg (by omega)
  have hband : FourierBandEstimatesUpTo φ a δ Q R :=
    ⟨hδ, hδ1, hmidband, hhighband, hlowband⟩
  -- the output density
  obtain ⟨A, θ', hA, hθ', hout⟩ := ceps_output_density hD hθ hvlo hv hreg (by
    obtain ⟨K, -, hK⟩ := hfam.eventually_high hη hD hθ hvlo hreg (r := 2) (by omega)
    filter_upwards [hK] with eps he
    exact ⟨K * eps ^ (2 + 2), he⟩)
  -- the finite inversion
  obtain ⟨η', hη', hcoef, hFcl, hrem⟩ := cepsFourier_sobolev_expansion_of_density_upTo
    (F := fun eps => cepsOutDensity eps (ν eps)) hband m' P' (le_of_eq hQdef.symm)
    (le_of_eq (by rw [hRdef, hQdef]))
    (hout.mono fun eps he => ⟨he.2.2.1, he.2.1, he.2.2.2.2.2⟩)
    ⟨A, θ', hA, hθ', hout.mono fun eps he => he.2.2.2.1⟩
  have ha0 : angularRealInverse (a 0) = cepsLambdaDensity := J.outDensityCoeff_zero g
  refine ⟨η', hη', ⟨?_, ?_, ?_⟩, ?_⟩
  · -- the reference density
    rw [← ha0]
    exact hcoef 0 (Nat.zero_le _)
  · -- the coefficients
    intro n hn
    exact hcoef n (mem_Icc.mp hn).2
  · -- the density and the remainder
    refine ⟨fun eps => cepsOutDensity eps (ν eps), ?_, ?_⟩
    · filter_upwards [hout, hFcl] with eps he hcl
      exact ⟨he.1, hcl, he.2.2.2.2.1⟩
    · have heq : ∀ eps, cepsInversionRemainder (fun eps => cepsOutDensity eps (ν eps))
          (fun k => angularRealInverse (a k)) P' eps = fun x => cepsOutDensity eps (ν eps) x -
            cepsLambdaDensity x - ∑ n ∈ Icc 1 P', (eps⁻¹) ^ n * J.outDensityCoeff g n x := by
        intro eps
        funext x
        simp only [cepsInversionRemainder]
        rw [sum_range_succ', sum_Icc_one_eq_sum_range, pow_zero, one_mul, ha0]
        simp only [CepsJetData.outDensityCoeff, hadef]
        ring
      simpa only [heq] using hrem
  · -- the scalar expansion
    obtain ⟨r, hr, K, e0, hb⟩ := hm5 P' D θ vlo vhi η hD hθ hvlo hv hη
    have hs := CepsJetData.scal_sum_expansion hT3 (ν := ν) (g := g) (P := P')
      fun k hk i => hy k (by omega) (P' - k) (by omega) i
    refine ⟨J.scalCoeff g, hs.transfer ?_⟩
    obtain ⟨e1, he1⟩ := eventually_atTop.mp (hfam.eventually_inputClass hreg hm5P hr)
    exact ⟨K, max e0 e1, fun eps he =>
      hb eps ((le_max_left _ _).trans he) (ν eps) (he1 eps ((le_max_right _ _).trans he))⟩

/-- **Track F.** The remaining analytic interfaces give the one-layer family interface. -/
theorem cepsOneLayerFamily_of_interfaces (h : CepsTransformInterfaces) : CepsOneLayerFamily := by
  obtain ⟨hmid, J, hlow, hT3, hT5, hJF⟩ := h
  exact ⟨J.outDensityCoeff, cepsTriangular_outDensityCoeff hJF,
    cepsOneLayerStep_of_interfaces hmid hlow hT3 hT5 hJF⟩

/-- **The P-CEPS expansion, conditional on the analytic interfaces.** `gepC ε / ε²` has a unique
all-orders expansion in `ε⁻¹`, with leading coefficient `κ / α`. -/
theorem gepC_asymptoticExpansion_of_interfaces (h : CepsTransformInterfaces) :
    ∃! a : ℕ → ℝ, (∀ M : ℕ, ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps →
      |gepC eps / eps ^ 2 - ∑ j ∈ Finset.range (M + 1), a j * eps ^ (-(j : ℤ))| ≤
        K * eps ^ (-((M : ℤ) + 1))) ∧
      a 0 = BrownianAffine.optimalMeanConstant / BrownianAffine.optimalDispersionConstant :=
  gepC_asymptoticExpansion_coeff_zero_of_oneLayerFamily (cepsOneLayerFamily_of_interfaces h)

end

end PGM
