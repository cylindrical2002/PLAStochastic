import PLAStochastic.Index.GEP.Response.Score.Continuity

/-!
# WP4 leaf 4A-S: the score calculus along mixture paths (`ScoreCalculus`)

`scoreCalculus : ScoreCalculus` (`PLAStochastic/Index/GEP/Response/Defs.lean`), with the output weight
`η₀ = θK / 8` (an absolute constant: `θK` is the exponential weight of the output law in
`lawPhi_expMom`) and a threshold depending on the class.  Sources: `joint-response.md` §5,
`influence-lipschitz.md` §8 (mix), `positive-direction-response.md` §8.1, §8.3.

The three rows:
* **φ** (`outFn`): continuity from `continuousOn_outFn_mix`, derivative
  `∫ J_φ d(ν₁ - ν₀)` from `hasDerivAt_outFn_mix`;
* **V** (`lawV`): on the class `v(Φ_ε ν) = F_{φ_V}(ν) + 1` with `φ_V(y) = y² - 2y`
  (`lawVar_lawPhi_eq`), and `lawJV = outJ psiVar`, so it is row φ for `psiVar`
  (`outTest_psiVar`);
* **A** (`lawA = log v + log C`): `v(ν_s) = (1 - s) v₀ + s v₁` (`lawVar_mixPM`) and
  `hasDerivAt_lawC_mix`, with `∫ (x - 1)² dν_j = v_j`.

The uniform inputs along the whole path come from `regLaw_facts` and `RegLaw.mix`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

variable {D θ vlo vhi : ℝ}

/-! ## The variance along the path -/

theorem RegLaw.integrable_sq_sub_one {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) : Integrable (fun x : ℝ => (x - 1) ^ 2) (ν : Measure ℝ) := by
  have hi := (h.tail_mean hθ).1
  have hs := (h.tail_sq hθ).1
  have e : (fun x : ℝ => (x - 1) ^ 2) = fun x => x ^ 2 - 2 * x + 1 := by ext x; ring
  rw [e]
  exact (hs.sub (hi.const_mul 2)).add (integrable_const _)

theorem RegLaw.lawVar_eq {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) :
    lawVar ν = ∫ x, (x - 1) ^ 2 ∂(ν : Measure ℝ) := by
  rw [lawVar, h.mean]

/-- `v(ν_s) = (1 - s) v₀ + s v₁` (both means are one). -/
theorem lawVar_mixPM {ν₀ ν₁ : ProbabilityMeasure ℝ} (h₀ : RegLaw D θ vlo vhi ν₀)
    (h₁ : RegLaw D θ vlo vhi ν₁) (hθ : 0 < θ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    lawVar (mixPM ν₀ ν₁ s) = (1 - s) * lawVar ν₀ + s * lawVar ν₁ := by
  have h1s : 0 ≤ 1 - s := by linarith [hs.2]
  rw [(h₀.mix h₁ hθ s).lawVar_eq, h₀.lawVar_eq, h₁.lawVar_eq, coe_mixPM, mixParam_of_mem hs,
    integral_add_measure ((h₀.integrable_sq_sub_one hθ).smul_measure ENNReal.ofReal_ne_top)
      ((h₁.integrable_sq_sub_one hθ).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal h1s,
    ENNReal.toReal_ofReal hs.1, smul_eq_mul, smul_eq_mul]

/-! ## The variance test -/

theorem testFn_psiVar {y : ℝ} (hy : 0 < y) : testFn psiVar y = y ^ 2 - 2 * y := by
  have hint1 : IntegrableOn (fun t : ℝ => 2 * t) (Ioo 0 y) :=
    (continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun _ : ℝ => (2 : ℝ)) (Ioo 0 y) :=
    continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have e1 := testFn_two_mul hy
  have e2 := testFn_one hy
  rw [testFn] at e1 e2 ⊢
  simp only [psiVar]
  rw [integral_sub hint1 hint2, e1, setIntegral_const, Real.volume_real_Ioo_of_le hy.le,
    smul_eq_mul]
  ring

theorem outTest_psiVar {η : ℝ} (hη : 0 < η) : OutTest η (2 / η + 2) psiVar := by
  refine ⟨by unfold psiVar; fun_prop, fun x hx => ?_⟩
  have h1 := le_exp_div (t := x) hη
  have h2 : 1 ≤ Real.exp (η * x) := Real.one_le_exp (by positivity)
  rw [psiVar, abs_le]
  have e : (2 / η + 2) * Real.exp (η * x) = 2 / η * Real.exp (η * x) + 2 * Real.exp (η * x) := by
    ring
  have h3 : 0 ≤ 2 / η * Real.exp (η * x) := by positivity
  constructor
  · rw [e]; linarith
  · have : x * η ≤ Real.exp (η * x) := by rw [le_div_iff₀ hη] at h1; linarith
    have hx2 : 2 * x ≤ 2 / η * Real.exp (η * x) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hη]; linarith
    nlinarith

/-- **Row V is row φ for the variance test**: `v(Φ_ε ν) = ∫ φ_V dΦ_ε ν + 1`. -/
theorem lawVar_lawPhi_eq {b β vmin eps : ℝ} {ν : ProbabilityMeasure ℝ}
    (hm : MomClass b β vmin (lawPhi eps ν)) :
    lawVar (lawPhi eps ν) = outFn eps ν psiVar + 1 := by
  set ρ := lawPhi eps ν with hρ
  have h2 : MemLp id 2 (ρ : Measure ℝ) := hm.memLp3.mono_exponent (by norm_num)
  have h1 : MemLp id 1 (ρ : Measure ℝ) := hm.memLp3.mono_exponent (by norm_num)
  have hsq : Integrable (fun x : ℝ => x ^ 2) (ρ : Measure ℝ) := h2.integrable_sq
  have hid : Integrable (fun x : ℝ => x) (ρ : Measure ℝ) := memLp_one_iff_integrable.1 h1
  have hpos : ∀ᵐ y ∂(ρ : Measure ℝ), 0 < y := by
    filter_upwards [compl_mem_ae_iff.2 hm.pos] with y hy
    simpa using hy
  have hout : outFn eps ν psiVar = ∫ y, (y ^ 2 - 2 * y) ∂(ρ : Measure ℝ) := by
    rw [outFn]
    exact integral_congr_ae (by filter_upwards [hpos] with y hy using testFn_psiVar hy)
  rw [hout, lawVar, hm.mean]
  have e : (fun x : ℝ => (x - 1) ^ 2) = fun x => (x ^ 2 - 2 * x) + 1 := by ext x; ring
  rw [e, integral_add (f := fun x : ℝ => x ^ 2 - 2 * x) (g := fun _ => (1 : ℝ))
    (hsq.sub (hid.const_mul 2)) (integrable_const _), integral_const,
    probReal_univ, smul_eq_mul, mul_one]

/-! ## The score calculus -/

/-- **Leaf 4A-S.** -/
theorem scoreCalculus : ScoreCalculus := by
  intro D θ vlo vhi hD hθ hvlo hv
  obtain ⟨e0, -, hF⟩ := regLaw_facts hD hθ hvlo hv
  set b := regB vhi with hbdef
  set β := regBeta D θ vlo with hβdef
  have hb0 : 0 < b := (regV_pos hvlo).trans_le (regV_le_regB hv)
  set η₀ : ℝ := θK / 8 with hη₀def
  have hη₀ : 0 < η₀ := by have := θK_pos; positivity
  refine ⟨η₀, max (max e0 (epsZero b β)) (512 * b * η₀ / θ + 1), hη₀,
    fun eps heps ν₀ ν₁ h₀ h₁ => ?_⟩
  have heps0 : e0 ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have hepsZ : epsZero b β ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have heps2 : 512 * b * η₀ / θ + 1 ≤ eps := le_trans (le_max_right _ _) heps
  have heps1 : 1 ≤ eps := by
    have : 0 ≤ 512 * b * η₀ / θ := by positivity
    linarith
  have hmix : ∀ s, RegLaw D θ vlo vhi (mixPM ν₀ ν₁ s) := fun s => h₀.mix h₁ hθ s
  have hfacts := fun s => hF eps heps0 _ (hmix s)
  -- the densities of the endpoints
  obtain ⟨f₀, hf₀m, hf₀0, -, -, hν₀⟩ := h₀.density
  obtain ⟨f₁, hf₁m, hf₁0, -, -, hν₁⟩ := h₁.density
  have hS : MixSetup ν₀ ν₁ f₀ f₁ := ⟨hf₀0, hf₁0, hf₀m, hf₁m, hν₀, hν₁⟩
  -- the stopping moment
  set a := tailA vlo eps with ha
  set lam := tailRate * regV vlo / eps ^ 2 with hlam
  have hlam0 : 0 < lam := by have := tailRate_pos; have := regV_pos hvlo; positivity
  have ha_eq : a = Real.exp (-lam) := by rw [ha, tailA, hlam, neg_div]
  set κ := lam / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  have hκa : Real.exp κ * a < 1 := by
    rw [ha_eq, ← Real.exp_add, Real.exp_lt_one_iff]; linarith
  have ha0 : 0 ≤ a := (tailA_pos vlo eps).le
  have ha1 : a < 1 := tailA_lt_one hvlo (by linarith)
  have hK : (0 : ℝ) ≤ 72 / 71 := by norm_num
  have hfin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s)), gapSegLen eps g ≠ ⊤ :=
    fun s _ => (hfacts s).1
  have htail : ∀ s ∈ Icc (0 : ℝ) 1, ∀ m : ℕ, iidLaw (mixPM ν₀ ν₁ s)
      {g | (m : ℕ∞) < gapSegLen eps g} ≤ ENNReal.ofReal (72 / 71 * a ^ m) :=
    fun s _ => (hfacts s).2.2.1
  have hexp : ∀ s, Integrable (fun g => Real.exp (κ * (gapSegLen eps g).toNat))
      (iidLaw (mixPM ν₀ ν₁ s)) := fun s =>
    (integrable_exp_gapSegLen (hfacts s).1 hK ha0 (hfacts s).2.2.1 hκ0.le hκa).1
  set clo := eps ^ 2 / (128 * b) with hclo
  have hclo0 : 0 < clo := by positivity
  have hCpos : ∀ s, 0 < lawC eps (mixPM ν₀ ν₁ s) := fun s =>
    hclo0.trans_le (hfacts s).2.1
  -- row C
  have hCder : ∀ s₀ ∈ Ioo (0 : ℝ) 1,
      Integrable (lawJC eps (mixPM ν₀ ν₁ s₀)) (ν₀ : Measure ℝ) ∧
        Integrable (lawJC eps (mixPM ν₀ ν₁ s₀)) (ν₁ : Measure ℝ) ∧
        HasDerivAt (fun s => lawC eps (mixPM ν₀ ν₁ s))
          (∫ x, lawJC eps (mixPM ν₀ ν₁ s₀) x ∂(ν₁ : Measure ℝ) -
            ∫ x, lawJC eps (mixPM ν₀ ν₁ s₀) x ∂(ν₀ : Measure ℝ)) s₀ := fun s₀ hs₀ => by
    obtain ⟨h1, h2, h3, -⟩ := hasDerivAt_lawC_mix hS hs₀ hfin hκ0 (hexp s₀)
    exact ⟨h1, h2, h3⟩
  have hCcont : ContinuousOn (fun s => lawC eps (mixPM ν₀ ν₁ s)) (Icc 0 1) :=
    continuousOn_lawC_mix hS hK ha0 ha1 hfin htail
  -- the reference law has the exponential moment needed for continuity
  have hρexp : Integrable (fun x => Real.exp (2 * η₀ / clo * x))
      (mixPM ν₀ ν₁ (1 / 2) : Measure ℝ) := by
    have hE := (hmix (1 / 2)).expMom hθ
    have hle : 2 * η₀ / clo ≤ θ / 2 := by
      have heps_sq : 512 * b * η₀ / θ ≤ eps ^ 2 := by nlinarith
      rw [hclo, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      rw [div_le_iff₀ hθ] at heps_sq
      nlinarith
    exact (hE.mono (hmix (1 / 2)).measure_Iic_zero (by positivity) hle le_rfl).integrable
  -- row φ
  have hphi : ∀ M ψ, OutTest η₀ M ψ →
      MixDiff (fun ν => outFn eps ν ψ) (fun ν x => outJ eps ν ψ x) ν₀ ν₁ := by
    intro M ψ hψ
    refine ⟨?_, fun s₀ hs₀ => ?_⟩
    · exact continuousOn_outFn_mix hS hK ha0 (β := κ / 2) (by positivity)
        (by rw [show 2 * (κ / 2) = κ by ring]; exact hκa) hfin htail
        (fun s _ => (hfacts s).2.2.2.1) (fun s _ => (hfacts s).2.2.2.2.2) hclo0
        (fun s _ => (hfacts s).2.1) hρexp hη₀ (by rw [hη₀def]; linarith [θK_pos]) hψ
    · exact hasDerivAt_outFn_mix hS hs₀ hfin hκ0 (hexp s₀) (hCpos s₀)
        (integrable_exp_output (hfacts s₀).2.2.2.1).1 (hfacts s₀).2.2.2.2.1
        (hfacts s₀).2.2.2.2.2 hη₀ (by rw [hη₀def]; linarith [θK_pos]) hψ
  -- row V
  have hV : ∀ s, lawV eps (mixPM ν₀ ν₁ s) = outFn eps (mixPM ν₀ ν₁ s) psiVar + 1 := fun s =>
    lawVar_lawPhi_eq (lawPhi_momClass (bAbs_le_regB vhi) (βAbs_le_regBeta D θ vlo)
      (regV_pos hvlo) (regV_le_half vlo) hepsZ ((hmix s).momClass hθ hvlo))
  have rowV : MixDiff (lawV eps) (lawJV eps) ν₀ ν₁ := by
    obtain ⟨hc, hd⟩ := hphi _ _ (outTest_psiVar hη₀)
    refine ⟨(hc.add continuousOn_const).congr fun s _ => hV s, fun s₀ hs₀ => ?_⟩
    exact ((hd s₀ hs₀).add_const 1).congr_of_eventuallyEq (Eventually.of_forall fun s => hV s)
  -- row A
  have hvar : ∀ s ∈ Icc (0 : ℝ) 1,
      lawVar (mixPM ν₀ ν₁ s) = (1 - s) * lawVar ν₀ + s * lawVar ν₁ := fun s hs =>
    lawVar_mixPM h₀ h₁ hθ hs
  have hvpos : ∀ s, 0 < lawVar (mixPM ν₀ ν₁ s) := fun s => hvlo.trans_le (hmix s).var_ge
  have rowA : MixDiff (lawA eps) (lawJA eps) ν₀ ν₁ := by
    have hvc : ContinuousOn (fun s => lawVar (mixPM ν₀ ν₁ s)) (Icc 0 1) :=
      ((continuous_const.sub continuous_id).mul continuous_const |>.add
        (continuous_id.mul continuous_const)).continuousOn.congr hvar
    refine ⟨(hvc.log fun s _ => (hvpos s).ne').add (hCcont.log fun s _ => (hCpos s).ne'),
      fun s₀ hs₀ => ?_⟩
    obtain ⟨hJ₀, hJ₁, hCd⟩ := hCder s₀ hs₀
    have hvd : HasDerivAt (fun s => lawVar (mixPM ν₀ ν₁ s)) (lawVar ν₁ - lawVar ν₀) s₀ := by
      have h := ((hasDerivAt_id s₀).const_sub 1 |>.mul_const (lawVar ν₀)).add
        ((hasDerivAt_id s₀).mul_const (lawVar ν₁))
      have e : (-1 * lawVar ν₀ + 1 * lawVar ν₁) = lawVar ν₁ - lawVar ν₀ := by ring
      simp only [id] at h
      rw [e] at h
      refine h.congr_of_eventuallyEq ?_
      filter_upwards [Icc_mem_nhds hs₀.1 hs₀.2] with s hs using hvar s hs
    have hd := (hvd.log (hvpos s₀).ne').add (hCd.log (hCpos s₀).ne')
    set νb := mixPM ν₀ ν₁ s₀ with hνb
    have hsplit : ∀ {ν : ProbabilityMeasure ℝ}, RegLaw D θ vlo vhi ν →
        Integrable (lawJC eps νb) (ν : Measure ℝ) →
        ∫ x, lawJA eps νb x ∂(ν : Measure ℝ) =
          (∫ x, lawJC eps νb x ∂(ν : Measure ℝ)) / lawC eps νb + lawVar ν / lawVar νb := by
      intro ν hν hJ
      rw [show (fun x => lawJA eps νb x) = fun x => lawJC eps νb x / lawC eps νb +
          (x - 1) ^ 2 / lawVar νb from rfl,
        integral_add (hJ.div_const _) ((hν.integrable_sq_sub_one hθ).div_const _),
        integral_div, integral_div, ← hν.lawVar_eq]
    have hval : (∫ x, lawJA eps νb x ∂(ν₁ : Measure ℝ)) - ∫ x, lawJA eps νb x ∂(ν₀ : Measure ℝ) =
        (lawVar ν₁ - lawVar ν₀) / lawVar νb +
          (∫ x, lawJC eps νb x ∂(ν₁ : Measure ℝ) - ∫ x, lawJC eps νb x ∂(ν₀ : Measure ℝ)) /
            lawC eps νb := by
      rw [hsplit h₁ hJ₁, hsplit h₀ hJ₀]; ring
    rw [hval]
    exact hd
  exact ⟨rowA, rowV, hphi⟩

end

end PGM
