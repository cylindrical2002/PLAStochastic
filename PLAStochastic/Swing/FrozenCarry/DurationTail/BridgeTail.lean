import PLAStochastic.Swing.FrozenCarry.DurationTail.BridgeConstraint
import PLAStochastic.Swing.Gaussian.Bridge.ConditionalBallot
import PLAStochastic.Swing.FrozenCarry.DurationTail.TailArithmetic

/-! Endpoint averaging of the actual frozen duration bridge constraint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- A direct second-moment bound suffices for averaging the random bridge starting height. -/
theorem gaussianReal_integral_abs_le (N : ℕ) :
    (∫ y : ℝ, |y| ∂gaussianReal 0 (N : ℝ≥0)) ≤ ((N : ℝ)+1)/2 := by
  have h1 : Integrable (fun y : ℝ => |y|) (gaussianReal 0 (N : ℝ≥0)) :=
    (memLp_id_gaussianReal (μ := 0) (v := (N : ℝ≥0)) 1).integrable (by norm_num) |>.abs
  have h2 : Integrable (fun y : ℝ => y^2) (gaussianReal 0 (N : ℝ≥0)) :=
    (memLp_id_gaussianReal (μ := 0) (v := (N : ℝ≥0)) 2).integrable_sq
  have hs : (∫ y : ℝ, y^2 ∂gaussianReal 0 (N : ℝ≥0)) = (N : ℝ) := by
    have hv := variance_of_integral_eq_zero (X := (id : ℝ → ℝ))
      (μ := gaussianReal 0 (N : ℝ≥0)) measurable_id.aemeasurable
      (by simpa only [id_eq] using integral_id_gaussianReal (μ := 0) (v := (N : ℝ≥0)))
    simpa only [variance_id_gaussianReal, NNReal.coe_natCast, id_eq] using hv.symm
  calc
    _ ≤ ∫ y : ℝ, (y^2+1)/2 ∂gaussianReal 0 (N : ℝ≥0) := by
      apply integral_mono_ae h1 ((h2.add (integrable_const 1)).div_const 2)
      exact ae_of_all _ (fun y => by
        dsimp only [Pi.add_apply]
        nlinarith [sq_nonneg (|y|-1), sq_abs y])
    _ = _ := by rw [integral_div, integral_add h2 (integrable_const 1), hs]; simp

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The conditioned bridge estimate is averaged over the actual Gaussian endpoint law. -/
theorem frozenPrefixLength_bridge_tail
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {N M : ℕ}
    (hMN : M < N) (hhalf : M ≤ N-M) (hM : 0 < M)
    (w : ℝ) {E : ℝ} (hE : 0 ≤ E) (hEN : 4*E ≤ N) :
    μ.real {ω | ((N+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X w E ω} ≤
      Real.sqrt 2*gaussianBallotConstant*(2*E/(N : ℝ)+(Real.sqrt (M : ℝ))⁻¹)*
        (max w 0+3/2+2*E/((N : ℝ)+1)) := by
  have := hi.isProbabilityMeasure
  have hN : 0 < N := hM.trans hMN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let b : ℝ → ℝ := fun y => max w 0+2*E/((N : ℝ)+1)+|y|/((N : ℝ)+1)
  have hb : Integrable b (gaussianReal 0 (N : ℝ≥0)) :=
    (integrable_const _).add (((memLp_id_gaussianReal (μ := 0) (v := (N : ℝ≥0)) 1).integrable
      (by norm_num)).abs.div_const _)
  have hb0 (y : ℝ) : 0 ≤ b y := by
    dsimp [b]
    positivity
  have hs : {ω | ((N+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X w E ω} ⊆
      gaussianBridgeVariableSurvives X N (frozenBridgeStart w E N) (2*E/(N : ℝ)) M := by
    intro ω hω
    exact ⟨frozenBridgeStart_nonneg_of_feasible hω,
      frozenPrefix_implies_bridge_survives hN hMN.le hω⟩
  have ha : 0 ≤ 2*E/(N : ℝ) := by positivity
  have ha' : 2*E/(N : ℝ) ≤ 1/2 := (div_le_iff₀ hNr).mpr (by linarith)
  have hh := gaussianBridgeVariableSurvives_bound hX hi hG hMN hhalf hM ha ha'
    (frozenBridgeStart_measurable w E N) hb hb0 (frozenBridgeStart_le w E N)
  have hmean : (∫ y, b y+1 ∂gaussianReal 0 (N : ℝ≥0)) ≤ max w 0+3/2+2*E/((N : ℝ)+1) := by
    have habs : Integrable (fun y : ℝ => |y|) (gaussianReal 0 (N : ℝ≥0)) :=
      ((memLp_id_gaussianReal (μ := 0) (v := (N : ℝ≥0)) 1).integrable (by norm_num)).abs
    change (∫ y, (max w 0+2*E/((N : ℝ)+1)+|y|/((N : ℝ)+1))+1 ∂gaussianReal 0 (N : ℝ≥0)) ≤ _
    rw [integral_add hb (integrable_const 1), integral_add (integrable_const _) (habs.div_const _),
      integral_div]
    simp only [integral_const, probReal_univ, one_smul]
    have hg := div_le_div_of_nonneg_right (gaussianReal_integral_abs_le N)
      (show (0 : ℝ) ≤ (N : ℝ)+1 by positivity)
    have hdiv : (((N : ℝ)+1)/2)/((N : ℝ)+1) = (1 : ℝ)/2 := by field_simp
    rw [hdiv] at hg
    linarith
  calc
    _ ≤ μ.real (gaussianBridgeVariableSurvives X N (frozenBridgeStart w E N) (2*E/(N : ℝ)) M) :=
      measureReal_mono hs
    _ ≤ _ := hh.trans (mul_le_mul_of_nonneg_left hmean (by
      have hc := gaussianBallotConstant_pos
      positivity))


/-- The actual duration has the ballot-scale tail for all horizons above the linear budget scale. -/
theorem frozenPrefixLength_duration_tail_general
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (w : ℝ) {E : ℝ} (hE : 1 ≤ E) {n : ℕ} (hn : 4*E+2 ≤ n) :
    μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω} ≤
      16*gaussianBallotConstant*(1+max w 0)*(E/(n : ℝ)+(Real.sqrt (n : ℝ))⁻¹) := by
  have hnR : (3 : ℝ) ≤ n := by linarith
  have hn3 : 3 ≤ n := by exact_mod_cast hnR
  have hN : 2 ≤ n-1 := by omega
  have hcast : ((n-1 : ℕ) : ℝ)+1 = n := by exact_mod_cast (show n-1+1 = n by omega)
  have hEN : 4*E ≤ ((n-1 : ℕ) : ℝ) := by linarith
  have hM : 0 < (n-1)/2 := by omega
  have hMN : (n-1)/2 < n-1 := by omega
  have hhalf : (n-1)/2 ≤ (n-1)-(n-1)/2 := by omega
  have hh := frozenPrefixLength_bridge_tail hX hi hG hMN hhalf hM w (by linarith : 0 ≤ E) hEN
  have ha := frozenBridge_tail_arithmetic hN w (by linarith : 0 ≤ E) hEN
  have he : n-1+1 = n := by omega
  simpa only [he, hcast] using hh.trans ha

/-- The paper's harmonic tail, including the ceiling endpoint ceil(E²). -/
theorem frozenPrefixLength_duration_tail
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (w : ℝ) {E : ℝ} (hE : 1 ≤ E) {n : ℕ} (hn : 4*E+2 ≤ n) (hnE : (n : ℝ) ≤ E^2+1) :
    μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω} ≤
      48*gaussianBallotConstant*(1+max w 0)*E/(n : ℝ) := by
  have hNr : (0 : ℝ) < n := by linarith
  have hs : Real.sqrt (n : ℝ) ≤ 2*E := by
    have hroot := Real.sq_sqrt hNr.le
    have hpos := Real.sqrt_nonneg (n : ℝ)
    nlinarith
  have hd : (Real.sqrt (n : ℝ))⁻¹ ≤ 2*E/(n : ℝ) := by
    have hroot := Real.sq_sqrt hNr.le
    apply (le_div_iff₀ hNr).mpr
    have hspos := Real.sqrt_pos.mpr hNr
    have he : (Real.sqrt (n : ℝ))⁻¹*(n : ℝ) = Real.sqrt (n : ℝ) := by
      calc
        _ = (Real.sqrt (n : ℝ))⁻¹*(Real.sqrt (n : ℝ))^2 := congrArg (fun z => (Real.sqrt (n : ℝ))⁻¹*z) hroot.symm
        _ = _ := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hspos.ne', one_mul]
    rw [he]
    exact hs
  have hh := frozenPrefixLength_duration_tail_general hX hi hG w hE hn
  have hc := gaussianBallotConstant_pos
  calc
    _ ≤ 16*gaussianBallotConstant*(1+max w 0)*(E/(n : ℝ)+(Real.sqrt (n : ℝ))⁻¹) := hh
    _ ≤ 16*gaussianBallotConstant*(1+max w 0)*(E/(n : ℝ)+2*E/(n : ℝ)) := by
      gcongr
    _ = _ := by ring

end SwingRepair
