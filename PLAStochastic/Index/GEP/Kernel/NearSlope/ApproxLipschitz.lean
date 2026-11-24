import PLAStochastic.Index.GEP.Kernel.Insertion.Rewards
import PLAStochastic.Index.GEP.Kernel.Tail.Original.Scale
import PLAStochastic.Index.GEP.Kernel.Row.ClassUniform
import PLAStochastic.Index.GEP.Kernel.NearSlope.InsertionBlocks

/-!
# Class-uniform actual near kernels at the original tolerance scale

The density representative may be chosen by a separate absolute-mass theorem.
The near bound is uniform over every representative with the original pointwise
envelope. The four actual marked/exterior orientations share these constants.
-/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

set_option maxHeartbeats 1800000 in
/-- The actual scalar and output near contributions satisfy the original AL
scale. This is stated for each orientation before the IF finite sign sum. -/
theorem kernel_regLaw_insertion_near_for_density (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    ∃ ηB : ℝ, 0 < ηB ∧ ∀ α b : ℝ, 0 < α → 0 < b →
    ∃ K e0 : ℝ, 0 < K ∧ 2 ≤ e0 ∧
    ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
    ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, x ≤ 0 → f x=0) →
      (∀ x, f x ≤ D) → (∀ x, f x ≤ D*Real.exp (-θ*x)) →
      (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
    ∀ eps : ℝ, e0 ≤ eps → ∀ up outerUp : Bool,
      KernelApproxLip (b*Real.log eps) (K*Real.sqrt eps*Real.log eps^8) (K/eps)
        (krInsertionNearKernel ν f (2*eps) (α*Real.log (2*eps)) up outerUp
          (krInsertionScalarReward (lawC eps ν) (2*eps) up)) ∧
      ∀ η M : ℝ, 0 ≤ η → η ≤ ηB → ∀ ψ : ℝ → ℝ, OutTest η M ψ →
      KernelApproxLip (b*Real.log eps) (M*(K*Real.sqrt eps*Real.log eps^8)) (M*(K/eps))
        (krInsertionNearKernel ν f (2*eps) (α*Real.log (2*eps)) up outerUp
          (krInsertionOutputReward ν (lawC eps ν) ψ (2*eps) up outerUp)) := by
  let ε := krEps D vlo vhi
  have hε : 0 < ε := by
    have hk := krKappa_pos hD hvlo hvhi
    have hr := (kBVClass_constants hD hvlo hvhi).2.1
    exact lt_min (by positivity) (by linarith)
  obtain ⟨Kr,hKr,hLS⟩ := krLinearSurvival_exists D θ vlo vhi hD hθ hvlo hvhi
  obtain ⟨Lr,hFree⟩ := krFreeBound_exists D θ vlo vhi hD hθ hvlo hvhi
  obtain ⟨ηB,hηB,hphys⟩ := kernel_regLaw_tail_physical_scale D θ vlo vhi (ε/2)
    hD hθ hvlo hvhi (by positivity)
  obtain ⟨ep,hep,hphysical⟩ := hphys (θ/4) (by positivity)
  obtain ⟨ef,hef,hfacts⟩ := regLaw_facts hD hθ hvlo hvhi
  let B₀ := regB vhi
  have hB₀ : 0 < B₀ := (regV_pos hvlo).trans_le (regV_le_regB hvhi)
  let Ms := 512*B₀
  let Mo := Ms*(8*D/θ^2)*Real.exp ε
  have hMs : 0 < Ms := by dsimp [Ms]; positivity
  have hMo : 0 < Mo := by dsimp [Mo]; positivity
  refine ⟨ηB,hηB,?_⟩
  intro α b hα hb
  obtain ⟨C,w0,hC,hw0,hlog⟩ := krInsertion_coefficient_log_scale D θ vlo vhi Kr Lr α b
    hD hθ hvlo hvhi hα hb 1
  obtain ⟨w1,hw1⟩ := eventually_atTop.mp (kernel_log_cutoff_eventually hα (show (0 : ℝ) < 1/4 by norm_num))
  let K := (2^9 : ℝ)*C*(Ms+Mo)
  let e0 := max 96 (max ef (max ep (max w0 w1)))
  have hK : 0 < K := by dsimp [K]; positivity
  have hKs : (2^9 : ℝ)*(Ms*C) ≤ K := by
    calc
      _ = (2^9*C)*Ms := by ring
      _ ≤ (2^9*C)*(Ms+Mo) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hMo.le) (by positivity)
  have hKo : (2^9 : ℝ)*(Mo*C) ≤ K := by
    calc
      _ = (2^9*C)*Mo := by ring
      _ ≤ (2^9*C)*(Ms+Mo) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hMs.le) (by positivity)
  have hKs' : Ms*C ≤ K :=
    (le_mul_of_one_le_left (mul_pos hMs hC).le (by norm_num : (1 : ℝ) ≤ 2^9)).trans hKs
  have hKo' : Mo*C ≤ K :=
    (le_mul_of_one_le_left (mul_pos hMo hC).le (by norm_num : (1 : ℝ) ≤ 2^9)).trans hKo
  refine ⟨K,e0,hK,by dsimp [e0]; linarith [le_max_left (96 : ℝ) (max ef (max ep (max w0 w1)))],?_⟩
  intro ν hν f hf hf0 hfz hfD hfe hνf
  have hrow (w A a : ℝ) (hw : 1 ≤ w) (hA : 0 ≤ A) (haA : |a-1| ≤ A/w)
      (ha₁ : 1/2 ≤ |a|) (ha₂ : |a| ≤ 2) :
      KrBand D θ vlo vhi Kr Lr ν f w A a 1 a ∧
        KrBand D θ vlo vhi Kr Lr ν f w A a (-1) (-a) := by
    have H : KrBand D θ vlo vhi Kr Lr ν f w A a 1 a :=
      { hD := hD, hθ := hθ, hvlo := hvlo, hvhi := hvhi, hLS := hLS, hFree := hFree,
        hν := hν, hK := hKr.le, hf := hf, hf0 := hf0, hfz := hfz, hfD := hfD,
        hfe := hfe, hνf := hνf, hw := hw, hA := hA, haA := haA, ha₁ := ha₁,
        ha₂ := ha₂, hβ := Or.inl ⟨rfl,rfl⟩ }
    exact ⟨H,H.rev⟩
  intro eps heps up outerUp
  have he96 : 96 ≤ eps := (show 96 ≤ e0 from le_max_left _ _).trans heps
  have hep0 : 0 < eps := by linarith
  have he2 : 2 ≤ eps := by linarith
  have heF : ef ≤ eps := (show ef ≤ e0 from le_max_of_le_right (le_max_left _ _)).trans heps
  have heP : ep ≤ eps := (show ep ≤ e0 from le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans heps
  have heW : w0 ≤ 2*eps := by
    have ht : w0 ≤ e0 := le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
    linarith
  have heA : w1 ≤ 2*eps := by
    have ht : w1 ≤ e0 := le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
    linarith
  have hww : 1 ≤ 2*eps := by linarith
  have hwpos : 0 < 2*eps := by positivity
  obtain ⟨_,hA1,hAw⟩ := hw1 (2*eps) heA
  have hA : 0 ≤ α*Real.log (2*eps) := by linarith
  have hsubset := kernelNearSlopes_subset hwpos (by nlinarith : α*Real.log (2*eps) ≤ (2*eps)/4)
  have hne := kernelNearSlopes_nonempty hwpos (by linarith : 0 < α*Real.log (2*eps))
  have H (a : ℝ) (ha : a ∈ kernelNearSlopes (2*eps) (α*Real.log (2*eps))) :
      KrBand D θ vlo vhi Kr Lr ν f (2*eps) (α*Real.log (2*eps)) a 1 a := by
    have has := hsubset ha
    have ha0 : 0 < a := by linarith [has.1]
    exact (hrow (2*eps) (α*Real.log (2*eps)) a hww hA
      ((le_div_iff₀ hwpos).mpr (by
        have hh := ((kernelNearSlopes_iff hwpos).mp ha).le
        simpa only [mul_comm] using hh))
      (by rw [abs_of_pos ha0]; linarith [has.1])
      (by rw [abs_of_pos ha0]; exact has.2.le)).1
  have hCm := (hfacts eps heF ν hν).2.1
  have hCpos : 0 < lawC eps ν := lt_of_lt_of_le (by dsimp [B₀] at hB₀; positivity) hCm
  have hInv : 1/lawC eps ν ≤ Ms/(2*eps)^2 := by
    apply (one_div_le_one_div_of_le (by dsimp [B₀] at hB₀; positivity) hCm).trans_eq
    dsimp only [Ms,B₀]
    field_simp
    ring
  have hs := hlog ν heW (measurableSet_kernelNearSlopes _ _) hne hsubset H up outerUp hε.le le_rfl hMs.le
    (measurable_krInsertionScalarReward (lawC eps ν) (2*eps) up)
    (fun _ _ l r t g _ => krInsertion_scalar_reward_bound hCpos hMs.le hε.le hInv up l r t _ g)
  change KernelApproxLip (b*Real.log (2*eps)) (Ms*(C*Real.sqrt (2*eps)*Real.log (2*eps)^8))
    (Ms*(C/(2*eps)^1)) (krInsertionNearKernel ν f (2*eps) (α*Real.log (2*eps)) up outerUp _) at hs
  have hs' : KernelApproxLip (b*Real.log (2*eps))
      ((Ms*C)*Real.sqrt (2*eps)*Real.log (2*eps)^8) ((Ms*C)/(2*eps))
      (krInsertionNearKernel ν f (2*eps) (α*Real.log (2*eps)) up outerUp
        (krInsertionScalarReward (lawC eps ν) (2*eps) up)) := by
    convert hs using 1 <;> ring
  have hs'' := kernelApproxLip_width_transfer he2 hb.le (mul_pos hMs hC).le hs'
  constructor
  · apply hs''.mono
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKs (Real.sqrt_nonneg _))
        (pow_nonneg (Real.log_nonneg (by linarith)) _)
    · exact div_le_div_of_nonneg_right hKs' hep0.le
  · intro η M hη hηle ψ hψ
    obtain ⟨_,_,hnear,hscale⟩ := hphysical eps heP ν hν η hη hηle
    have hnear' : η/lawC eps ν ≤ ε/(2*(2*eps)^2) := hnear.trans_eq (by ring)
    have hM := hψ.nonneg
    have hEnv : M*(8*D/θ^2)/lawC eps ν*Real.exp ε ≤ (M*Mo)/(2*eps)^2 := by
      calc
        _ = (M*(8*D/θ^2)*Real.exp ε)*(1/lawC eps ν) := by ring
        _ ≤ (M*(8*D/θ^2)*Real.exp ε)*(Ms/(2*eps)^2) :=
          mul_le_mul_of_nonneg_left hInv (by positivity)
        _ = _ := by dsimp only [Mo]; ring
    have ho := hlog ν heW (measurableSet_kernelNearSlopes _ _) hne hsubset H up outerUp hε.le le_rfl
      (mul_nonneg hM hMo.le) (measurable_krInsertionOutputReward hψ ν (lawC eps ν) (2*eps) up outerUp)
      (fun a ha l r t g hout => krInsertion_output_reward_bound hν hθ hψ hη hCpos hscale
        (hsubset ha).1.le hww hε.le hnear' (mul_nonneg hM hMo.le) hEnv up outerUp l r t g hout)
    change KernelApproxLip (b*Real.log (2*eps))
      ((M*Mo)*(C*Real.sqrt (2*eps)*Real.log (2*eps)^8)) ((M*Mo)*(C/(2*eps)^1))
      (krInsertionNearKernel ν f (2*eps) (α*Real.log (2*eps)) up outerUp
        (krInsertionOutputReward ν (lawC eps ν) ψ (2*eps) up outerUp)) at ho
    have ho' : KernelApproxLip (b*Real.log (2*eps))
        ((M*Mo*C)*Real.sqrt (2*eps)*Real.log (2*eps)^8) ((M*Mo*C)/(2*eps))
        (krInsertionNearKernel ν f (2*eps) (α*Real.log (2*eps)) up outerUp
          (krInsertionOutputReward ν (lawC eps ν) ψ (2*eps) up outerUp)) := by
      convert ho using 1 <;> ring
    have ho'' := kernelApproxLip_width_transfer he2 hb.le (by positivity) ho'
    apply ho''.mono
    · have hh : (2^(8+1) : ℝ)*(M*Mo*C) ≤ M*K := by
        simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left hKo hM
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg _))
        (pow_nonneg (Real.log_nonneg (by linarith)) _)).trans_eq (by ring)
    · have hh : M*Mo*C ≤ M*K := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hKo' hM
      exact (div_le_div_of_nonneg_right hh hep0.le).trans_eq (by ring)


/-- The four physical terms with the derivative signs from the marked bridge.
The second pair is subtracted because its marked orientation is downward. -/
def kernelIFInsertionNearBoundary (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (w A : ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  krInsertionNearKernel ν f w A true true (kernelIFInsertionReward H w true true) x +
    krInsertionNearKernel ν f w A true false (kernelIFInsertionReward H w true false) x -
    (krInsertionNearKernel ν f w A false false (kernelIFInsertionReward H w false false) x +
      krInsertionNearKernel ν f w A false true (kernelIFInsertionReward H w false true) x)

theorem KernelApproxLip.sub {R L₁ L₂ ρ₁ ρ₂ : ℝ} {j₁ j₂ : ℝ → ℝ}
    (h₁ : KernelApproxLip R L₁ ρ₁ j₁) (h₂ : KernelApproxLip R L₂ ρ₂ j₂) :
    KernelApproxLip R (L₁+L₂) (ρ₁+ρ₂) (fun x => j₁ x-j₂ x) := by
  simpa only [abs_neg, abs_one, one_mul, neg_one_mul, ← sub_eq_add_neg] using
    h₁.add (h₂.const_mul (-1))

/-- Finite physical orientation sum preserves both AL budgets with factor four. -/
theorem kernel_IF_insertion_near_AL (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (w A : ℝ) (H : ℝ → ℝ) {R L E : ℝ}
    (h : ∀ up outerUp : Bool, KernelApproxLip R L E
      (krInsertionNearKernel ν f w A up outerUp (kernelIFInsertionReward H w up outerUp))) :
    KernelApproxLip R (4*L) (4*E) (kernelIFInsertionNearBoundary ν f w A H) := by
  have hh := ((h true true).add (h true false)).sub ((h false false).add (h false true))
  convert hh using 1 <;> first | rfl | ring

set_option maxHeartbeats 1800000 in
/-- Class-uniform AL for the signed four-orientation scalar and output insertions.
The law, density representative, tolerance and output test are selected after
all class constants. No regularity of the chosen density beyond the original
envelope is imposed. -/
theorem kernel_regLaw_signed_insertion_near (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    ∃ ηB : ℝ, 0 < ηB ∧ ∀ α b : ℝ, 0 < α → 0 < b →
    ∃ K e0 : ℝ, 0 < K ∧ 2 ≤ e0 ∧
    ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
    ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, x ≤ 0 → f x=0) →
      (∀ x, f x ≤ D) → (∀ x, f x ≤ D*Real.exp (-θ*x)) →
      (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
    ∀ eps : ℝ, e0 ≤ eps →
      KernelApproxLip (b*Real.log eps) (K*Real.sqrt eps*Real.log eps^8) (K/eps)
        (kernelIFInsertionNearBoundary ν f (2*eps) (α*Real.log (2*eps))
          (fun _ => 1/lawC eps ν)) ∧
      ∀ η M : ℝ, 0 ≤ η → η ≤ ηB → ∀ ψ : ℝ → ℝ, OutTest η M ψ →
      KernelApproxLip (b*Real.log eps) (M*(K*Real.sqrt eps*Real.log eps^8)) (M*(K/eps))
        (kernelIFInsertionNearBoundary ν f (2*eps) (α*Real.log (2*eps))
          (kernelPositiveBoundaryReward ν (lawC eps ν) ψ)) := by
  obtain ⟨ηB,hηB,hnear⟩ := kernel_regLaw_insertion_near_for_density D θ vlo vhi hD hθ hvlo hvhi
  refine ⟨ηB,hηB,?_⟩
  intro α b hα hb
  obtain ⟨K,e0,hK,he0,hclass⟩ := hnear α b hα hb
  refine ⟨4*K,e0,by positivity,he0,?_⟩
  intro ν hν f hf hf0 hfz hfD hfe hνf eps heps
  have hh := hclass ν hν f hf hf0 hfz hfD hfe hνf eps heps
  constructor
  · have hs := kernel_IF_insertion_near_AL ν f (2*eps) (α*Real.log (2*eps))
      (fun _ => 1/lawC eps ν) (fun up outerUp => by
        rw [kernel_IF_insertion_scalar_reward]
        exact (hh up outerUp).1)
    convert hs using 1 <;> ring
  · intro η M hη hηle ψ hψ
    have hs := kernel_IF_insertion_near_AL ν f (2*eps) (α*Real.log (2*eps))
      (kernelPositiveBoundaryReward ν (lawC eps ν) ψ) (fun up outerUp => by
        rw [kernel_IF_insertion_output_reward]
        exact (hh up outerUp).2 η M hη hηle ψ hψ)
    convert hs using 1 <;> ring

end
end PGM
