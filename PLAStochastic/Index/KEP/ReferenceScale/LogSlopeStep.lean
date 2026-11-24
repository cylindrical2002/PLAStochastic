import PLAStochastic.Index.KEP.ReferenceScale.KernelWard

/-!
# The actual residual step in logarithmic slope coordinates

Both orientations use the same positive physical slope `exp s`. The identities
retain the orientation in the spatial derivative and its transport velocity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepLogStep (f : ℝ → ℝ) (σ s t : ℝ) : ℝ :=
  f ((1 - σ * t) * Real.exp (-s)) * Real.exp (-s)

def kepLogStepFirst (f' : ℝ → ℝ) (σ s t : ℝ) : ℝ :=
  -σ * f' ((1 - σ * t) * Real.exp (-s)) * Real.exp (-s) ^ 2

def kepLogStepSlope (f f' : ℝ → ℝ) (σ s t : ℝ) : ℝ :=
  -kepLogStep f σ s t -
    (1 - σ * t) * f' ((1 - σ * t) * Real.exp (-s)) * Real.exp (-s) ^ 2

def kepLogStepSecond (f'' : ℝ → ℝ) (σ s t : ℝ) : ℝ :=
  σ ^ 2 * f'' ((1 - σ * t) * Real.exp (-s)) * Real.exp (-s) ^ 3

def kepLogStepMixed (f' f'' : ℝ → ℝ) (σ s t : ℝ) : ℝ :=
  -2 * kepLogStepFirst f' σ s t + (σ - t) * kepLogStepSecond f'' σ s t

theorem continuous_kepLogStep {f : ℝ → ℝ} (hf : Continuous f) (σ : ℝ) :
    Continuous (Function.uncurry (kepLogStep f σ)) := by
  unfold kepLogStep Function.uncurry
  fun_prop

theorem continuous_kepLogStepFirst {f' : ℝ → ℝ} (hf' : Continuous f') (σ : ℝ) :
    Continuous (Function.uncurry (kepLogStepFirst f' σ)) := by
  unfold kepLogStepFirst Function.uncurry
  fun_prop

theorem continuous_kepLogStepSlope {f f' : ℝ → ℝ}
    (hf : Continuous f) (hf' : Continuous f') (σ : ℝ) :
    Continuous (Function.uncurry (kepLogStepSlope f f' σ)) := by
  unfold kepLogStepSlope kepLogStep Function.uncurry
  fun_prop

theorem hasDerivAt_kepLogStep_right {f f' : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt f (f' t) t) (σ s t : ℝ) :
    HasDerivAt (kepLogStep f σ s) (kepLogStepFirst f' σ s t) t := by
  have hu : HasDerivAt (fun r : ℝ => (1 - σ * r) * Real.exp (-s))
      (-σ * Real.exp (-s)) t := by
    convert (((hasDerivAt_const t 1).sub ((hasDerivAt_id t).const_mul σ)).mul_const
      (Real.exp (-s))) using 1 <;> first | rfl | ring
  convert ((hd _).comp t hu).mul_const (Real.exp (-s)) using 1 <;>
    first | rfl | (dsimp [kepLogStepFirst]; ring)

theorem hasDerivAt_kepLogStep_slope {f f' : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt f (f' t) t) (σ s t : ℝ) :
    HasDerivAt (fun r => kepLogStep f σ r t) (kepLogStepSlope f f' σ s t) s := by
  have he : HasDerivAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-s)) s := by
    simpa only [Function.comp_def, mul_neg_one] using
      (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)
  convert ((hd _).comp s (he.const_mul (1 - σ * t))).mul he using 1 <;>
    first | rfl | (dsimp [kepLogStepSlope, kepLogStep]; ring)

theorem kepLogStepSlope_eq {f f' : ℝ → ℝ} {σ : ℝ}
    (hσ : σ ^ 2 = 1) (s t : ℝ) :
    kepLogStepSlope f f' σ s t =
      -kepLogStep f σ s t + (σ - t) * kepLogStepFirst f' σ s t := by
  dsimp [kepLogStepSlope, kepLogStepFirst]
  linear_combination (f' ((1 - σ * t) * Real.exp (-s)) * Real.exp (-s) ^ 2) * hσ

theorem continuous_kepLogStepSecond {f'' : ℝ → ℝ} (hf'' : Continuous f'') (σ : ℝ) :
    Continuous (Function.uncurry (kepLogStepSecond f'' σ)) := by
  unfold kepLogStepSecond Function.uncurry
  fun_prop

theorem continuous_kepLogStepMixed {f' f'' : ℝ → ℝ}
    (hf' : Continuous f') (hf'' : Continuous f'') (σ : ℝ) :
    Continuous (Function.uncurry (kepLogStepMixed f' f'' σ)) := by
  unfold kepLogStepMixed kepLogStepFirst kepLogStepSecond Function.uncurry
  fun_prop

theorem hasDerivAt_kepLogStepFirst_right {f' f'' : ℝ → ℝ}
    (hdd : ∀ t, HasDerivAt f' (f'' t) t) (σ s t : ℝ) :
    HasDerivAt (kepLogStepFirst f' σ s) (kepLogStepSecond f'' σ s t) t := by
  have hu : HasDerivAt (fun r : ℝ => (1 - σ * r) * Real.exp (-s))
      (-σ * Real.exp (-s)) t := by
    convert (((hasDerivAt_const t 1).sub ((hasDerivAt_id t).const_mul σ)).mul_const
      (Real.exp (-s))) using 1 <;> first | rfl | ring
  convert (((hdd _).comp t hu).const_mul (-σ)).mul_const (Real.exp (-s) ^ 2)
    using 1 <;> first | rfl | (dsimp [kepLogStepSecond]; ring)

theorem hasDerivAt_kepLogStepFirst_slope {f' f'' : ℝ → ℝ} {σ : ℝ}
    (hdd : ∀ t, HasDerivAt f' (f'' t) t) (hσ : σ ^ 2 = 1) (s t : ℝ) :
    HasDerivAt (fun r => kepLogStepFirst f' σ r t) (kepLogStepMixed f' f'' σ s t) s := by
  have he : HasDerivAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-s)) s := by
    simpa only [Function.comp_def, mul_neg_one] using
      (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)
  have hh := (((hdd _).comp s (he.const_mul (1 - σ * t))).const_mul (-σ)).mul (he.pow 2)
  convert hh using 1 <;> first
    | rfl
    | (dsimp [kepLogStepMixed, kepLogStepFirst, kepLogStepSecond]
       norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp_apply, Pi.pow_apply]
       linear_combination (σ * f'' ((1 - σ * t) * Real.exp (-s)) *
         Real.exp (-s) ^ 3) * hσ)

theorem hasDerivAt_kepLogStepSlope_right {f f' f'' : ℝ → ℝ} {σ : ℝ}
    (hd : ∀ t, HasDerivAt f (f' t) t) (hdd : ∀ t, HasDerivAt f' (f'' t) t)
    (hσ : σ ^ 2 = 1) (s t : ℝ) :
    HasDerivAt (kepLogStepSlope f f' σ s) (kepLogStepMixed f' f'' σ s t) t := by
  have hp := hasDerivAt_kepLogStep_right hd σ s t
  have hp' := hasDerivAt_kepLogStepFirst_right hdd σ s t
  have hh := hp.neg.add (((hasDerivAt_const t σ).sub (hasDerivAt_id t)).mul hp')
  have he : (-kepLogStep f σ s + ((fun _ => σ) - id) * kepLogStepFirst f' σ s) =
      kepLogStepSlope f f' σ s := by
    funext r
    exact (kepLogStepSlope_eq hσ s r).symm
  rw [he] at hh
  convert hh using 1 <;> first | rfl | (dsimp [kepLogStepMixed]; ring)

/-- The forward and reverse residuals of the unchanged actual kernel. -/
theorem kepLogStep_eq_kepStepSpatial {f : ℝ → ℝ} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (s t : ℝ) :
    kepLogStep f σ s t = kepStepSpatial f σ (σ * Real.exp s) t := by
  rcases hσ with rfl | rfl
  · simp only [kepLogStep, kepStepSpatial, one_mul, abs_of_pos (Real.exp_pos s),
      Real.exp_neg, div_eq_mul_inv]
  · simp only [kepLogStep, kepStepSpatial, neg_one_mul, abs_neg,
      abs_of_pos (Real.exp_pos s), Real.exp_neg, div_eq_mul_inv]
    congr 2
    ring

end

end PGM
