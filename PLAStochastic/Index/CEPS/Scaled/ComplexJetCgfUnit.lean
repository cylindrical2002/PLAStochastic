import PLAStochastic.Index.CEPS.Scaled.ComplexJetCgfFunction
import PLAStochastic.Index.CEPS.Scaled.ComplexJetSpatial
import PLAStochastic.Index.CEPS.Scaled.ComplexJetDependence
import PLAStochastic.Index.CEPS.Normal.BanachSlopeLift

/-! # Actual finite cumulant Morse units and their compact-function lifts -/

noncomputable section
open Complex Filter Topology
namespace PGM

def cepsComplexCgfJetUnit (p : ℕ → ℂ) (N : ℕ) (a x : ℂ) : ℂ :=
  dslope (dslope (cepsComplexCgfJetModel p N) a) a (a + x)

theorem cepsComplexCgfJetUnit_spec (p : ℕ → ℂ) (N : ℕ) (a x : ℂ) :
    cepsComplexCgfJetModel p N (a + x) = cepsComplexCgfJetModel p N a +
      deriv (cepsComplexCgfJetModel p N) a * x + x ^ 2 * cepsComplexCgfJetUnit p N a x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hax : a + x ≠ a := fun h => hx (add_eq_left.mp h)
    rw [cepsComplexCgfJetUnit, dslope_of_ne _ hax, slope_def_field,
      dslope_of_ne _ hax, slope_def_field, dslope_same]
    field_simp
    ring

theorem cepsComplexCgfJetUnit_zero (p : ℕ → ℂ) (N : ℕ) :
    cepsComplexCgfJetUnit p N 0 0 = p (cepsJetCode (.inl 0)) / 2 := by
  have he : dslope (cepsComplexCgfJetModel p N) 0 =
      fun s : ℂ => s * cepsCgfComplexJetPolynomial p N s := by
    funext s
    by_cases hs : s = 0
    · simp [hs, dslope_same, cepsComplexCgfJetModel_deriv_zero]
    · rw [dslope_of_ne _ hs, slope_def_field]
      simp only [cepsComplexCgfJetModel, sub_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
      field_simp
  have hP : AnalyticAt ℂ (cepsCgfComplexJetPolynomial p N) 0 :=
    cepsCgfComplexJetPolynomial_analyticAt (p := fun _ : ℂ => p) (s := id) (x := (0 : ℂ))
      (fun _ => analyticAt_const) analyticAt_id N
  rw [cepsComplexCgfJetUnit, zero_add, he, dslope_same]
  simpa [cepsCgfComplexJetPolynomial_zero, Pi.mul_apply, id_eq] using!
    ((hasDerivAt_id (0 : ℂ)).mul hP.differentiableAt.hasDerivAt).deriv

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def cepsContinuousCgfJetModel (p : ℕ → ℂ) (N : ℕ) (S : C(K, ℂ)) : C(K, ℂ) :=
  S ^ 2 * cepsCgfContinuousJetPolynomial p N S

omit [CompactSpace K] in
theorem cepsContinuousCgfJetModel_apply (p : ℕ → ℂ) (N : ℕ) (S : C(K, ℂ)) (k : K) :
    cepsContinuousCgfJetModel p N S k = cepsComplexCgfJetModel p N (S k) := by
  simp [cepsContinuousCgfJetModel, cepsComplexCgfJetModel, cepsCgfContinuousJetPolynomial_apply]

theorem cepsContinuousCgfJetModel_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {x : E} {p : E → ℕ → ℂ} {S : E → C(K, ℂ)}
    (hp : ∀ i, AnalyticAt ℂ (fun u => p u i) x) (hS : AnalyticAt ℂ S x) (N : ℕ) :
    AnalyticAt ℂ (fun u => cepsContinuousCgfJetModel (p u) N (S u)) x :=
  (hS.pow 2).mul (cepsCgfContinuousJetPolynomial_analyticAt hp hS N)

theorem cepsContinuousCgfJetModel_joint_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {x : E} {p : E → ℕ → ℂ}
    (hp : ∀ i, AnalyticAt ℂ (fun u => p u i) x) (N : ℕ) (S : C(K, ℂ)) :
    AnalyticAt ℂ (fun v : E × C(K, ℂ) => cepsContinuousCgfJetModel (p v.1) N v.2) (x, S) := by
  apply cepsContinuousCgfJetModel_analyticAt (p := fun v : E × C(K, ℂ) => p v.1)
    (S := Prod.snd) (x := (x, S)) _ analyticAt_snd N
  intro i
  simpa only [Function.comp_apply] using!
    (hp i).comp (x := (x, S)) (f := (Prod.fst : E × C(K, ℂ) → E)) analyticAt_fst

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def cepsContinuousCgfJetUnit (p : E → ℕ → ℂ) (N : ℕ) (a : E → ℂ)
    (X : E → C(K, ℂ)) : E → C(K, ℂ) :=
  compactSecondSlopeLift (fun u => cepsContinuousCgfJetModel (p u.1) N u.2)
    a a (fun u => ContinuousMap.const K (a u) + X u)

theorem cepsContinuousCgfJetUnit_analyticAt {p : E → ℕ → ℂ} {N : ℕ}
    {a : E → ℂ} {X : E → C(K, ℂ)} {x : E}
    (hp : ∀ i, AnalyticAt ℂ (fun u => p u i) x) (ha : AnalyticAt ℂ a x)
    (hX : AnalyticAt ℂ X x) : AnalyticAt ℂ (cepsContinuousCgfJetUnit p N a X) x := by
  apply compactSecondSlopeLift_analyticAt
    (cepsContinuousCgfJetModel_joint_analyticAt hp N _)
    ha ha (ha.continuousMap_const.add hX)

theorem cepsContinuousCgfJetUnit_apply {p : E → ℕ → ℂ} {N : ℕ}
    {a : E → ℂ} {X : E → C(K, ℂ)} {u : E}
    (hp : ∀ i, AnalyticAt ℂ (fun v => p v i) u) (k : K) :
    cepsContinuousCgfJetUnit p N a X u k = cepsComplexCgfJetUnit (p u) N (a u) (X u k) := by
  apply compactSecondSlopeLift_apply
    (fun S => cepsContinuousCgfJetModel_joint_analyticAt hp N S)
    (fun S q => cepsContinuousCgfJetModel_apply (p u) N S q)
    (fun s => (cepsComplexCgfJetModel_analyticAt (p := fun _ : ℂ => p u) (s := id) (x := s)
      (fun _ => analyticAt_const) analyticAt_id N).differentiableAt) k

/-- The actual removable Morse unit is jointly analytic in every finite cumulant
coordinate and both spatial coordinates, including the double collision. -/
theorem cepsComplexCgfJetUnit_pad_analyticAt (d N : ℕ)
    (u : ((Fin d → ℂ) × ℂ) × ℂ) :
    AnalyticAt ℂ (fun v : ((Fin d → ℂ) × ℂ) × ℂ =>
      cepsComplexCgfJetUnit (cepsComplexJetPad d v.1.1) N v.1.2 v.2) u := by
  let p : (((Fin d → ℂ) × ℂ) × ℂ) → ℕ → ℂ := fun v => cepsComplexJetPad d v.1.1
  have hp : ∀ v i, AnalyticAt ℂ (fun w => p w i) v := by
    intro v i
    simpa only [Function.comp_apply] using!
      (cepsComplexJetPad_analyticAt d i v.1.1).comp (x := v)
        (f := fun w : ((Fin d → ℂ) × ℂ) × ℂ => w.1.1)
        (analyticAt_fst.comp analyticAt_fst)
  let U : (((Fin d → ℂ) × ℂ) × ℂ) → C(PUnit.{1}, ℂ) :=
    cepsContinuousCgfJetUnit p N (fun v => v.1.2) (fun v => ContinuousMap.const PUnit.{1} v.2)
  have hU : AnalyticAt ℂ U u := cepsContinuousCgfJetUnit_analyticAt
    (hp u) (analyticAt_snd.comp analyticAt_fst) analyticAt_snd.continuousMap_const
  have he := ((ContinuousMap.evalCLM ℂ PUnit.unit.{1}).analyticAt (U u)).comp hU
  apply he.congr
  exact Filter.Eventually.of_forall (fun v => cepsContinuousCgfJetUnit_apply (hp v) PUnit.unit.{1})

end PGM
