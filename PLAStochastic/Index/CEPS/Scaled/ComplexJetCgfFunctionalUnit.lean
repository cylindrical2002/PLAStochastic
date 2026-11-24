import PLAStochastic.Index.CEPS.Scaled.ComplexJetCgfUnit
import PLAStochastic.Index.CEPS.Normal.FunctionalSlopeLift

/-! # Finite cumulant Morse units with compact-function-valued critical centers -/

noncomputable section
open Complex
namespace PGM

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace K] [CompactSpace K]

def cepsContinuousCgfFunctionalJetUnit (p : E → ℕ → ℂ) (N : ℕ)
    (A X : E → C(K, ℂ)) : E → C(K, ℂ) :=
  functionalSecondSlopeLift (fun u => cepsContinuousCgfJetModel (p u.1) N u.2)
    A A (fun u => A u + X u)

theorem cepsContinuousCgfFunctionalJetUnit_analyticAt {p : E → ℕ → ℂ} {N : ℕ}
    {A X : E → C(K, ℂ)} {u : E}
    (hp : ∀ i, AnalyticAt ℂ (fun v => p v i) u) (hA : AnalyticAt ℂ A u)
    (hX : AnalyticAt ℂ X u) : AnalyticAt ℂ (cepsContinuousCgfFunctionalJetUnit p N A X) u := by
  apply functionalSecondSlopeLift_analyticAt
    (cepsContinuousCgfJetModel_joint_analyticAt hp N _) hA hA (hA.add hX)

theorem cepsContinuousCgfFunctionalJetUnit_apply {p : E → ℕ → ℂ} {N : ℕ}
    {A X : E → C(K, ℂ)} {u : E}
    (hp : ∀ i, AnalyticAt ℂ (fun v => p v i) u) (k : K) :
    cepsContinuousCgfFunctionalJetUnit p N A X u k =
      cepsComplexCgfJetUnit (p u) N (A u k) (X u k) := by
  apply functionalSecondSlopeLift_apply (f := fun v : E => cepsComplexCgfJetModel (p v) N)
    (fun S => cepsContinuousCgfJetModel_joint_analyticAt hp N S)
    (fun S q => cepsContinuousCgfJetModel_apply (p u) N S q)
    (fun s => by
      simpa only [id_eq] using!
        (cepsComplexCgfJetModel_analyticAt (p := fun _ : ℂ => p u) (s := id) (x := s)
          (fun _ => analyticAt_const) analyticAt_id N).differentiableAt) k

theorem cepsContinuousCgfFunctionalJetUnit_zero {p : E → ℕ → ℂ} {N : ℕ}
    {A X : E → C(K, ℂ)} {u : E}
    (hp : ∀ i, AnalyticAt ℂ (fun v => p v i) u) (hA : A u = 0) (hX : X u = 0) :
    cepsContinuousCgfFunctionalJetUnit p N A X u =
      ContinuousMap.const K (p u (cepsJetCode (.inl 0)) / 2) := by
  apply ContinuousMap.ext
  intro k
  rw [cepsContinuousCgfFunctionalJetUnit_apply hp k]
  simp [hA, hX, cepsComplexCgfJetUnit_zero]

end PGM
