import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousFunction.Polynomial



variable {n : ℕ}

def unitSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1

class VectorFieldOnSn (v : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))) where
  isCont : Continuous v
  isTang : ∀ x : EuclideanSpace ℝ (Fin (n+1)), x ∈ unitSphere → ⟪x, (v x)⟫_ℝ = 0



section

variable {v : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))} [VectorFieldOnSn v]
  {vDiff : ContDiff ℝ 1 v}
  {vUnit : ∀ x : EuclideanSpace ℝ (Fin (n+1)), x ∈ unitSphere → ‖x‖ = 1}
  {A : Set (EuclideanSpace ℝ (Fin (n+1)))} [CompactSpace A]

noncomputable def f (t : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) := x + t • (v x)

lemma ftInj : ∃ ε > 0, ∀ t : ℝ, |t| < ε → Function.Injective (f (v := v) t) := by
  sorry

lemma ftVol : ∃ ε > 0, ∃ P : Polynomial ℝ, ∀ t : ℝ, |t| < ε → MeasureTheory.volume ((f (v := v) t) '' A) = ENNReal.ofReal (P.toContinuousMap t) := by
  sorry

lemma ftIm : ∃ ε > 0, ∀ t : ℝ, |t| < ε → (f (v := v) t) '' unitSphere = Metric.sphere 0 (Real.sqrt (1 + t*t)) := by
  sorry

theorem HairyBallDiff (hn : Even n) : ∃ x, v x = 0 := by
  sorry

end



section

variable (v : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))) [VectorFieldOnSn v]

theorem HairyBallTheorem (hn : Even n) : ∃ x, v x = 0 := by
  sorry

end
