import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousFunction.Polynomial
import Mathlib.MeasureTheory.Function.Jacobian


/- Problèmes :
    · E := EuclideanSpace ℝ (Fin (n+1))
    · f (v := v) t
    · ∃ ε > 0, ∀ t : ℝ, |t| < ε → ...   OU   ∀ t : (𝓝 0), ...
-/


variable {n : ℕ}

def unitSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1

class VectorFieldOnSn (v : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))) where
  isCont : Continuous v
  isTang : ∀ x : EuclideanSpace ℝ (Fin (n+1)), x ∈ unitSphere → ⟪x, (v x)⟫_ℝ = 0



section

variable {v : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))} [VectorFieldOnSn v]
  {vContDiff : ContDiff ℝ 1 v}
  {vUnit : ∀ x : EuclideanSpace ℝ (Fin (n+1)), x ∈ unitSphere → ‖x‖ = 1}
  {A : Set (EuclideanSpace ℝ (Fin (n+1)))} [CompactSpace A]

noncomputable def f (t : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) := x + t • (v x)

lemma vLip : ∃ c > 0, LipschitzOnWith c v A := by
  sorry

lemma ftx_eq_fty {x y : EuclideanSpace ℝ (Fin (n+1))} {hx : x ∈ A} {hy : y ∈ A} (h : f (v := v) t x = f (v := v) t y) : x - y = t • (v y - v x) := by
  sorry

lemma eq_zero_of_le_self {α t : ℝ} (ht : |t| < 1) (h : α ≤ |t| * α) : α = 0 := by
  sorry

lemma ftInj : ∃ ε > 0, ∀ t : ℝ, |t| < ε → A.InjOn (f (v := v) t) := by
  let ⟨c, cpos, vlip⟩ := vLip (v := v) (A := A)
  use c⁻¹
  constructor
  · exact inv_pos.mpr cpos
  · intro t ht x hx y hy hxy
    apply eq_of_sub_eq_zero
    apply norm_eq_zero.1
    have : |t * c| < 1 := by sorry
    apply eq_zero_of_le_self this
    nth_rw 1 [ftx_eq_fty hxy]
    rw [norm_smul, abs_mul, mul_assoc]
    sorry
    sorry
    sorry
    sorry

lemma vDiff : Differentiable ℝ v :=
  vContDiff.differentiable (PartENat.withTopEquiv_symm_le.mp (Exists.intro (fun a => a) fun _ => Nat.le.refl))

lemma ftDiff : ∀ t : ℝ, Differentiable ℝ (f (v := v) t) := by
  sorry

noncomputable def f' (t : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) :
  EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)) where
  toFun h := h + t • (fderiv ℝ v x h)
  map_add' := sorry
  map_smul' := sorry
  cont := sorry

lemma ftDeriv : ∀ t : ℝ, ∀ x ∈ A, HasFDerivWithinAt (f (v := v) t) (f' (v := v) t x) A x := by sorry

lemma meas_A : MeasurableSet A := by sorry

open MeasureTheory

lemma integral_abs_det_ft : ∃ ε > 0, ∀ t : ℝ, |t| < ε →
  (∫⁻ x in A, ENNReal.ofReal |(f' (v := v) t x).det| ∂volume) = volume ((f (v := v) t) '' A) := by
  let ⟨ε, hε, h⟩ := @ftInj n v A /- ??? -/
  use ε
  constructor
  · exact hε
  · intro t ht
    exact lintegral_abs_det_fderiv_eq_addHaar_image volume meas_A (ftDeriv t) (h t ht)

lemma f't_det_poly : ∀ x : EuclideanSpace ℝ (Fin (n+1)), ∃ P : Polynomial ℝ,
  P.coeff 0 = 1 ∧ ∀ t : ℝ, (f' (v := v) t x).det = P.toContinuousMap t := by
  sorry

lemma ftVol_poly : ∃ ε > 0, ∃ P : Polynomial ℝ, ∀ t : ℝ, |t| < ε →
  volume ((f (v := v) t) '' A) = ENNReal.ofReal (P.toContinuousMap t) := by
  sorry

lemma ftIm : ∃ ε > 0, ∀ t : ℝ, |t| < ε →
  (f (v := v) t) '' unitSphere = Metric.sphere 0 (Real.sqrt (1 + t*t)) := by
  sorry

theorem HairyBallDiff (hn : Even n) : ∃ x, v x = 0 := by
  sorry

end



section

variable (v : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))) [VectorFieldOnSn v]

theorem HairyBallTheorem (hn : Even n) : ∃ x, v x = 0 := by
  sorry

end
