import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousFunction.Polynomial
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv


/- Problèmes :
    · E := EuclideanSpace ℝ (Fin (n+1))
    · f (v := v) t
    · ∃ ε > 0, ∀ t : ℝ, |t| < ε → ...   OU   ∀ᶠ t ∈ (𝓝 0), ...
-/


variable {n : ℕ} (n_pos : 0 < n) (n_even : Even n)

def unitSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1

class VectorFieldOnSn (v : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))) where
  isCont : Continuous v
  isTang : ∀ x : EuclideanSpace ℝ (Fin (n+1)), x ∈ unitSphere → ⟪x, (v x)⟫_ℝ = 0



section

variable {v : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))} [VectorFieldOnSn v]
  {vContDiff : ContDiff ℝ 1 v}
  {vUnit : ∀ x : EuclideanSpace ℝ (Fin (n+1)), x ∈ unitSphere → ‖v x‖ = 1}
  {A : Set (EuclideanSpace ℝ (Fin (n+1)))} [CompactSpace A]

noncomputable def f (t : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) := x + t • (v x)

/- v est lipschitzienne sur A -/
lemma vLip : ∃ c > 0, LipschitzOnWith c v A := by
  sorry

lemma ftx_eq_fty {x y : EuclideanSpace ℝ (Fin (n+1))} {hx : x ∈ A} {hy : y ∈ A} (h : f (v := v) t x = f (v := v) t y) : x - y = t • (v y - v x) := by
  sorry

lemma eq_zero_of_le_self {α t : ℝ} (ht : |t| < 1) (h : α ≤ |t| * α) : α = 0 := by
  sorry

/- f t est injectif sur A pour t assez petit -/
lemma InjOn_A_ft : ∃ ε > 0, ∀ t : ℝ, |t| < ε → A.InjOn (f (v := v) t) := by
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

/- v est différentiable -/
lemma Diff_v : Differentiable ℝ v :=
  vContDiff.differentiable (PartENat.withTopEquiv_symm_le.mp (Exists.intro (fun a => a) fun _ => Nat.le.refl))

/- f t est différentiable -/
lemma Diff_ft : ∀ t : ℝ, Differentiable ℝ (f (v := v) t) := by
  sorry

/- différentielle de f t en x -/
noncomputable def f' (t : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) :=
  (ContinuousLinearMap.id ℝ _) + (t • (fderiv ℝ v x))

/- f' t x est la différentielle (stricte) de f t en x si t est assez petit -/
lemma ftStrictDeriv : ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ x, HasStrictFDerivAt (f (v :=v) t) (f' (v := v) t x) x := by
  sorry

/- f' t x est la différentielle de f t en x ∈ A -/
lemma ftDeriv : ∀ t : ℝ, ∀ x ∈ A, HasFDerivWithinAt (f (v := v) t) (f' (v := v) t x) A x := by
  sorry

open MeasureTheory

/- A est mesurable -/
lemma meas_A : MeasurableSet A := by
  sorry

lemma integral_abs_det_ft : ∃ ε > 0, ∀ t : ℝ, |t| < ε →
  (∫⁻ x in A, ENNReal.ofReal |(f' (v := v) t x).det| ∂volume) = volume ((f (v := v) t) '' A) := by
  let ⟨ε, hε, h⟩ := @InjOn_A_ft n v A /- ??? -/
  use ε
  constructor
  · exact hε
  · intro t ht
    exact lintegral_abs_det_fderiv_eq_addHaar_image volume meas_A (ftDeriv t) (h t ht)

/- det (f' t x) est polynomial en t et les coefficients sont continus en x -/
lemma f't_det_poly : ∃ P : EuclideanSpace ℝ (Fin (n+1)) → Polynomial ℝ, ∀ x : EuclideanSpace ℝ (Fin (n+1)),
  (P x).coeff 0 = 1
  ∧ ∀ t : ℝ, (f' (v := v) t x).det = (P x).toContinuousMap t
  ∧ ∀ k : ℕ, Continuous (fun x => (P x).coeff k) := by
  sorry

/- si P 0 = 1 alors P t > 0 pour t assez petit -/
lemma zero_lt_poly (P : Polynomial ℝ) (h0 : P.coeff 0 = 1) : ∃ ε > 0, ∀ t > 0, |t| < ε → P.toContinuousMap t > 0 := by
  sorry

/- det (f' t x) > 0 pour t assez petit -/
lemma zero_lt_det_f't (x : EuclideanSpace ℝ (Fin (n+1))) : ∃ ε > 0, ∀ t : ℝ, |t| < ε →
  (f' (v := v) t x).det > 0 := by
  sorry

/- |det (f' t x)| est polynomial en t et les coefficients sont continus en x -/
lemma abs_f'_det_poly : ∃ P : EuclideanSpace ℝ (Fin (n+1)) → Polynomial ℝ, ∀ x : EuclideanSpace ℝ (Fin (n+1)),
  ∀ t : ℝ, |(f' (v := v) t x).det| = (P x).toContinuousMap t
  ∧ ∀ k : ℕ, Continuous (fun x => (P x).coeff k) := by
  sorry

/- le volume de (f t)''(A) est polynomial en t -/
lemma vol_ft_A_poly : ∃ ε > 0, ∃ P : Polynomial ℝ, ∀ t : ℝ, |t| < ε →
  volume ((f (v := v) t) '' A) = ENNReal.ofReal (P.toContinuousMap t) := by
  sorry

/- f' t est une equivalence linéaire si t est assez petit -/
noncomputable def f't_equiv (t : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) : EuclideanSpace ℝ (Fin (n+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n+1)) where
  toFun := f' (v := v) t x
  map_add' := sorry
  map_smul' := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

lemma inner_self_v_eq_zero (t : ℝ) (x : EuclideanSpace ℝ (Fin (n+1))) : ⟪x, t • v x⟫_ℝ = 0 := by
  sorry

lemma im_ft_subset (t : ℝ) : (f (v := v) t) '' unitSphere ⊆ Metric.sphere 0 (Real.sqrt (1 + t*t)) := by
  intro y ⟨x, xUnit, hxy⟩
  rw [← hxy]
  unfold f; simp
  unfold unitSphere at xUnit
  have : ‖x‖ = 1 := by simp at xUnit; assumption
  rw [← Real.sqrt_mul_self (norm_nonneg _), norm_add_sq_eq_norm_sq_add_norm_sq_real (inner_self_v_eq_zero t x)]
  rw [this, norm_smul, vUnit x xUnit]
  simp

/-
TODO : f t induit f_restr t : unitSphere → Metric.sphere 0 (Real.sqrt (1 + t*t))
qui est toujours continue
-/

lemma rank_EuclideanSpace : FiniteDimensional.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1 := by
  sorry

lemma one_lt_rank_EuclideanSpace : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n+1))) := by
  apply FiniteDimensional.one_lt_rank_of_one_lt_finrank
  rw [rank_EuclideanSpace]
  linarith

/- f t est ouverte pour t assez petit (théorème d'inversion globale) -/
lemma ft_open : ∃ ε > 0, ∀ t : ℝ, |t| < ε → IsOpenMap (f (v := v) t) := by
  let ⟨ε, εpos, h⟩ := @ftStrictDeriv n v /- ??? -/
  use ε
  constructor; assumption
  intro t ht
  /- apply open_map_of_strict_fderiv_equiv (𝕜 := ℝ) (h t ht) -/
  sorry

lemma connected_sphere (t : ℝ) : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) (Real.sqrt (1 + t*t))) :=
  isConnected_sphere (one_lt_rank_EuclideanSpace n_pos) 0 (Real.sqrt_nonneg (1 + t*t))

lemma im_ft_open : ∃ ε > 0, ∀ t : ℝ, |t| < ε → IsOpen ((f (v:=v) t) '' unitSphere) := by
  sorry

lemma im_ft : ∃ ε > 0, ∀ t : ℝ, |t| < ε →
  (f (v := v) t) '' unitSphere = Metric.sphere 0 (Real.sqrt (1 + t*t)) := by
  sorry

theorem HairyBallDiff : ∃ x, v x = 0 := by
  sorry

end



section

variable (v : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1))) [VectorFieldOnSn v]

theorem HairyBallTheorem : ∃ x, v x = 0 := by
  sorry

end
