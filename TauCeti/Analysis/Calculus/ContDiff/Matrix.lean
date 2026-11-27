/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Instances.Matrix

/-!
# Smoothness of determinants and adjugates

The determinant of a square matrix is a polynomial in its entries, so a matrix-valued map whose
entries are `C^n` has a `C^n` determinant. This is the `C^n` counterpart of Mathlib's
`Continuous.matrix_det`, and holds at every regularity, including analytic regularity, globally
(`ContDiff.matrix_det`), on a set (`ContDiffOn.matrix_det`) and at a point
(`ContDiffAt.matrix_det`).

Each entry of the adjugate is the determinant of a matrix whose entries are entries of the
original matrix or constants, so the adjugate of such a map again has `C^n` entries
(`ContDiff.matrix_adjugate`, `ContDiffOn.matrix_adjugate` and `ContDiffAt.matrix_adjugate`), the
`C^n` counterpart of Mathlib's `Continuous.matrix_adjugate`.

For the Frobenius norm, differentiability passes to entries, to the trace and to the determinant
(`Differentiable.matrix_elem`, `Differentiable.matrix_trace`, `Differentiable.matrix_det`), the
counterparts of Mathlib's `Continuous.matrix_elem`, `Continuous.matrix_trace` and
`Continuous.matrix_det`.
-/

public section

section Differentiable

variable {𝕜 E α m n : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup α] [NormedSpace 𝕜 α] [Finite m] [Finite n]

open scoped Matrix.Norms.Frobenius

/-- An entry of a differentiable matrix-valued map is differentiable. Matrices carry the Frobenius
norm. -/
theorem Differentiable.matrix_elem {M : E → Matrix m n α} (hM : Differentiable 𝕜 M) (i : m)
    (j : n) : Differentiable 𝕜 fun x ↦ M x i j := by
  have := Fintype.ofFinite (α := m)
  have := Fintype.ofFinite (α := n)
  let e : Matrix m n α →L[𝕜] α :=
    ⟨Matrix.entryLinearMap 𝕜 α i j, continuous_id.matrix_elem i j⟩
  intro x
  refine ((e.differentiable.differentiableAt (x := M x)).comp x
    (hM.differentiableAt (x := x))).congr_of_eventuallyEq ?_
  filter_upwards with y
  rw [show (e : Matrix m n α → α) = Matrix.entryLinearMap 𝕜 α i j from
    ContinuousLinearMap.coe_mk' _ _]
  rfl

variable [Fintype n]

/-- The trace of a differentiable square-matrix-valued map is differentiable. Matrices carry the
Frobenius norm. -/
theorem Differentiable.matrix_trace {M : E → Matrix n n α} (hM : Differentiable 𝕜 M) :
    Differentiable 𝕜 fun x ↦ (M x).trace := by
  simp_rw [Matrix.trace, Matrix.diag_apply]
  exact Differentiable.fun_sum fun i _ ↦ hM.matrix_elem i i

end Differentiable

section DifferentiableDet

variable {𝕜 E α n : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedCommRing α] [NormedAlgebra 𝕜 α] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Frobenius

/-- The determinant of a differentiable square-matrix-valued map is differentiable. Matrices carry
the Frobenius norm. -/
theorem Differentiable.matrix_det {M : E → Matrix n n α} (hM : Differentiable 𝕜 M) :
    Differentiable 𝕜 fun x ↦ (M x).det := by
  simp_rw [Matrix.det_apply']
  refine Differentiable.fun_sum fun σ _ ↦ ?_
  have hp : Differentiable 𝕜 fun x ↦ ∏ i, M x (σ i) i := fun x ↦
    (HasFDerivAt.finsetProd (u := Finset.univ) (g := fun i y ↦ M y (σ i) i) fun i _ ↦
      ((hM.matrix_elem (σ i) i).differentiableAt (x := x)).hasFDerivAt).differentiableAt
  exact hp.const_mul ((Equiv.Perm.sign σ : ℤ) : α)

end DifferentiableDet

variable {𝕜 E 𝔸 ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Fintype ι] [DecidableEq ι] {n : WithTop ℕ∞}
  {s : Set E}

/-- A matrix-valued map whose entries are `C^n` on a set has a determinant that is `C^n` there. -/
theorem ContDiffOn.matrix_det {M : E → Matrix ι ι 𝔸}
    (hM : ∀ i j, ContDiffOn 𝕜 n (fun x ↦ M x i j) s) :
    ContDiffOn 𝕜 n (fun x ↦ (M x).det) s := by
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ ↦ contDiffOn_const.mul (contDiffOn_prod fun i _ ↦ hM _ _)

/-- A matrix-valued map whose entries are `C^n` at a point has a determinant which is `C^n` there.
-/
theorem ContDiffAt.matrix_det {M : E → Matrix ι ι 𝔸} {x : E}
    (hM : ∀ i j, ContDiffAt 𝕜 n (fun y ↦ M y i j) x) : ContDiffAt 𝕜 n (fun y ↦ (M y).det) x := by
  simp_rw [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ ↦ contDiffAt_const.mul (contDiffAt_prod fun i _ ↦ hM _ _)

/-- A matrix-valued map with `C^n` entries has a `C^n` determinant. -/
theorem ContDiff.matrix_det {M : E → Matrix ι ι 𝔸} (hM : ∀ i j, ContDiff 𝕜 n fun x ↦ M x i j) :
    ContDiff 𝕜 n fun x ↦ (M x).det :=
  contDiffOn_univ.1 (ContDiffOn.matrix_det fun i j ↦ (hM i j).contDiffOn)

/-- A matrix-valued map whose entries are `C^n` on a set has an adjugate whose entries are `C^n`
there. -/
theorem ContDiffOn.matrix_adjugate {M : E → Matrix ι ι 𝔸}
    (hM : ∀ i j, ContDiffOn 𝕜 n (fun x ↦ M x i j) s) (i j : ι) :
    ContDiffOn 𝕜 n (fun x ↦ (M x).adjugate i j) s := by
  simp only [Matrix.adjugate_apply]
  refine ContDiffOn.matrix_det fun k l ↦ ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hM k l

/-- A matrix-valued map whose entries are `C^n` at a point has an adjugate whose entries are `C^n`
there. -/
theorem ContDiffAt.matrix_adjugate {M : E → Matrix ι ι 𝔸} {x : E}
    (hM : ∀ i j, ContDiffAt 𝕜 n (fun y ↦ M y i j) x) (i j : ι) :
    ContDiffAt 𝕜 n (fun y ↦ (M y).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  refine ContDiffAt.matrix_det fun k l ↦ ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffAt_const
  · exact hM k l

/-- A matrix-valued map with `C^n` entries has an adjugate with `C^n` entries. -/
theorem ContDiff.matrix_adjugate {M : E → Matrix ι ι 𝔸}
    (hM : ∀ i j, ContDiff 𝕜 n fun x ↦ M x i j) (i j : ι) :
    ContDiff 𝕜 n fun x ↦ (M x).adjugate i j :=
  contDiffOn_univ.1 (ContDiffOn.matrix_adjugate (fun i j ↦ (hM i j).contDiffOn) i j)
