import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace SCHAUM_Problem_1_12
/-
Let $ABCD$ be a convex quadrilateral. Assume that the diagonal $BD \perp BC$ and $BD \perp DA$.
Suppose that $BC = DA$.

Prove that $ABCD$ is a parallelogram.
-/

structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  -- Let $ABCD$ be a convex quadrilateral.
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  ABCD_IsCvx : Quadrilateral.IsConvex (QDR A B C D)
  -- $A, B, C, D$ are pairwise distinct because $ABCD$ is convex.
  D_ne_B : D ≠ B := Quadrilateral_cvx.nd₂₄ (Quadrilateral_cvx.mk_is_convex ABCD_IsCvx)
  C_ne_B : C ≠ B := Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex ABCD_IsCvx)
  A_ne_D : A ≠ D := (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex ABCD_IsCvx)).symm
  -- Assume that the diagonal $BD \perp BC$ and $BD \perp DA$.
  BD_perp_BC : (SEG_nd B D D_ne_B) ⟂ (SEG_nd B C C_ne_B)
  BD_perp_DA : (SEG_nd B D D_ne_B) ⟂ (SEG_nd D A A_ne_D)
  -- Suppose that $BC = DA$.
  BC_eq_DA : (SEG B C).length = (SEG D A).length

-- Prove that $ABCD$ is a parallelogram.
theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (QDR_cvx e.A e.B e.C e.D e.ABCD_IsCvx).IsParallelogram_nd := by
  /- From $BD \perp BC$ and $BD \perp DA$ we have $BC \parallel DA$, which means $AD \parallel BC$.
  Combined with $AD = BC$ we can conclude that $ABCD$ is a parallelogram. -/
  -- From $BD \perp BC$ and $BD \perp DA$ we have $BC \parallel DA$.
  have BC_para_DA : (SEG_nd e.B e.C e.C_ne_B) ∥ (SEG_nd e.D e.A e.A_ne_D) := parallel_of_perp_perp (perpendicular.symm e.BD_perp_BC) e.BD_perp_DA
  -- Then $AD \parallel BC$.
  have AD_para_BC : (SEG_nd e.A e.D e.A_ne_D.symm) ∥ (SEG_nd e.B e.C e.C_ne_B) := SegND.rev_para_of_para BC_para_DA.symm
  -- $AD \parallel BC$ combined with $AD = BC$ finishes the proof.
  apply is_prg_nd_of_para_eq_length'
  · exact AD_para_BC
  · calc
      _ = (SEG e.D e.A).length := (SEG e.D e.A).length_of_rev_eq_length
      _ = _ := by exact e.BC_eq_DA.symm

end SCHAUM_Problem_1_12
