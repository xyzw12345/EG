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
  ABCD_IsND : (QDR A B C D).IsND
  QDRnd_ABCD_IsCvx : Quadrilateral_nd.IsConvex (QDR_nd A B C D ABCD_IsND)
  -- $A, B, C, D$ are pairwise distinct because $ABCD$ is convex.
  D_ne_B : PtNe D B := Quadrilateral_cvx.nd₂₄ (Quadrilateral_cvx.mk_is_convex QDRnd_ABCD_IsCvx)
  C_ne_B : PtNe C B := ⟨ABCD_IsND.nd₂₃⟩
  A_ne_D : PtNe A D := ⟨(ABCD_IsND.nd₁₄).symm⟩
  -- Assume that the diagonal $BD \perp BC$ and $BD \perp DA$.
  BD_perp_BC : (SEG_nd B D D_ne_B.out) ⟂ (SEG_nd B C)
  BD_perp_DA : (SEG_nd B D D_ne_B.out) ⟂ (SEG_nd D A)
  -- Suppose that $BC = DA$.
  BC_eq_DA : (SEG B C).length = (SEG D A).length

attribute [instance] Setting.D_ne_B
attribute [instance] Setting.C_ne_B
attribute [instance] Setting.A_ne_D

-- Prove that $ABCD$ is a parallelogram.
theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (QDR_cvx e.A e.B e.C e.D e.ABCD_IsND e.QDRnd_ABCD_IsCvx).IsParallelogram_nd := by
  /- From $BD \perp BC$ and $BD \perp DA$ we have $BC \parallel DA$, which means $AD \parallel BC$.
  Combined with $AD = BC$ we can conclude that $ABCD$ is a parallelogram. -/
  -- From $BD \perp BC$ and $BD \perp DA$ we have $BC \parallel DA$.
  have BC_para_DA : (SEG_nd e.B e.C) ∥ (SEG_nd e.D e.A) := parallel_of_perp_perp (perpendicular.symm e.BD_perp_BC) e.BD_perp_DA
  -- Then $AD \parallel BC$.
  have AD_para_BC : (SEG_nd e.A e.D) ∥ (SEG_nd e.B e.C) := SegND.rev_para_of_para BC_para_DA.symm
  -- $AD \parallel BC$ combined with $AD = BC$ finishes the proof.
  apply qdr_cvx_is_prg_nd_of_para_eq_length'
  -- $AD \parallel BC$.
  · exact AD_para_BC
  -- $AD = DA = BC$.
  · calc
      -- $AD = DA$ by symmetry
      _ = (SEG e.D e.A).length := (SEG e.D e.A).length_of_rev_eq_length
      -- We have already known $AD = BC$
      _ = _ := e.BC_eq_DA.symm

end SCHAUM_Problem_1_12
