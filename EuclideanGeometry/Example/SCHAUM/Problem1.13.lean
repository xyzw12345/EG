import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace SCHAUM_Problem_1_13
/-
Let $ABCD$ be a parallelogram in which the diagonals $AC$ and $BD$ meet at $M$. Let $P$ and $Q$ be points on $AM$ and $MC$, respectively, such that $MP = MQ$.

Prove that $PBQD$ is a nondegenarate parallelogram.
-/

structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  -- Let $ABCD$ be a nondegenarate parallelogram.
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  ABCD_IsPRGnd : (QDR A B C D) IsPRG_nd
  -- A nondegenerate parallelogram is convex, and its vertexes are pairwise distinct.
  ABCD_IsCvx : Quadrilateral.IsConvex (QDR A B C D) := is_convex_of_is_prg_nd (QDR A B C D) ABCD_IsPRGnd
  C_ne_A : C ≠ A := by sorry
  D_ne_B : D ≠ B := by sorry
  -- The diagonals $AC$ and $BD$ meet at $M$
  M : Plane
  M_inx : M = (QDR_cvx A B C D ABCD_IsCvx).diag_inx
  -- $M ≠ A$ and $M ≠ C$ because $A ≠ C$ and $M$ is the midpoint of $AC$.
  M_ne_A : M ≠ A := by sorry
  C_ne_M : C ≠ M := by sorry
  -- Let $P$ and $Q$ be points on $AM$ and $MC$, respectively, such that $MP = MQ$.
  P : Plane
  Q : Plane
  P_int_AM : P LiesInt (SEG_nd A M M_ne_A)
  Q_int_MC : Q LiesInt (SEG_nd M C C_ne_M)
  MP_eq_MQ : (SEG M P).length = (SEG M Q).length

theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (QDR e.P e.B e.Q e.D) IsPRG_nd := by
  /-
  Because $P$ lies in $AM$ and $Q$ lies in $CM$, $P ≠ Q$, combined with $MP = MQ$ we have $M$ is the
  midpoint of $PQ$. Also, because $ABCD$ is a parallelogram, $M$, as the intersection of diagonals, is the
  midpoint of $BD$, so $PBQD$ is a parallelogram.
  -/

  sorry

-- theorem is_prg_nd_of_is_prg_not_colinear₁₂₃

end SCHAUM_Problem_1_13
