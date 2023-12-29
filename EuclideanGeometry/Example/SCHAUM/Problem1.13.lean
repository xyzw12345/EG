import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace SCHAUM_Problem_1_13
/-
Let $ABCD$ be a parallelogram in which the diagonals $AC$ and $BD$ meet at $M$. Let $P$ and $Q$ be points on $AM$ and $MC$, respectively, such that $PM = MQ$.

Prove that $PBQD$ is a nondegenarate parallelogram.
-/

structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  -- Let $ABCD$ be a nondegenarate parallelogram.
  PRG_ABCD : Parallelogram_nd Plane
  A : Plane := PRG_ABCD.point₁
  B : Plane := PRG_ABCD.point₂
  C : Plane := PRG_ABCD.point₃
  D : Plane := PRG_ABCD.point₄
  QDR_ABCD_IsND : (QDR A B C D).IsND := by sorry
  QDR_ABCD_IsParallelogram_nd : (QDR A B C D).IsParallelogram_nd := by sorry
  QDRnd_ABCD_IsConvex : (QDR_nd A B C D QDR_ABCD_IsND).IsConvex := by sorry
  -- Then the vertexes of the parallelogram are pairwise distinct.
  C_ne_A : C ≠ A := by sorry
  D_ne_B : D ≠ B := by sorry
  -- The diagonals $AC$ and $BD$ meet at $M$.
  M : Plane
  M_inx : M = (QDR_cvx A B C D QDR_ABCD_IsND QDRnd_ABCD_IsConvex).diag_inx
  -- $M ≠ A$ and $M ≠ C$ because $A ≠ C$ and $M$ is the midpoint of $AC$.
  M_ne_A : M ≠ A := by sorry
  C_ne_M : C ≠ M := by sorry
  -- Let $P$ and $Q$ be points on $AM$ and $MC$, respectively, such that $PM = MQ$.
  P : Plane
  Q : Plane
  P_int_AM : P LiesInt (SEG_nd A M M_ne_A)
  Q_int_MC : Q LiesInt (SEG_nd M C C_ne_M)
  PM_eq_MQ : (SEG P M).length = (SEG M Q).length

theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (QDR e.P e.B e.Q e.D).IsParallelogram := by
  /-
  Because $P$ lies in $AM$ and $Q$ lies in $CM$, M lies in $PQ$. Combined with $PM = MQ$ we have $M$ is the
  midpoint of $PQ$. Also, because $ABCD$ is a parallelogram, $M$, as the intersection of diagonals, is the
  midpoint of $BD$, so $PBQD$ is a parallelogram.
  -/
  -- Because of the positional relationships on line AC, M lies in PQ.
  have M_lies_int_PQ : e.M LiesInt (SEG e.P e.Q) := by sorry
  -- Combined with $PM = MQ$ we have $M$ is the midpoint of $PQ$.
  have M_mid_of_PQ : e.M = (SEG e.P e.Q).midpoint := by
    -- Because $M$ lies in $PQ$, we only need to prove $PM = MQ$.
    apply eq_midpoint_iff_in_seg_and_dist_target_eq_dist_source.mpr ⟨M_lies_int_PQ, _⟩
    exact e.PM_eq_MQ
  /- Because $M$ is the only intersection of $AC$ and $BD$, and $P, Q$ are not equal to $M$,
  $P, B, D$ and $Q, B, D$ are not collinear, respectively. Therefore $PBQD$ is a nondegenerate quadrilateral.
  -/
  have PBD_not_colinear : ¬ colinear e.P e.B e.D := by sorry
  have QBD_not_colinear : ¬ colinear e.Q e.B e.D := by sorry
  have QDR_PBQD_IsND : (QDR e.P e.B e.Q e.D).IsND := by sorry
  -- Because $ABCD$ is a parallelogram, $M$, as the intersection of diagonals, is the midpoint of $BD$.
  have M_mid_of_BD : e.M = (SEG e.B e.D).midpoint := by
    simp only [e.M_inx]
    exact nd_eq_midpt_of_diag_inx_of_is_prg_nd'_variant e.QDR_ABCD_IsParallelogram_nd
  -- $M$ equals to the midpoint of both $PQ$ and $BD$ implies that $PBQD$ is a parallelogram.
  have PBQD_IsPRG : (QDR_nd e.P e.B e.Q e.D QDR_PBQD_IsND).IsParallelogram := by
    apply qdr_nd_is_prg_nd_of_diag_inx_eq_mid_eq_mid_variant
    -- The midpoints of $PQ$ and $BD$ are the same because both of them are $M$.
    simp only [M_mid_of_PQ.symm, M_mid_of_BD]
  exact PBQD_IsPRG

end SCHAUM_Problem_1_13
