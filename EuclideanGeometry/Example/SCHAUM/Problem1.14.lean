import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel_trash
import EuclideanGeometry.Foundation.Construction.Polygon.Parallelogram_trash
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence_trash

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace SCHAUM_Problem_1_14
/-
Let $ABCD$ be a parallelogram. Let $P$ and $Q$ be points on the segments $AB$ and $CD$, respectively, such that $BP = DQ$. Let $M$ be the foot of perpendicular from $P$ to the diagonal $BD$, and let $N$ be the foot of perpendicular from $Q$ to the diagonal $BD$

Prove that $PM = QN$ and $PM \parallel QN$.
-/

structure Setting1 (Plane : Type _) [EuclideanPlane Plane] where
  -- Let $ABCD$ be a parallelogram.
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  QDR_ABCD_IsND : (QDR A B C D).IsND
  ABCD_IsPRGnd : (QDR A B C D).IsParallelogram_nd
  -- Let $P$ and $Q$ be points on the segments $AB$ and $CD$, respectively, such that $BP = DQ$.
  P : Plane
  Q : Plane
  P_int_AB : P LiesInt SEG A B
  Q_int_CD : Q LiesInt SEG C D
  BP_eq_DQ : (SEG B P).length = (SEG D Q).length
  D_ne_B : PtNe D B := ⟨nd₂₄_of_is_prg_nd (QDR A B C D) ABCD_IsPRGnd⟩
  -- Let $M$ be the foot of perpendicular from $P$ to the diagonal $BD$.
  M : Plane
  perp_foot_M : M = perp_foot P (LIN B D)
  -- Let $N$ be the foot of perpendicular from $Q$ to the diagonal $BD$.
  N : Plane
  perp_foot_N : N = perp_foot Q (LIN B D)

attribute [instance] Setting1.D_ne_B

-- Because $P$ is not on line $BD$, $M$, the foot of the perpendicular from $P$ to the diagonal $BD$ doesn't equal to $P$.
lemma not_P_lieson_BD {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : ¬ e.P LiesOn (LIN e.B e.D) := sorry
lemma not_Q_lieson_BD {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : ¬ e.Q LiesOn (LIN e.B e.D) := sorry
instance M_ne_P {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.M e.P where
  out := by
    rw [e.perp_foot_M]
    exact (perp_foot_eq_self_iff_lies_on e.P (LIN e.B e.D)).not.mpr (not_P_lieson_BD)
instance N_ne_Q {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.N e.Q where
  out := by
    rw [e.perp_foot_N]
    exact (perp_foot_eq_self_iff_lies_on e.Q (LIN e.B e.D)).not.mpr (not_Q_lieson_BD)

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends (Setting1 Plane) where
  not_P_lieson_BD : ¬ P LiesOn (LIN B D) := not_P_lieson_BD
  not_Q_lieson_BD : ¬ Q LiesOn (LIN B D) := not_Q_lieson_BD

-- Prove that $PM = QN$.
theorem result1 {Plane : Type _} [EuclideanPlane Plane] (e : Setting2 Plane) : (SEG e.P e.M).length = (SEG e.Q e.N).length := by
  /-
  In $\triangle PBD$ and $\triangle QDB$,
  $\bullet \qquad PB = QD$
  $\bullet \qquad \angle BPD = \angle DQB$ by the properties of a parallelogram
  $\bullet \qquad BD = DB$
  Thus $\triangle PBD \congr \triangle QDB$ (by SAS), which implies the lengths of the corresponding heights of the two triangle is equal, $PM = QN$.
  -/
  -- We have $P, B, D$ are not collinear because $P$ is not on line $BD$
  have PBD_nd : ¬ colinear e.P e.B e.D := by sorry
  -- We have $Q, D, B$ are not collinear because $Q$ is not on line $BD$
  have QDB_nd : ¬ colinear e.Q e.D e.B := by sorry
  -- We have $B \ne M$.
  haveI B_ne_M : PtNe e.B e.M := by sorry
  -- We have $P \ne M$.
  haveI P_ne_M : PtNe e.P e.M := by sorry
  -- We have $D \ne N$.
  haveI D_ne_N : PtNe e.D e.N := by sorry
  -- We have $Q \ne N$.
  haveI Q_ne_N : PtNe e.Q e.N := by sorry
  -- We have $P \ne B$.
  haveI P_ne_B : PtNe e.P e.B := by sorry
  -- We have $Q \ne D$.
  haveI Q_ne_D : PtNe e.Q e.D := by sorry
  -- We have $A \ne B$.
  haveI A_ne_B : PtNe e.A e.B := by sorry
  -- We have $D \ne B$.
  haveI D_ne_B : PtNe e.D e.B := by sorry
  -- We have $C \ne D$.
  haveI C_ne_D : PtNe e.C e.D := by sorry
  -- We have $B \ne D$.
  haveI B_ne_D : PtNe e.B e.D := by sorry
  -- $\triangle PBD \congr \triangle QDB$ (by SAS)
  have PBD_congr_QDB : (TRI_nd e.B e.D e.P (perm_colinear_trd_fst_snd.mt PBD_nd)) ≅ (TRI_nd e.D e.B e.Q (perm_colinear_trd_fst_snd.mt QDB_nd)) := by
    apply TriangleND.congr_of_SAS
    -- $PB = QD$
    calc
      -- $PB = BP$ by symmetry
      _ = (SEG e.B e.P).length := length_of_rev_eq_length'
      -- $BP = DQ$ by condition
      _ = (SEG e.D e.Q).length := e.BP_eq_DQ
      -- $DQ = QD$ by symmetry
      _ = _ := length_of_rev_eq_length'
    -- $\angle BPD = \angle DQB$
    sorry
    -- $BD = DB$ by symmetry
    exact length_of_rev_eq_length'
  -- $M, N$ are perpendicular foots
  simp only [e.perp_foot_M, e.perp_foot_N]
  -- line $BD$ and line $DB$ are identical
  have BD_is_DB : (LIN e.B e.D) = (LIN e.D e.B) := (SEG_nd e.B e.D).toLine_eq_rev_toLine
  nth_rw 2 [BD_is_DB]
  -- $PM$ and $QN$ is equal as the correspongding heights of $\triangle PBD$ and $\triangle QDB$
  exact height₃_eq_of_congr PBD_congr_QDB

-- Prove that $PM \parallel QN$.
theorem result2 {Plane : Type _} [EuclideanPlane Plane] (e : Setting2 Plane) : (LIN e.P e.M) ∥ (LIN e.Q e.N) := by
  /-
  We have $PM \perp BD$ and $BD \perp QN$ because $M$ is the perpendicular foot from $P$ to $BD$, respectively.
  Then $PM \perp QN$ because $PM \perp BD$ and $BD \perp QN$.
  -/
  -- We have $PM \perp BD$ because $M$ is the perpendicular foot from $P$ to $BD$.
  have PM_perp_BD : LIN e.P e.M ⟂ (LIN e.B e.D) := by
    simp only [e.perp_foot_M]
    exact line_of_self_perp_foot_perp_line_of_not_lies_on e.not_P_lieson_BD
  -- We have $BD \perp QN$ because $N$ is the perpendicular foot from $Q$ to $BD$.
  have BD_perp_QN : LIN e.B e.D ⟂ LIN e.Q e.N := by
    simp only [e.perp_foot_N]
    exact perpendicular.symm (line_of_self_perp_foot_perp_line_of_not_lies_on e.not_Q_lieson_BD)
  -- Then $PM \perp QN$ because $PM \perp BD$ and $BD \perp QN$.
  exact parallel_of_perp_perp (l₂ := LIN e.B e.D) PM_perp_BD BD_perp_QN

end SCHAUM_Problem_1_14
