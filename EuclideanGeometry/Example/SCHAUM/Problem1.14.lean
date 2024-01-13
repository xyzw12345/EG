import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel_trash
import EuclideanGeometry.Foundation.Construction.Polygon.Parallelogram_trash

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
  /- Because quadrilateral $ABCD$ is a parallelogram, $AB \parallel CD$, the alternate interior angle $\angle ABD = \angle CDB$,
  therefore $\angle PBM = \angle ABD = \angle CDB = \angle QDN$. Also, $\angle BMP = \pm\frac{\pi}{2}$, $\angle DNQ = \pm\frac{\pi}{2}$
  because $M$ and $N$ are the foot of perpendicular from $P$, $Q$ to $BD$, respectively.
  In $\triangle MBP$ and $\triangle NDQ$,
  $\bullet \qquad \angle BMP = \angle DNQ \mod \pi$
  $\bullet \qquad \angle PBM = \angle QDN$
  $\bullet \qquad BP = DQ$
  Thus $\triangle MBP \congr \triangle NCQ$ (by AAS),
  which implies $PM = QN$.
  -/
  -- We have $M, B, P$ are not collinear because $P$ is not on line $BD$, namely line $BM$.
  have MBP_nd : ¬ colinear e.M e.B e.P := by sorry
  -- We have $N, D, Q$ are not collinear because $Q$ is not on line $BD$, namely line $ND$.
  have NDQ_nd : ¬ colinear e.N e.D e.Q := by sorry
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
  -- $\angle PMB = \pm\frac{\pi}{2}$, $\angle QND = \pm\frac{\pi}{2}$ because $M$ and $N$ are the foot of perpendicular from $P$, $Q$ to $BD$, respectively.
  have ang_PMB_dval_eq_pi_div_two : (ANG e.P e.M e.B).dvalue = ↑(π / 2) := by
    apply angle_dval_eq_pi_div_two_at_perp_foot (l := (LIN e.B e.D))
    · sorry -- trivial, but can't be fixed now
    · exact e.not_P_lieson_BD
    · exact e.perp_foot_M
  have ang_QND_dval_eq_pi_div_two : (ANG e.Q e.N e.D).dvalue = ↑(π / 2) := by
    apply angle_dval_eq_pi_div_two_at_perp_foot (l := (LIN e.B e.D))
    · sorry -- trivial, but can't be fixed now
    · exact e.not_Q_lieson_BD
    · exact e.perp_foot_N
  -- So $\angle BMP = \angle DNQ \mod \pi$.
  have ang1 : (ANG e.B e.M e.P).dvalue = (ANG e.D e.N e.Q).dvalue := by
    calc
      -- $\angle BMP = -\angle PMB$ by symmetry.
      _ = - (ANG e.P e.M e.B).dvalue := by apply neg_dvalue_of_rev_ang
      -- $-\angle PMB$ equals to $-\pi / 2 (\mod \pi)$ because their opposite numbers are equal.
      _ = - ↑(π / 2) := by simp only [ang_PMB_dval_eq_pi_div_two]
      -- $-\pi / 2$ equals to $-\angle QND (\mod \pi)$ because their opposite numbers are equal.
      _ = - (ANG e.Q e.N e.D).dvalue := by simp only [ang_QND_dval_eq_pi_div_two]
      -- $\angle QND = \angle
      _ = _ := by apply (neg_dvalue_of_rev_ang _ _).symm
  -- Because quadrilateral $ABCD$ is a parallelogram, $AB \parallel CD$, the alternate interior angle $\angle ABD = \angle CDB$, therefore $\angle PBM = \angle ABD = \angle CDB = \angle QDN$.
  have ang2 : ∠ e.P e.B e.M = ∠ e.Q e.D e.N := by
    calc
      -- $\angle PBM = \angle ABD$ because $P$ lies on ray $BA$ and $M$ lies on ray $BD$.
      _ = ∠ e.A e.B e.D := by sorry -- apply eq_ang_val_of_lies_int_lies_int
      -- $\angle ABD = \angle CDB$ is a property in parallelogram $ABCD$.
      _ = ∠ e.C e.D e.B := nd_eq_int_angle_value_of_is_prg_nd_variant e.ABCD_IsPRGnd
      -- $\angle CDB = \angle QDN$ because $Q$ lies on ray $DC$ and $N$ lies on ray $DB$.
      _ = _ := by sorry -- apply eq_ang_val_of_lies_int_lies_int
  -- $BP = DQ$ is stated in the problem.
  have seg1 : (SEG e.B e.P).length = (SEG e.D e.Q).length := e.BP_eq_DQ
  -- Thus $\triangle MBP \congr \triangle NCQ$ (by AAS).
  have MBP_congr_NCQ : (TRI_nd e.M e.B e.P MBP_nd).IsCongr (TRI_nd e.N e.D e.Q NDQ_nd) := by sorry -- Prove with a single line.
  -- Congruence implies $PM = QN$.
  exact MBP_congr_NCQ.edge₂

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
