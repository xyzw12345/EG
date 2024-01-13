import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

namespace Schaum
namespace Problem1_2
/-
Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.Let $D$ be a point on $AB$.
Let $E$ be a point on $AC$ such that $AE = AD$.Let $P$ be the foot of perpendicular from $D$ to $BC$.
Let $Q$ be the foot of perpendicular from $E$ to $BC$.

Prove that $DP = EQ$.
-/

structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  -- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
  A : Plane
  B : Plane
  C : Plane
  not_colinear_ABC : ¬ colinear A B C
  isoceles_ABC : (▵ A B C).IsIsoceles
  --Let $D$ be a point on $AB$.
  D : Plane
  D_int_AB : D LiesInt (SEG A B)
  --Let $E$ be a point on $AC$,
  E : Plane
  E_int_AC: E LiesInt (SEG A C)
  -- such that $AE = AD$.
  AE_eq_AD : (SEG A E).length = (SEG A D).length
  -- Claim: $B \ne C$.
  B_ne_C : PtNe B C :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    ⟨(ne_of_not_colinear not_colinear_ABC).1.symm⟩
  -- Let $P$ be the foot of perpendicular from $D$ to $BC$.
  P : Plane
  hP : P = perp_foot D (LIN B C)
  -- Let $Q$ be the foot of perpendicular from $E$ to $BC$.
  Q : Plane
  hQ : Q = perp_foot E (LIN B C)

attribute [instance] Setting.B_ne_C

/- # Another Style of Setting-/
structure Setting1 (Plane : Type _) [EuclideanPlane Plane] where
  -- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
  A : Plane
  B : Plane
  C : Plane
  not_colinear_ABC : ¬ colinear A B C
  hisoc : (▵ A B C).IsIsoceles
  --Let $D$ be a point on $AB$.
  D : Plane
  D_int_AB : D LiesInt (SEG A B)
  --Let $E$ be a point on $AC$,
  E : Plane
  E_int_AC: E LiesInt (SEG A C)
  -- such that $AE = AD$.
  AE_eq_AD : (SEG A E).length = (SEG A D).length

-- Claim: $B \ne C$.
instance B_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: PtNe e.B e.C :=
  -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
  ⟨(ne_of_not_colinear e.not_colinear_ABC).1.symm⟩

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting1 Plane where
  -- Let $P$ be the foot of perpendicular from $D$ to $BC$.
  P : Plane
  hP : P = perp_foot D (LIN B C)
  -- Let $Q$ be the foot of perpendicular from $E$ to $BC$.
  Q : Plane
  hQ : Q = perp_foot E (LIN B C)

-- Prove that $DP = EQ$.
theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (SEG e.D e.P).length = (SEG e.E e.Q).length := by
/-
  In the isoceles triangle $ABC$, we have $AB = AC$.
  Thus we have $BD = AB - AD = AC - AE = CE$.
  In the isoceles triangle $ABC$, we have $\angle ABC = - \angle ACB$.
  Therefore, $\angle DBP = \angle ABC = -\angle ACB = - \angle ECQ$.
  Since $DP$ is perpendicular to $BC$ at $P$, we have $\angle DPB = \pi/2$ or $ - \pi/2$.
  Since $EQ$ is perpendicular to $BC$ at $Q$, we have $\angle EQC = \pi/2$ or $ - \pi/2$.
  Thus $\angle DPB = - \angle EQC \mod \pi$.
  In $\triangle DBP$ and $\triangle EQC$,
  $\bullet \qquad \angle DBP = - \angle ECQ$
  $\bullet \qquad \angle DPB = - \angle EQC \mod \pi$
  $\bullet \qquad BD = CE$
  Thus $\triangle DPB \congr_a \triangle EQC$ (by AAS).
  Therefore, $DP = EQ$.
-/
  -- In the isoceles triangle $ABC$, we have $AB = AC$.
  have isoceles_ABC' : (SEG e.A e.B).length = (SEG e.A e.C).length := by
    calc
      -- $AB = CA$ by isoceles,
      _ = (SEG e.C e.A).length := e.isoceles_ABC.symm
      -- $CA = AC$ by symmetry.
      _ = (SEG e.A e.C).length := (SEG e.A e.C).length_of_rev_eq_length
  -- Thus we have $BD = AB - AD = AC - AE = CE$.
  have seg1 : (SEG e.B e.D).length = (SEG e.C e.E).length := by
    calc
      -- $BD = DB$ by symmetry,
      _ = (SEG e.D e.B).length := by sorry
      -- $DB = AB - AD$ since $D$ lies on $AB$,
      _ = (SEG e.A e.B).length - (SEG e.A e.D).length := by
        rw [← eq_sub_of_add_eq']
        exact sorry -- (length_eq_length_add_length (SEG A B) D (D_on_seg)).symm
      -- $AB - AD = AC - AE$ since $AB = AC$ and $AD = AE$,
      _ = (SEG e.A e.C).length - (SEG e.A e.E).length := by sorry -- rw [E_ray_position, ← isoceles_ABC']
      -- $AC - AE = EC$ since $E$ lies on $AC$.
      _ = (SEG e.E e.C).length := by
        rw [← eq_sub_of_add_eq']
        exact sorry --(length_eq_length_add_length (SEG A C) E (E_on_seg)).symm
      _ = (SEG e.C e.E).length := sorry -- length_eq_length_of_rev (SEG E C)
  -- We have $A \ne B$.
  haveI A_ne_B : PtNe e.A e.B := ⟨(ne_of_not_colinear e.not_colinear_ABC).2.2.symm⟩
  -- We have $A \ne C$.
  haveI A_ne_C : PtNe e.A e.C := ⟨(ne_of_not_colinear e.not_colinear_ABC).2.1⟩
  -- We have $C \ne B$.
  haveI C_ne_B : PtNe e.C e.B := ⟨(ne_of_not_colinear e.not_colinear_ABC).1⟩
  -- We have $\triangle PBD$ is nondegenerate
  haveI not_colinear_PBD : ¬ colinear e.P e.B e.D := by sorry
  -- We have $B \ne D$.
  haveI B_ne_D : PtNe e.B e.D := ⟨(ne_of_not_colinear not_colinear_PBD).1.symm⟩
  -- We have $P \ne D$.
  haveI P_ne_D : PtNe e.P e.D := ⟨(ne_of_not_colinear not_colinear_PBD).2.1⟩
  -- We have $P \ne B$.
  haveI P_ne_B : PtNe e.P e.B := ⟨(ne_of_not_colinear not_colinear_PBD).2.2.symm⟩
  -- We have $\triangle QCE$ is nondegenerate
  haveI not_colinear_QCE : ¬ colinear e.Q e.C e.E := by sorry
  -- We have $C \ne E$.
  haveI C_ne_E : PtNe e.C e.E := ⟨(ne_of_not_colinear not_colinear_QCE).1.symm⟩
  -- We have $Q \ne E$.
  haveI Q_ne_E : PtNe e.Q e.E := ⟨(ne_of_not_colinear not_colinear_QCE).2.1⟩
  -- We have $Q \ne C$.
  haveI Q_ne_C : PtNe e.Q e.C := ⟨(ne_of_not_colinear not_colinear_QCE).2.2.symm⟩
  -- Therefore, $\angle DBP = \angle ABC = -\angle ACB = - \angle ECQ$.
  have ang2 : ∠ e.D e.B e.P = - ∠ e.E e.C e.Q := by
    calc
      -- the angle $DBP$ is the same as angle $ABC$,
      _ = ∠ e.A e.B e.C := by sorry -- xxxxx_of_liesint_liesint, need order relations on a segment
      -- $\angle ABC = - \angle CBA$ by symmetry,
      _ = - ∠ e.C e.B e.A := neg_value_of_rev_ang
      -- $- \angle CBA = - \angle ACB$ because $\triangle ABC$ is isoceles,
      _ = - ∠ e.A e.C e.B := by
        simp
        exact (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := TRI_nd e.A e.B e.C e.not_colinear_ABC)).mp e.isoceles_ABC
      -- $- \angle ACB = \angle BCA$ by symmetry,
      _ = ∠ e.B e.C e.A := neg_value_of_rev_ang.symm
      -- the angle $ECQ$ is the same as angle $ACB$.
      _ = - ∠ e.E e.C e.Q := by sorry -- xxxxx_of_liesint_liesint
  -- $|\angle DPB| = |\angle EQC|$.
  have ang1 : ∠ e.B e.P e.D = - ∠ e.C e.Q e.E := by sorry
  -- $\triangle DPB \congr_a \triangle EQC$ (by AAS).
  have h : (TRI_nd e.P e.B e.D not_colinear_PBD) ≅ₐ (TRI_nd e.Q e.C e.E not_colinear_QCE) := by
    apply TriangleND.acongr_of_AAS
    -- $\cdot \angle DBP = - \angle ECQ$
    · exact ang1
    -- $\cdot |\angle DPB| = |\angle EQC|$
    · exact ang2
    -- $\cdot BD = CE$
    · exact seg1
  -- Therefore, $DP = EQ$.
  exact h.edge₂

end Problem1_2
end Schaum
end EuclidGeom
