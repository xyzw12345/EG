import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace Problem1_4_
/-Let $B$ $D$ be points on segment $AF$, such that $AD = BF$. Let $C$ be a point.
Let $E$ be a point on the opposite side of $AF$ to $C$, such that EF ∥ AC and ED ∥ BC

Prove that $BC = DE$ and $AC = EF$.
-/

structure Setting1 (Plane : Type _) [EuclideanPlane Plane] where
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  E : Plane
  F : Plane
  AD_eq_BF : (SEG A D).length = (SEG B F).length
  A_ne_F : PtNe A F
  B_int : B LiesInt (SEG A F)
  D_int : D LiesInt (SEG A F)
  AFC_nd : ¬ colinear A F C
  AFE_nd : ¬ colinear A F E
  C_side : IsOnLeftSide C (SEG_nd A F)
  E_side : IsOnRightSide E (SEG_nd A F)

attribute [instance] Setting1.A_ne_F
instance C_ne_A {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: PtNe e.C e.A := by sorry
instance C_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: PtNe e.C e.B := by sorry
instance E_ne_D {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: PtNe e.E e.D := by sorry
instance E_ne_F {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: PtNe e.E e.F := by sorry

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting1 Plane where
  EF_para_AC : (SEG_nd E F) ∥ (SEG_nd A C)
  ED_para_BC : (SEG_nd E D) ∥ (SEG_nd B C)

--Prove that $BC = DE$.
theorem Result1 {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : (SEG e.B e.C).length = (SEG e.D e.E).length := by
  -- Claim : $B \ne A$, $D \ne F$, $E \ne F$.
  haveI B_ne_A : PtNe e.B e.A := by sorry
  haveI D_ne_F : PtNe e.D e.F := by sorry
  haveI E_ne_F : PtNe e.E e.F := by sorry
  -- We have $\angle B A C = \angle D F E$ and $\angle C B A = \angle E D F$ because alternate interior angles are equal.
  have ang2 : ∠ e.B e.A e.C = ∠ e.D e.F e.E := by
    have alt : IsAlternateIntAng (ANG e.C e.A e.B) (ANG e.E e.F e.D) := by
      constructor
      sorry
      sorry
    have : ∠ e.C e.A e.B = ∠ e.E e.F e.D := by apply value_eq_of_isalternateintang alt
    calc
      _ = - ∠ e.C e.A e.B := by apply neg_value_of_rev_ang
      _ = - ∠ e.E e.F e.D := by rw [this]
      _ = ∠ e.D e.F e.E := (neg_value_of_rev_ang).symm
  have ang3 : ∠ e.C e.B e.A = ∠ e.E e.D e.F := by
    have alt : IsAlternateIntAng (ANG e.C e.B e.A) (ANG e.E e.D e.F) := by sorry
    exact value_eq_of_isalternateintang alt
  -- We have $AB = FD$ because $AD = AF - BF = AF - BD = BF$.
  have seg1 : (SEG e.A e.B).length = (SEG e.F e.D).length := by
    calc
      _ = (SEG e.A e.F).length - (SEG e.B e.F).length := by
        apply eq_sub_of_add_eq
        symm
        apply length_eq_length_add_length e.B_int
      _ = (SEG e.A e.F).length - (SEG e.A e.D).length := by simp only [e.AD_eq_BF]
      _ = (SEG e.D e.F).length := (eq_sub_of_add_eq' (length_eq_length_add_length e.D_int).symm).symm
      _ = (SEG e.F e.D).length := length_of_rev_eq_length'
  have CAB_nd : ¬ colinear e.C e.A e.B := by sorry
  have EFD_nd : ¬ colinear e.E e.F e.D := by sorry
  -- Then $\triangle CAB ≅ \triangle EFD$ by SAS.
  have hcong : TriangleND.IsCongr (TRI_nd e.C e.A e.B CAB_nd) (TRI_nd e.E e.F e.D EFD_nd) := by
    apply TriangleND.congr_of_ASA
    · exact ang2
    · exact seg1
    · exact ang3
  -- The main goal can then be proved by the congruence.
  exact hcong.edge₂

-- Prove that $AC = EF$.
theorem Result2 {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : (SEG e.A e.C).length = (SEG e.E e.F).length := by
  -- Claim : $B \ne A$, $D \ne F$, $E \ne F$.
  haveI B_ne_A : PtNe e.B e.A := by sorry
  haveI D_ne_F : PtNe e.D e.F := by sorry
  haveI E_ne_F : PtNe e.E e.F := by sorry
  -- We have $\angle B A C = \angle D F E$ and $\angle C B A = \angle E D F$ because alternate interior angles are equal.
  have ang2 : ∠ e.B e.A e.C = ∠ e.D e.F e.E := by
    have alt : IsAlternateIntAng (ANG e.C e.A e.B) (ANG e.E e.F e.D) := by
      constructor
      sorry
      sorry
    have : ∠ e.C e.A e.B = ∠ e.E e.F e.D := by apply value_eq_of_isalternateintang alt
    calc
      _ = - ∠ e.C e.A e.B := by apply neg_value_of_rev_ang
      _ = - ∠ e.E e.F e.D := by rw [this]
      _ = ∠ e.D e.F e.E := (neg_value_of_rev_ang).symm
  have ang3 : ∠ e.C e.B e.A = ∠ e.E e.D e.F := by
    have alt : IsAlternateIntAng (ANG e.C e.B e.A) (ANG e.E e.D e.F) := by sorry
    exact value_eq_of_isalternateintang alt
  -- We have $AB = FD$ because $AD = AF - BF = AF - BD = BF$.
  have seg1 : (SEG e.A e.B).length = (SEG e.F e.D).length := by
    calc
      _ = (SEG e.A e.F).length - (SEG e.B e.F).length := by
        apply eq_sub_of_add_eq
        symm
        apply length_eq_length_add_length e.B_int
      _ = (SEG e.A e.F).length - (SEG e.A e.D).length := by simp only [e.AD_eq_BF]
      _ = (SEG e.D e.F).length := (eq_sub_of_add_eq' (length_eq_length_add_length e.D_int).symm).symm
      _ = (SEG e.F e.D).length := length_of_rev_eq_length'
  have CAB_nd : ¬ colinear e.C e.A e.B := by sorry
  have EFD_nd : ¬ colinear e.E e.F e.D := by sorry
  -- Then $\triangle CAB ≅ \triangle EFD$ by SAS.
  have hcong : TriangleND.IsCongr (TRI_nd e.C e.A e.B CAB_nd) (TRI_nd e.E e.F e.D EFD_nd) := by
    apply TriangleND.congr_of_ASA
    · exact ang2
    · exact seg1
    · exact ang3
  calc
    _ = (SEG e.C e.A).length := length_of_rev_eq_length'
    _ = (SEG e.E e.F).length := hcong.edge₃

end Problem1_4_
