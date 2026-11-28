import LeanGeodesy.Spherical.Tammes18BV8Data

/-!
# Cholesky + Diagonal Dominance Verification for `tammes18BV8Cert`

Verifies all 18 positive-semidefinite certificate matrices (`F0..F8`, `S0`, `S1`,
and `M0..M6`) in the Lean 4 kernel using 10-row chunks via `choleskyCheckRows_append`.
-/

namespace Geodesy.Spherical

set_option maxRecDepth 400000
set_option maxHeartbeats 1600000

theorem t18b8_basic :
    decide (0 < tammes18BV8Cert.sDen) = true ∧
    decide (0 < tammes18BV8Cert.dK) = true ∧
    decide (0 < tammes18BV8Cert.dS0) = true ∧
    decide (0 < tammes18BV8Cert.dS) = true ∧
    decide (0 < tammes18BV8Cert.dR) = true ∧
    decide (-(tammes18BV8Cert.sDen : ℤ) < tammes18BV8Cert.sNum) = true ∧
    (List.range 16).all (fun k => decide (0 ≤ tammes18BV8Cert.c2.getD k 0)) = true ∧
    decide (tammes18BV8Cert.dM0 * tammes18BV8Cert.sc0 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.dM1 * tammes18BV8Cert.sc1 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.dM2 * tammes18BV8Cert.sc2 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.dM3 * tammes18BV8Cert.sc3 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.dM4 * tammes18BV8Cert.sc4 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.dM5 * tammes18BV8Cert.sc5 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.dM6 * tammes18BV8Cert.sc6 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.b0.length = tammes18BV8Cert.m0) = true ∧
    decide (tammes18BV8Cert.b1.length = tammes18BV8Cert.m1) = true ∧
    decide (tammes18BV8Cert.b2.length = tammes18BV8Cert.m2) = true ∧
    decide (tammes18BV8Cert.b3.length = tammes18BV8Cert.m3) = true ∧
    decide (tammes18BV8Cert.b4.length = tammes18BV8Cert.m4) = true ∧
    decide (tammes18BV8Cert.b5.length = tammes18BV8Cert.m5) = true ∧
    decide (tammes18BV8Cert.b6.length = tammes18BV8Cert.m6) = true := by
  decide

theorem t18b8_cF0 : isCholeskyDDValid 9 tammes18BV8Cert.dK tammes18BV8Cert.dR tammes18BV8Cert.F0 tammes18BV8Cert.R_F0 = true := by decide
theorem t18b8_cF1 : isCholeskyDDValid 8 tammes18BV8Cert.dK tammes18BV8Cert.dR tammes18BV8Cert.F1 tammes18BV8Cert.R_F1 = true := by decide
theorem t18b8_cF2 : isCholeskyDDValid 7 tammes18BV8Cert.dK tammes18BV8Cert.dR tammes18BV8Cert.F2 tammes18BV8Cert.R_F2 = true := by decide
theorem t18b8_cF3 : isCholeskyDDValid 6 tammes18BV8Cert.dK tammes18BV8Cert.dR tammes18BV8Cert.F3 tammes18BV8Cert.R_F3 = true := by decide
theorem t18b8_cF4 : isCholeskyDDValid 5 tammes18BV8Cert.dK tammes18BV8Cert.dR tammes18BV8Cert.F4 tammes18BV8Cert.R_F4 = true := by decide
theorem t18b8_cF5 : isCholeskyDDValid 4 tammes18BV8Cert.dK tammes18BV8Cert.dR tammes18BV8Cert.F5 tammes18BV8Cert.R_F5 = true := by decide
theorem t18b8_cF6 : isCholeskyDDValid 3 tammes18BV8Cert.dK tammes18BV8Cert.dR tammes18BV8Cert.F6 tammes18BV8Cert.R_F6 = true := by decide
theorem t18b8_cF7 : isCholeskyDDValid 2 tammes18BV8Cert.dK tammes18BV8Cert.dR tammes18BV8Cert.F7 tammes18BV8Cert.R_F7 = true := by decide
theorem t18b8_cF8 : isCholeskyDDValid 1 tammes18BV8Cert.dK tammes18BV8Cert.dR tammes18BV8Cert.F8 tammes18BV8Cert.R_F8 = true := by decide
theorem t18b8_cS0 : isCholeskyDDValid 9 tammes18BV8Cert.dS0 tammes18BV8Cert.dR tammes18BV8Cert.S0 tammes18BV8Cert.R_S0 = true := by decide
theorem t18b8_cS1 : isCholeskyDDValid 8 tammes18BV8Cert.dK tammes18BV8Cert.dR tammes18BV8Cert.S1 tammes18BV8Cert.R_S1 = true := by decide

private theorem t18b8_cM0_hdr :
    (decide (0 < tammes18BV8Cert.dM0) &&
     decide (0 < tammes18BV8Cert.dR) &&
     decide (tammes18BV8Cert.R0.length = tammes18BV8Cert.m0) &&
     tammes18BV8Cert.R0.all (fun row => decide (row.length ≤ tammes18BV8Cert.m0)) &&
     isSymmInt tammes18BV8Cert.m0 tammes18BV8Cert.M0 &&
     decide (tammes18BV8Cert.M0.length = tammes18BV8Cert.m0)) = true := by decide
private theorem t18b8_cM0_r0 : choleskyCheckRows 41 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM0 : ℤ) t18b8_RM0 0 t18b8_M0_p0 t18b8_RM0_p0 = true := by decide
private theorem t18b8_cM0_r1 : choleskyCheckRows 41 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM0 : ℤ) t18b8_RM0 10 t18b8_M0_p1 t18b8_RM0_p1 = true := by decide
private theorem t18b8_cM0_r2 : choleskyCheckRows 41 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM0 : ℤ) t18b8_RM0 20 t18b8_M0_p2 t18b8_RM0_p2 = true := by decide
private theorem t18b8_cM0_r3 : choleskyCheckRows 41 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM0 : ℤ) t18b8_RM0 30 t18b8_M0_p3 t18b8_RM0_p3 = true := by decide
private theorem t18b8_cM0_r4 : choleskyCheckRows 41 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM0 : ℤ) t18b8_RM0 40 t18b8_M0_p4 t18b8_RM0_p4 = true := by decide
theorem t18b8_cM0 : isCholeskyDDLower tammes18BV8Cert.m0 tammes18BV8Cert.dM0 tammes18BV8Cert.dR tammes18BV8Cert.M0 tammes18BV8Cert.R0 = true := by
  unfold isCholeskyDDLower
  rw [t18b8_cM0_hdr, Bool.true_and]
  change choleskyCheckRows 41 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM0 : ℤ) t18b8_RM0 0 (t18b8_M0_p0 ++ (t18b8_M0_p1 ++ (t18b8_M0_p2 ++ (t18b8_M0_p3 ++ (t18b8_M0_p4))))) (t18b8_RM0_p0 ++ (t18b8_RM0_p1 ++ (t18b8_RM0_p2 ++ (t18b8_RM0_p3 ++ (t18b8_RM0_p4))))) = true
  refine choleskyCheckRows_append 41 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM0 : ℤ) t18b8_RM0 0 _ _ _ _ rfl t18b8_cM0_r0 ?_
  refine choleskyCheckRows_append 41 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM0 : ℤ) t18b8_RM0 10 _ _ _ _ rfl t18b8_cM0_r1 ?_
  refine choleskyCheckRows_append 41 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM0 : ℤ) t18b8_RM0 20 _ _ _ _ rfl t18b8_cM0_r2 ?_
  refine choleskyCheckRows_append 41 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM0 : ℤ) t18b8_RM0 30 _ _ _ _ rfl t18b8_cM0_r3 ?_
  exact t18b8_cM0_r4

private theorem t18b8_cM1_hdr :
    (decide (0 < tammes18BV8Cert.dM1) &&
     decide (0 < tammes18BV8Cert.dR) &&
     decide (tammes18BV8Cert.R1.length = tammes18BV8Cert.m1) &&
     tammes18BV8Cert.R1.all (fun row => decide (row.length ≤ tammes18BV8Cert.m1)) &&
     isSymmInt tammes18BV8Cert.m1 tammes18BV8Cert.M1 &&
     decide (tammes18BV8Cert.M1.length = tammes18BV8Cert.m1)) = true := by decide
private theorem t18b8_cM1_r0 : choleskyCheckRows 54 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM1 : ℤ) t18b8_RM1 0 t18b8_M1_p0 t18b8_RM1_p0 = true := by decide
private theorem t18b8_cM1_r1 : choleskyCheckRows 54 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM1 : ℤ) t18b8_RM1 10 t18b8_M1_p1 t18b8_RM1_p1 = true := by decide
private theorem t18b8_cM1_r2 : choleskyCheckRows 54 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM1 : ℤ) t18b8_RM1 20 t18b8_M1_p2 t18b8_RM1_p2 = true := by decide
private theorem t18b8_cM1_r3 : choleskyCheckRows 54 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM1 : ℤ) t18b8_RM1 30 t18b8_M1_p3 t18b8_RM1_p3 = true := by decide
private theorem t18b8_cM1_r4 : choleskyCheckRows 54 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM1 : ℤ) t18b8_RM1 40 t18b8_M1_p4 t18b8_RM1_p4 = true := by decide
private theorem t18b8_cM1_r5 : choleskyCheckRows 54 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM1 : ℤ) t18b8_RM1 50 t18b8_M1_p5 t18b8_RM1_p5 = true := by decide
theorem t18b8_cM1 : isCholeskyDDLower tammes18BV8Cert.m1 tammes18BV8Cert.dM1 tammes18BV8Cert.dR tammes18BV8Cert.M1 tammes18BV8Cert.R1 = true := by
  unfold isCholeskyDDLower
  rw [t18b8_cM1_hdr, Bool.true_and]
  change choleskyCheckRows 54 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM1 : ℤ) t18b8_RM1 0 (t18b8_M1_p0 ++ (t18b8_M1_p1 ++ (t18b8_M1_p2 ++ (t18b8_M1_p3 ++ (t18b8_M1_p4 ++ (t18b8_M1_p5)))))) (t18b8_RM1_p0 ++ (t18b8_RM1_p1 ++ (t18b8_RM1_p2 ++ (t18b8_RM1_p3 ++ (t18b8_RM1_p4 ++ (t18b8_RM1_p5)))))) = true
  refine choleskyCheckRows_append 54 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM1 : ℤ) t18b8_RM1 0 _ _ _ _ rfl t18b8_cM1_r0 ?_
  refine choleskyCheckRows_append 54 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM1 : ℤ) t18b8_RM1 10 _ _ _ _ rfl t18b8_cM1_r1 ?_
  refine choleskyCheckRows_append 54 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM1 : ℤ) t18b8_RM1 20 _ _ _ _ rfl t18b8_cM1_r2 ?_
  refine choleskyCheckRows_append 54 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM1 : ℤ) t18b8_RM1 30 _ _ _ _ rfl t18b8_cM1_r3 ?_
  refine choleskyCheckRows_append 54 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM1 : ℤ) t18b8_RM1 40 _ _ _ _ rfl t18b8_cM1_r4 ?_
  exact t18b8_cM1_r5

private theorem t18b8_cM2_hdr :
    (decide (0 < tammes18BV8Cert.dM2) &&
     decide (0 < tammes18BV8Cert.dR) &&
     decide (tammes18BV8Cert.R2.length = tammes18BV8Cert.m2) &&
     tammes18BV8Cert.R2.all (fun row => decide (row.length ≤ tammes18BV8Cert.m2)) &&
     isSymmInt tammes18BV8Cert.m2 tammes18BV8Cert.M2 &&
     decide (tammes18BV8Cert.M2.length = tammes18BV8Cert.m2)) = true := by decide
private theorem t18b8_cM2_r0 : choleskyCheckRows 16 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM2 : ℤ) t18b8_RM2 0 t18b8_M2_p0 t18b8_RM2_p0 = true := by decide
private theorem t18b8_cM2_r1 : choleskyCheckRows 16 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM2 : ℤ) t18b8_RM2 10 t18b8_M2_p1 t18b8_RM2_p1 = true := by decide
theorem t18b8_cM2 : isCholeskyDDLower tammes18BV8Cert.m2 tammes18BV8Cert.dM2 tammes18BV8Cert.dR tammes18BV8Cert.M2 tammes18BV8Cert.R2 = true := by
  unfold isCholeskyDDLower
  rw [t18b8_cM2_hdr, Bool.true_and]
  change choleskyCheckRows 16 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM2 : ℤ) t18b8_RM2 0 (t18b8_M2_p0 ++ (t18b8_M2_p1)) (t18b8_RM2_p0 ++ (t18b8_RM2_p1)) = true
  refine choleskyCheckRows_append 16 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM2 : ℤ) t18b8_RM2 0 _ _ _ _ rfl t18b8_cM2_r0 ?_
  exact t18b8_cM2_r1

private theorem t18b8_cM3_hdr :
    (decide (0 < tammes18BV8Cert.dM3) &&
     decide (0 < tammes18BV8Cert.dR) &&
     decide (tammes18BV8Cert.R3.length = tammes18BV8Cert.m3) &&
     tammes18BV8Cert.R3.all (fun row => decide (row.length ≤ tammes18BV8Cert.m3)) &&
     isSymmInt tammes18BV8Cert.m3 tammes18BV8Cert.M3 &&
     decide (tammes18BV8Cert.M3.length = tammes18BV8Cert.m3)) = true := by decide
private theorem t18b8_cM3_r0 : choleskyCheckRows 23 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM3 : ℤ) t18b8_RM3 0 t18b8_M3_p0 t18b8_RM3_p0 = true := by decide
private theorem t18b8_cM3_r1 : choleskyCheckRows 23 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM3 : ℤ) t18b8_RM3 10 t18b8_M3_p1 t18b8_RM3_p1 = true := by decide
private theorem t18b8_cM3_r2 : choleskyCheckRows 23 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM3 : ℤ) t18b8_RM3 20 t18b8_M3_p2 t18b8_RM3_p2 = true := by decide
theorem t18b8_cM3 : isCholeskyDDLower tammes18BV8Cert.m3 tammes18BV8Cert.dM3 tammes18BV8Cert.dR tammes18BV8Cert.M3 tammes18BV8Cert.R3 = true := by
  unfold isCholeskyDDLower
  rw [t18b8_cM3_hdr, Bool.true_and]
  change choleskyCheckRows 23 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM3 : ℤ) t18b8_RM3 0 (t18b8_M3_p0 ++ (t18b8_M3_p1 ++ (t18b8_M3_p2))) (t18b8_RM3_p0 ++ (t18b8_RM3_p1 ++ (t18b8_RM3_p2))) = true
  refine choleskyCheckRows_append 23 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM3 : ℤ) t18b8_RM3 0 _ _ _ _ rfl t18b8_cM3_r0 ?_
  refine choleskyCheckRows_append 23 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM3 : ℤ) t18b8_RM3 10 _ _ _ _ rfl t18b8_cM3_r1 ?_
  exact t18b8_cM3_r2

private theorem t18b8_cM4_hdr :
    (decide (0 < tammes18BV8Cert.dM4) &&
     decide (0 < tammes18BV8Cert.dR) &&
     decide (tammes18BV8Cert.R4.length = tammes18BV8Cert.m4) &&
     tammes18BV8Cert.R4.all (fun row => decide (row.length ≤ tammes18BV8Cert.m4)) &&
     isSymmInt tammes18BV8Cert.m4 tammes18BV8Cert.M4 &&
     decide (tammes18BV8Cert.M4.length = tammes18BV8Cert.m4)) = true := by decide
private theorem t18b8_cM4_r0 : choleskyCheckRows 27 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM4 : ℤ) t18b8_RM4 0 t18b8_M4_p0 t18b8_RM4_p0 = true := by decide
private theorem t18b8_cM4_r1 : choleskyCheckRows 27 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM4 : ℤ) t18b8_RM4 10 t18b8_M4_p1 t18b8_RM4_p1 = true := by decide
private theorem t18b8_cM4_r2 : choleskyCheckRows 27 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM4 : ℤ) t18b8_RM4 20 t18b8_M4_p2 t18b8_RM4_p2 = true := by decide
theorem t18b8_cM4 : isCholeskyDDLower tammes18BV8Cert.m4 tammes18BV8Cert.dM4 tammes18BV8Cert.dR tammes18BV8Cert.M4 tammes18BV8Cert.R4 = true := by
  unfold isCholeskyDDLower
  rw [t18b8_cM4_hdr, Bool.true_and]
  change choleskyCheckRows 27 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM4 : ℤ) t18b8_RM4 0 (t18b8_M4_p0 ++ (t18b8_M4_p1 ++ (t18b8_M4_p2))) (t18b8_RM4_p0 ++ (t18b8_RM4_p1 ++ (t18b8_RM4_p2))) = true
  refine choleskyCheckRows_append 27 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM4 : ℤ) t18b8_RM4 0 _ _ _ _ rfl t18b8_cM4_r0 ?_
  refine choleskyCheckRows_append 27 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM4 : ℤ) t18b8_RM4 10 _ _ _ _ rfl t18b8_cM4_r1 ?_
  exact t18b8_cM4_r2
theorem t18b8_cM5 : isCholeskyDDLower tammes18BV8Cert.m5 tammes18BV8Cert.dM5 tammes18BV8Cert.dR tammes18BV8Cert.M5 tammes18BV8Cert.R5 = true := by decide

private theorem t18b8_cM6_hdr :
    (decide (0 < tammes18BV8Cert.dM6) &&
     decide (0 < tammes18BV8Cert.dR) &&
     decide (tammes18BV8Cert.R6.length = tammes18BV8Cert.m6) &&
     tammes18BV8Cert.R6.all (fun row => decide (row.length ≤ tammes18BV8Cert.m6)) &&
     isSymmInt tammes18BV8Cert.m6 tammes18BV8Cert.M6 &&
     decide (tammes18BV8Cert.M6.length = tammes18BV8Cert.m6)) = true := by decide
private theorem t18b8_cM6_r0 : choleskyCheckRows 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 0 t18b8_M6_p0 t18b8_RM6_p0 = true := by decide
private theorem t18b8_cM6_r1 : choleskyCheckRows 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 10 t18b8_M6_p1 t18b8_RM6_p1 = true := by decide
private theorem t18b8_cM6_r2 : choleskyCheckRows 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 20 t18b8_M6_p2 t18b8_RM6_p2 = true := by decide
private theorem t18b8_cM6_r3 : choleskyCheckRows 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 30 t18b8_M6_p3 t18b8_RM6_p3 = true := by decide
private theorem t18b8_cM6_r4 : choleskyCheckRows 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 40 t18b8_M6_p4 t18b8_RM6_p4 = true := by decide
private theorem t18b8_cM6_r5 : choleskyCheckRows 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 50 t18b8_M6_p5 t18b8_RM6_p5 = true := by decide
private theorem t18b8_cM6_r6 : choleskyCheckRows 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 60 t18b8_M6_p6 t18b8_RM6_p6 = true := by decide
theorem t18b8_cM6 : isCholeskyDDLower tammes18BV8Cert.m6 tammes18BV8Cert.dM6 tammes18BV8Cert.dR tammes18BV8Cert.M6 tammes18BV8Cert.R6 = true := by
  unfold isCholeskyDDLower
  rw [t18b8_cM6_hdr, Bool.true_and]
  change choleskyCheckRows 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 0 (t18b8_M6_p0 ++ (t18b8_M6_p1 ++ (t18b8_M6_p2 ++ (t18b8_M6_p3 ++ (t18b8_M6_p4 ++ (t18b8_M6_p5 ++ (t18b8_M6_p6))))))) (t18b8_RM6_p0 ++ (t18b8_RM6_p1 ++ (t18b8_RM6_p2 ++ (t18b8_RM6_p3 ++ (t18b8_RM6_p4 ++ (t18b8_RM6_p5 ++ (t18b8_RM6_p6))))))) = true
  refine choleskyCheckRows_append 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 0 _ _ _ _ rfl t18b8_cM6_r0 ?_
  refine choleskyCheckRows_append 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 10 _ _ _ _ rfl t18b8_cM6_r1 ?_
  refine choleskyCheckRows_append 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 20 _ _ _ _ rfl t18b8_cM6_r2 ?_
  refine choleskyCheckRows_append 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 30 _ _ _ _ rfl t18b8_cM6_r3 ?_
  refine choleskyCheckRows_append 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 40 _ _ _ _ rfl t18b8_cM6_r4 ?_
  refine choleskyCheckRows_append 70 ((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ)) (tammes18BV8Cert.dM6 : ℤ) t18b8_RM6 50 _ _ _ _ rfl t18b8_cM6_r5 ?_
  exact t18b8_cM6_r6

end Geodesy.Spherical
