import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

def le_sub_one_of_lt (h : n < m) : n ≤ m - 1 := by
  induction h with
  | refl => simp_arith
  | step h ih => {
    simp_arith
    exact Nat.le_trans ih (by simp_arith)
  }

def mwe (a b c : Fin 256) : a.val * 2^16 + b.val * 2^8 + c.val ≤ 2^24 := by 
  have h1 : b.val * 2^8 ≤ (2^8-1)*2^8 := 
    Nat.mul_le_mul_of_nonneg_right (le_sub_one_of_lt b.isLt)
  
  
  have h2 : a.val * 2^16 ≤ (2^8-1)*2^16 := 
    Nat.mul_le_mul_of_nonneg_right (le_sub_one_of_lt a.isLt)
  
  have rhs : 2^24 = (2^8-1)*2^16 + (2^8-1)*2^8 + 2^8 := by simp_arith
  simp [ UInt8.toNat, rhs, Nat.add_assoc]
  set_option maxRecDepth 4096 in 
  exact Nat.add_le_add (Nat.add_le_add h2 h1) (c.isLt)