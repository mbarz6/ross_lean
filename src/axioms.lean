import algebra.ring
import data.real.basic
import algebra.order.ring
import tactic.linarith

theorem division_by_2 (a : ℕ) : (exists b : ℕ, a=2*b) ∨ (∃ b : ℕ, a=2*b+1) :=
begin
  induction a with d hd,
  left,
  use 0,
  ring,
  cases hd with hEven hOdd,
  cases hEven with b,
  right,
  use b,
  exact congr_arg nat.succ hEven_h,
  left,
  cases hOdd with b,
  use (b+1),
  rw nat.succ_eq_add_one,
  rw hOdd_h,
  ring,
end