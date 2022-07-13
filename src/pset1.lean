import algebra.divisibility
import algebra.ring
import data.real.basic
import algebra.order.ring
import tactic.linarith

def divides (a : ℤ) (b : ℤ) := exists c : ℤ, a * c = b

theorem s1p4 (a : ℤ) : divides a a :=
begin 
  rw divides,
  use 1,
  ring,
end 

theorem s1p5 (a b c : ℤ) (h : divides a b) : divides a (b*c) :=
begin
  rw divides,
  cases h with x,
  have H : c*x*a=b*c,
  { rw mul_assoc, rw mul_comm x a, rw h_h, ring },
  use (x*c),
  ring_nf,
  exact H
end

theorem s1p6 (k a b : ℤ) (ha : divides k a) (hb : divides k b) : divides k (a+b) :=
begin
  rw divides,
  cases ha with x,
  cases hb with y,
  use (x+y),
  rw left_distrib,
  rw ha_h, 
  rw hb_h,
end