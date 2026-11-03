import Mathlib




variable {n m : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
  (l : m → FreeAddGroup n)

def relatorMatrix : Matrix n m ℤ :=
  .of fun i j ↦ FreeAddGroup.lift (fun k ↦ (Pi.single k 1 : n → ℤ)) (l j) i

#check Group.IsPerfect
#print Group.IsPerfect
#check QuotientGroup.subgroup_eq_top_of_subsingleton
