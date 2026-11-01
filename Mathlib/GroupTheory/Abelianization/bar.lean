import Mathlib

-- TODO We should add `to_additive` to `PresentedGroup` so that
-- we obtain `PresentedAddGroup` and can avoid `Additive` below.
/-!-/
noncomputable section

section MoreGeneral

-- @[to_additive]  -- (to_additive gives an error for now; to be investigated.)
structure AddGroup.FinitePresentation {G α : Type*}
    [Finite α] [AddGroup G] where
  π : FreeAddGroup α →+ G
  rels : Set (FreeAddGroup α)
  surj : Function.Surjective π
  rels_finite : rels.Finite
  π_ker : π.ker = AddSubgroup.normalClosure rels

variable {n m : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
  (l : m → FreeAddGroup n)

-- Null hypothesis: use this instead of `Group.FinitePresentation` above
-- Fewer ways to spell the same thing means less API to write + maintain
#check PresentedAddGroup (Set.range l : Set (FreeAddGroup n))

def relatorMatrix : Matrix n m ℤ :=
  .of fun i j ↦ FreeAddGroup.lift (fun k ↦ (Pi.single k 1 : n → ℤ)) (l j) i

-- test cases
def x : FreeAddGroup (Fin 2) := FreeAddGroup.of 0
def y : FreeAddGroup (Fin 2) := FreeAddGroup.of 1
def testRelations : Fin 2 → FreeAddGroup (Fin 2)
  | 0 => 3 • x + (-2 : ℤ) • y
  | 1 => x + y - x - y
#eval relatorMatrix testRelations
-- Expected Output: !![3, 0; -2, 0]

open QuotientGroup

def key' :
    AddAbelianization (PresentedAddGroup (Set.range l : Set (FreeAddGroup n))) ≃+
      (n → ℤ) ⧸ (relatorMatrix l).toLin'.range := by
  let F := FreeAddGroup n
  let R : Set F := Set.range l

  --  map from `F` to `Multiplicative ℤ^n ⧸ relatorMatrix` that descends to our required map
  let freeToCoker : F →+ (n → ℤ) ⧸ (relatorMatrix l).toLin'.range.toAddSubgroup :=
    FreeAddGroup.lift fun i ↦ Submodule.Quotient.mk (Pi.single i 1)

  -- Prove relators map to identity for the descent.
  have h_rels (r : F) (hr : r ∈ R) : freeToCoker r = 0 := by
    rcases hr with ⟨j, rfl⟩
    unfold freeToCoker
    sorry

  -- Forward additive map
  let presentationToCoker : AddAbelianization (PresentedAddGroup R) →+
      (n → ℤ) ⧸ (relatorMatrix l).toLin'.range.toAddSubgroup :=
    (AddAbelianization.lift (PresentedAddGroup.toAddGroup h_rels))

  -- ℤ-linear map from ℤ^n ⧸ `relatorMatrix` to the abelianized presentation
  let φ : (n → ℤ) →ₗ[ℤ] AddAbelianization (PresentedAddGroup R) :=
    Fintype.linearCombination ℤ fun i ↦ AddAbelianization.of (PresentedAddGroup.of i)

  have h_range : (relatorMatrix l).toLin'.range ≤ φ.ker := by
    sorry

  -- Backward linear map
  let CokertoPresentationLin : (n → ℤ) ⧸ (relatorMatrix l).toLin'.range →ₗ[ℤ]
      AddAbelianization (PresentedAddGroup R) :=
    (relatorMatrix l).toLin'.range.liftQ φ h_range

  let linEquiv : AddAbelianization (PresentedAddGroup R) ≃ₗ[ℤ]
      (n → ℤ) ⧸ (relatorMatrix l).toLin'.range :=
    LinearEquiv.ofLinearMap
      presentationToCoker.toIntLinearMap
      CokertoPresentationLin
      (by
        sorry)
      (by
        sorry)

  exact linEquiv.toAddEquiv

end MoreGeneral

section ToAdditiveExamples


#check Group
#check AddGroup

example {G : Type*} [Group G] (x y : G) : (x * y)⁻¹ = y⁻¹ * x⁻¹ := sorry
example {G : Type*} [AddGroup G] (x y : G) : -(x + y) = -y + -x := sorry

example {G : Type*} [AddGroup G] : G ≃+ ℤ := sorry
example {G : Type*} [Group G] : Additive G ≃+ ℤ := sorry

variable {G : Type*} [Group G]

#synth Mul G
#synth Add (Additive G)

#check FreeAddGroup

end ToAdditiveExamples

variable {m n : Type*} [Fintype n] (v : m → n → ℤ)

def rel (i : m) : FreeGroup n :=
  ((Finset.univ : Finset n).toList.map fun j ↦ FreeGroup.of j ^ v i j).prod

def key :
    Additive (Abelianization (PresentedGroup <| Set.range <| rel v)) ≃+
      (n → ℤ) ⧸ (Submodule.span ℤ (Set.range v)) :=
  sorry -- Claude can fill this in ~25 lines.

-- The Abelianization of the group with presentation `⟨a, b | a⁴b⁶, a⁶b⁸⟩` has order 4
-- (in fact it is `(ℤ / 2ℤ) × (ℤ / 2ℤ)`)
example :
    letI A : Matrix _ _ ℤ := !![4, 6; 6, 8]
    Nat.card (Abelianization (PresentedGroup <| Set.range <| rel A)) = 4 := by
  sorry -- TODO prove in one line using new tactic.

-- The group with presentation `⟨a, b | a³ = b⁵ = (ab)²⟩` is perfect
-- (in fact it is the binary icosahedral group of order 120).
example :
    letI A : Matrix _ _ ℤ := !![1, -2; -2, 3]
    Group.IsPerfect (PresentedGroup <| Set.range <| rel A) := by
  sorry -- TODO prove in one line using new tactic.
