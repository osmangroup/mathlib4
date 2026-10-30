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
  .of fun i j ↦ by
    -- We want the "total power" (i.e., sum) of `i` in `l.get j`
    let w := l j
    -- Map the ith generator to 1 and all others to 0, then use the universal property!
    let f : n →  ℤ :=
      fun k => if k = i then 1 else  0
    let totalPowerHom := FreeAddGroup.lift f
    exact Multiplicative.toAdd (totalPowerHom w)


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
    Abelianization (PresentedAddGroup (Set.range l : Set (FreeAddGroup n)))) ≃+
      (n → ℤ) ⧸ (relatorMatrix l).toLin'.range.toAddSubgroup := by
  let F := FreeAddGroup n
  let R : Set F := Set.range l

  --  map from `F` to `Multiplicative ℤ^n ⧸ relatorMatrix` that descends to our required map
  let freeToCoker : F →* Multiplicative ((n → ℤ) ⧸ (relatorMatrix l).toLin'.range.toAddSubgroup) :=
    FreeGroup.lift fun i ↦ Multiplicative.ofAdd (Submodule.Quotient.mk (Pi.single i 1))

  -- Prove relators map to identity for the descent.
  have h_relators (r : F) (hr : r ∈ R) : freeToCoker r = 1 := by
    rcases hr with ⟨j, rfl⟩
    unfold freeToCoker
    apply_fun Multiplicative.toAdd
    dsimp
    sorry

  -- Forward additive map
  let presentationToCoker : Additive (Abelianization (PresentedGroup R)) →+
      (n → ℤ) ⧸ (relatorMatrix l).toLin'.range.toAddSubgroup :=
    (Abelianization.lift (PresentedGroup.toGroup h_relators)).toAdditive

  -- ℤ-linear map from ℤ^n ⧸ `relatorMatrix` to the abelianized presentation
  let φ : (n → ℤ) →ₗ[ℤ] Additive (Abelianization (PresentedGroup R)) :=
    Fintype.linearCombination ℤ fun i ↦ Additive.ofMul (Abelianization.of (PresentedGroup.of i))

  have h_range : (relatorMatrix l).toLin'.range ≤ φ.ker := by
    sorry

  -- Backward linear map
  let CokertoPresentationLin : (n → ℤ) ⧸ (relatorMatrix l).toLin'.range →ₗ[ℤ]
      Additive (Abelianization (PresentedGroup R)) :=
    (relatorMatrix l).toLin'.range.liftQ φ h_range

  let linEquiv : Additive (Abelianization (PresentedGroup R)) ≃ₗ[ℤ]
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
