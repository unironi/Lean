/-  Let I ⊂ k[x1, . . . , xn] be an ideal that can be generated by r elements.
Show that every irreducible component of V (I) has dimension ≥ n − r.

-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Algebraic
import Mathlib.Algebra.BigOperators.Group.Finset


namespace Mv_Polynomial

variable {k : Type*} [CommSemiring k] {σ :Type*} {s: σ → ℕ}

/- The algebraic set of a set of polynomials S ⊆ k[x₁, ... xₙ] is the set
of elements x ∈ kⁿ such that x is a root of all the polynomials in S -/
def ZeroOf (S: Set (MvPolynomial σ k)) : Set (σ → k) := {x : (σ → k) | ∀ f ∈ S, (MvPolynomial.eval x) f = 0}

/- The ideal of a set X ⊆ kⁿ is the set of all polynomials in k[x₁, ... xₙ] that are zero on every element in X-/
def IdealOf (X: Set (σ → k)) : Set (MvPolynomial σ k) := {f: MvPolynomial σ k | ∀ x ∈ X, (MvPolynomial.eval x) f = 0}

/- Here the underlying set is a subset of kⁿ -/
structure AlgebraicSet (k: Type*) [CommSemiring k] (σ : Type*) where
  -- (carrier: ZeroOf S)
  (carrier: Set (σ → k))
  (ideal_exists: ∃ S : Set (MvPolynomial σ k), carrier = ZeroOf S)

/- Underlying set is a subset of k[x₁, ... xₙ] -/
structure IdealOfAlgebraicSet (k: Type*) [CommSemiring k] (σ : Type*) where
  (carrier: Set (MvPolynomial σ k))
  (algebraic_exists: ∃ X : Set (σ → k), carrier = IdealOf X)

/- A variety is an irreducible algebraic set -/
def Irreducible (X: Set (σ → k)) (U₁ U₂: Set (σ → k)) := X ≠ ∅ ∧ X ≠ U₁ ∧ X ≠ U₂ ∧ X ≠ U₁ ∪ U₂

/- Every variety V has a dimension which is the transcendence degree of the function
field k(V) over k; here I am just defining it as a number ≥ 0 -/
structure Variety (k: Type*) [CommSemiring k] (σ : Type*) where
  (carrier: Set (σ → k))
  (is_variety: ∀ U₁ U₂ : Set (σ → k), Irreducible carrier U₁ U₂)
  (ideal_exists: ∃ S : Set (MvPolynomial σ k), carrier = ZeroOf S)
  (dimension : ℕ)

variable (V: Variety k σ) (SetOfVarieties: Set (Set (σ → k))) -- lean does not like Set (Variety k σ)

def AlgebraicSets : Set (σ → k) := Set.sUnion SetOfVarieties

-- Want to express an algebraic set as a union of varieties
-- but also be able to say something like ∀ varieties ∈ algebraic set

/- A reducible algebraic set consists of a union of varieties -/
   -- Y₁ and Y₂ could be further reducible

--def Reducible (X: AlgebraicSet k σ) := ∃ Y₁ Y₂: AlgebraicSet k σ, Y₁.carrier ≠ X.carrier ∧ Y₂.carrier ≠ X.carrier ∧ X.carrier = Y₁.carrier ∪ Y₂.carrier

--def SetsOfReducible (X: AlgebraicSet k σ) := X.carrier = Set (Variety k σ)

/- If Y is a subvariety of X, then the codimension of Y in X is dim X - dim Y -/
-- def Codim (X: Variety A) (Y: Variety A) (Y_sub_X: Y.carrier ⊆ X.carrier) := X.dimension - Y.dimension

--variable (A : AlgebraicSet (SetOfVarieties)) (S: Set (MvPolynomial σ k)) (VS: ZeroOf S)


/- Next two theorems are to help prove the main problem -/

/-
Theorem 2.5.3:
If Y is a proper subvariety of X ⊆ Am then dim Y < dim X.
Proof:
Let n = dim X.
Then any n+1 of the coordinate functions x1, . . . , xm are algebraically dependent as elements of k(X), and also as elements of k(Y ).
Therefore dimY ≤dimX.
Assume that dim Y = dim X .
We will derive the contradiction Y = X by showing that I(Y) ⊆ I(X).
Since dimY = n there are coordinate functions xi1,...,xin whose images are algebraically independent in k(Y). Then xi1 , . . . , xin must be algebraically independent in k(X).
Let u ∈ Γ(X) be non- zero.
Then u depends algebraically on xi1 , . . . , xin , i.e. there is a polynomial a ∈ k[t1,...,tn+1] such that
a(u,xi1,...,xin)=ak(xi1,...,xin)uk +···+a1(xi1,...,xin)u+a0(xi1,...,xin)=0 on X.
Since Γ(X) is a domain we may assume a is irreducible and a0(xi1 , . . . , xin ) is non-zero on X.
Then a(u,xi1,...,xin)=0 on Y since Y ⊆ X so if u=0 on Y then a0(xi1,...,xin) = 0 on Y, a contradiction since xi1,...,xin are algebraically independent in k(Y ).
Since u ≠ 0 on X implies u  ≠ 0 on Y we have that I(Y ) ⊆ I(X).
-/

theorem ProperSubVarietyDim (X Y: Variety k σ) (properSub: Y.carrier ⊂ X.carrier) : Y.dimension < X.dimension := by
  let n := X.dimension
  sorry

/-
Let f ∈ k[x1, . . . , xn] be a non-constant irreducible polynomial. Then V(f) ⊆ 𝔸ⁿ has codimension 1.

Proof:
Let X = V(f).
Suppose that xₙ appears in the expression of f.
Then x1, . . . , xn-1 are algebraically independent in k(X).
Indeed, if they are not then there is a polynomial g involving only the variables x1,...,xn−1 that is zero on X.
Then g ∈ I(X) = ⟨f⟩, so f | g and xn appears in the expression for g, a contradiction.
Therefore dim X ≥ n − 1, and Theorem 2.5.3 implies that dim X = n − 1, so codim X = 1.
-/

theorem IrredCodim1 (f: MvPolynomial σ k) (Vf: Variety k σ) (kn: Variety k σ) (h: Vf.carrier ⊆ kn.carrier): kn.dimension - Vf.dimension = 1 := by
  sorry

/-
Let I ⊂ k[x1, . . . , xn] be an ideal that can be generated by r elements.
Show that every irreducible component of V (I) has dimension ≥ n − r.
-/

/- Solution:

  induction on r using d:
  if d = 1:
  then I = ⟨a₁⟩ ⊆ k[x₁, ..., xₙ]
  so V(I) = V(a₁) = V(f₁) ∩ ... ∩ V(fₘ) where fᵢ is an irreducible factor of a₁
  since k is a UFD, each V(fᵢ) is irreducible and has a codimension of 1 in 𝔸ⁿ
  hence dim V(fᵢ) ≥ n - 1 (from equation codimₖ(V(fᵢ)) = dim k - dim V(fᵢ)

  if d = r - 1
  Let V(I) = V(a1, ... ar-1) = ∪ Wᵢ where Wᵢ is irreducible and dim Wᵢ ≥ n - r + 1
  X = V(a1, ... ar) = V(a1, ... ar-1) ∩ V(ar) = ∪ Wᵢ ∩ V(aᵣ)
  X is the union of irreducible decompositions of ∪ Wᵢ ∩ V(aᵣ)
  We show every irreducible component W of Wᵢ ∩ V(aᵣ) has dim W ≥ n - r

  If polynomial aᵣ = 0:
  then all of 𝔸ⁿ is its algebraic set, so Wᵢ ∩ V(aᵣ) = Wᵢ
  Since Wᵢ is irreducible, W = Wᵢ
  so dim W ≥ n - r + 1 ≥ n - r

  If aᵣ ≠ 0 in coordinate ring of Wᵢ:
  Every irreducible component of Wᵢ ∩ V(aᵣ) has codimension 1 in Wᵢ
  So dim W = dim (Wᵢ) - 1 ≥ n - r + 1 - 1 = n - r

  -/

-- Using the induction tactic will not work in this case since induction sets the base case to zero,
-- so we will split up the theorem into two, one considering r = 1 and the other assuming the inductive step

-- I is an ideal of polynomial ring
-- V(I) is the algebraic
-- to reference the irreducible component of an algebraic set
--variable (t : Type*) [t = {1}]

variable (SS: Set (Set (σ → k)))

theorem rIsOne (I: Set (MvPolynomial Unit k)) (V: AlgebraicSets SS) (W: Variety k σ) (h: W ⊆ V) : W.dimension ≥ n - 1 := by
sorry

-- want this to be true for any variety of I, so i need something that can split V(I) into irreducible components
-- and we can just take one of those components to prove in generality
theorem IrredDim (I: Set (MvPolynomial r k)) (V: AlgebraicSets SS) (W: Variety k σ) (h: W ⊆ V):
W.dimension ≥ n - r := by
sorry

--theorem ugh (I: Set (MvPolynomial σ k))
