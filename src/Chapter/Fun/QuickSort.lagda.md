---
---

```agda
open import Library.Nat
open import Library.Nat.Properties
open import Library.Equality
open import Library.List
open import Library.List.Properties
open import Library.List.Permutation
open import Library.LessThan
open import Library.LessThan.Reasoning
open import Library.LessThan.Alternative
open import Library.Logic
open import Library.WellFounded

module Chapter.Fun.QuickSort
  (A : Set)
  (_≼_ : A -> A -> Set)
  (≼-trans : {x y z : A} -> x ≼ y -> y ≼ z -> x ≼ z)
  (≼-total : (x y : A) -> x ≼ y ∨ y ≼ x)
  where

open import Library.List.Sorted A _≼_

partition :
  (x : A) (xs : List A) -> ∃[ ys ] ∃[ zs ] xs # ys ++ zs ∧ All (_≼ x) ys ∧ All (x ≼_) zs
partition x [] = [] , [] , #refl , <> , <>
partition x (u :: xs) with ≼-total x u | partition x xs
... | inl x≼u | ys , zs , π , py , pz =
  ys , u :: zs , #trans (#cong π) #push , py , x≼u , pz
... | inr u≼x | ys , zs , π , py , pz =
  u :: ys , zs , #cong π , (u≼x , py) , pz

sorted-++ : {z : A} {xs ys : List A} -> Sorted xs -> All (_≼ z) xs -> All (z ≼_) ys -> Sorted ys -> Sorted (xs ++ z :: ys)
sorted-++ {xs = []} p xs≼z z≼ys q = z≼ys , q
sorted-++ {z} {xs = x :: xs} (x≼xs , p) (x≼z , xs≼z) z≼ys q =
  all-++ (x ≼_) x≼xs (x≼z , implies-all (≼-trans x≼z) z≼ys) ,
  sorted-++ p xs≼z z≼ys q

{-# TERMINATING #-}
quick-sort-nt : (xs : List A) -> ∃[ ys ] xs # ys ∧ Sorted ys
quick-sort-nt [] = [] , #refl , <>
quick-sort-nt (x :: xs) with partition x xs
... | ys , zs , π , py , pz with quick-sort-nt ys | quick-sort-nt zs
... | ys' , πy , sys | zs' , πz , szs =
  let π' = #begin
             x :: xs         #⟨ #cong π ⟩
             x :: ys ++ zs   #⟨ #cong (#cong++l πy) ⟩
             x :: ys' ++ zs  #⟨ #cong (#cong++r πz) ⟩
             x :: ys' ++ zs' #⟨ #push ⟩
             ys' ++ x :: zs'
           #end in
  ys' ++ x :: zs' , π' ,
  sorted-++ sys (#all (_≼ x) πy py) (#all (x ≼_) πz pz) szs

data _⊏_ {A : Set} : List A → List A → Set where
  lt[] : ∀{x xs} → [] ⊏ (x :: xs)
  lt:: : ∀{x y xs ys} → xs ⊏ ys → (x :: xs) ⊏ (y :: ys)

accessible⊏ : ∀{A : Set} (xs ys : List A) → ys ⊏ xs → Accessible _⊏_ ys
accessible⊏ xs ys lt[]     = acc λ _ ()
accessible⊏ xs ys (lt:: p) = accessible⊏ {!!} {!!} {!p!}

accessible<' : (x y : ℕ) -> y <' x -> Accessible _<'_ y
accessible<' (succ y) _ le-refl'      = acc (accessible<' y)
accessible<' (succ y) z (le-succ' lt) = accessible<' y z lt

-- well-founded-lt' : WellFounded _<'_
-- well-founded-lt' x = acc (accessible<' x)

-- infix 4 _⊑_ _⊏_

-- _⊑_ : List A -> List A -> Set
-- xs ⊑ ys = length xs <= length ys

-- _⊏_ : List A -> List A -> Set
-- xs ⊏ ys = length xs < length ys

-- well-founded-⊏ : WellFounded _⊏_
-- well-founded-⊏ = well-founded-m _⊏_ _<'_ length <=to<=' well-founded-lt'

-- lemma-#-⊑ : {xs ys : List A} -> xs # ys -> ys ⊑ xs
-- lemma-#-⊑ π = subst (_<= length _) (#length π) le-refl

-- lemma-++-⊑-l : (xs ys : List A) -> xs ⊑ xs ++ ys
-- lemma-++-⊑-l xs ys =
--   begin
--     length xs <=⟨ le-plus (length xs) (length ys) ⟩
--     length xs + length ys ==⟨ symm (++-length xs ys) ⟩
--     length (xs ++ ys)
--   end

-- lemma-++-⊑-r : (xs ys : List A) -> ys ⊑ xs ++ ys
-- lemma-++-⊑-r xs ys =
--   begin
--     length ys <=⟨ le-plus (length ys) (length xs) ⟩
--     length ys + length xs ==⟨ +-comm (length ys) (length xs) ⟩
--     length xs + length ys ==⟨ symm (++-length xs ys) ⟩
--     length (xs ++ ys)
--   end

-- lemma-⊑ : (xs ys zs : List A) -> xs # ys ++ zs -> ys ⊑ xs ∧ zs ⊑ xs
-- lemma-⊑ xs ys zs π = le-trans (lemma-++-⊑-l ys zs) (lemma-#-⊑ π) ,
--                      le-trans (lemma-++-⊑-r ys zs) (lemma-#-⊑ π)

-- -- lemma-⊑ xs ys zs π =
-- --   begin
-- --     length ys             <=⟨ le-plus (length ys) (length zs) ⟩
-- --     length ys + length zs ==⟨ symm (++-length ys zs) ⟩
-- --     length (ys ++ zs)     ==⟨ symm (#length π) ⟩
-- --     length xs
-- --   end

-- quick-sort-acc : (xs : List A) -> Accessible _⊏_ xs -> ∃[ ys ] xs # ys ∧ Sorted ys
-- quick-sort-acc [] _ = [] , #refl , <>
-- quick-sort-acc (x :: xs) (acc f) with partition x xs
-- ... | ys , zs , π , py , pz with lemma-⊑ xs ys zs π
-- ... | ys⊑xs , zs⊑xs with quick-sort-acc ys (f ys (le-succ ys⊑xs)) |
--                          quick-sort-acc zs (f zs (le-succ zs⊑xs))
-- ... | ys' , πy , sys | zs' , πz , szs =
--   let π' = #begin
--              x :: xs         #⟨ #cong π ⟩
--              x :: ys ++ zs   #⟨ #cong (#cong++l πy) ⟩
--              x :: ys' ++ zs  #⟨ #cong (#cong++r πz) ⟩
--              x :: ys' ++ zs' #⟨ #push ⟩
--              ys' ++ x :: zs'
--            #end in
--   ys' ++ x :: zs' , π' , sorted-++ sys (#all (_≼ x) πy py) (#all (x ≼_) πz pz) szs

-- quick-sort : (xs : List A) -> ∃[ ys ] xs # ys ∧ Sorted ys
-- quick-sort xs = quick-sort-acc xs (well-founded-⊏ xs)
-- ```
