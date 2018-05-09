
open import Data.Bool

module StateSizedIO.LIB.DB.Dictionary {Key : Set}(_==_ : Key -> Key -> Bool) where

open import Data.Product
open import Data.Bool

open import Data.List using (List; _∷_; _++_; [])

Dict : Set -> Set
Dict A = List (Key × A)

hasKey : {A : Set} -> Key -> Dict A -> Bool
hasKey _ [] = false
hasKey y ((x , _) ∷ xs) = x == y ∨ hasKey y xs

-- this is now named T, right?
{-
IsTrue : Bool -> Set
IsTrue true  = True
IsTrue false = False
-}

HasKey : {A : Set} -> Key -> Dict A -> Set
HasKey x xs = T (hasKey x xs)

lookup : {A : Set}(x : Key)(xs : Dict A){p : HasKey x xs} -> A
lookup _ [] {}
lookup y ((x , v) ∷ xs) {p} with x == y
... | true  = v
... | false = lookup y xs {p}

hasKeys : {A : Set} -> List Key -> Dict A -> Bool
hasKeys []        _ = true
hasKeys (x ∷ xs) t = hasKey x t ∧ hasKeys xs t

HasKeys : {A : Set} -> List Key -> Dict A -> Set
HasKeys xs t = T (hasKeys xs t)

andElimL : forall {a b} -> T (a ∧ b) -> T a
andElimL {true} _ = _
andElimL {false} ()


andElimR : forall a {b} -> T (a ∧ b) -> T b
andElimR true p = p
andElimR false ()

project : {A : Set}(xs : List Key)(tbl : Dict A){p : HasKeys xs tbl} ->
          Dict A
project []        tbl     = []
project (x ∷ xs) tbl {p} = (x , lookup x tbl {andElimL p}) ∷
                            project xs tbl {andElimR (hasKey x tbl) p}

distinctKeys : {A : Set} -> Dict A -> Bool
distinctKeys []              = true
distinctKeys ((x , _) ∷ xs) = not (hasKey x xs) ∧ distinctKeys xs

disjoint : {A : Set} -> Dict A -> Dict A -> Bool
disjoint xs ys = distinctKeys (xs ++ ys)

Disjoint : {A : Set} -> Dict A -> Dict A -> Set
Disjoint xs ys = T (disjoint xs ys)
