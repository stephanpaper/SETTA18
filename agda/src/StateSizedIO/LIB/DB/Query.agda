
module StateSizedIO.LIB.DB.Query where

open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Bool
open import Data.String renaming (_++_ to _+++_) hiding (show)
open import Data.List hiding (lookup)
open import Data.Vec hiding (lookup; _++_)
open import Function
open import Data.Integer renaming (show to showℤ)

import StateSizedIO.LIB.DB.Dictionary

open import StateSizedIO.LIB.DB.Schema
--open import Universe
open StateSizedIO.LIB.DB.Dictionary {String} _==_
open import StateSizedIO.LIB.DB.DBUniverse



data ExprType : Set where
  bool  : ExprType
  ftype : FieldType -> ExprType

-- Exercise: add more interesting expressions.
-- For instance, less than or greater than comparisons. Look at the SQL documentation for ideas.



-- Expressions are
--   ! fieldname       fieldname is a string for a field in a table
--   val v             v is value for a field
--   s == t            equality between two expressions
-- If a table has for instance field  "name" of type string
-- expressions could be
-- ! "name" == "Tom"
-- standing for the expression   name = "Tom"


data Expr (t : TableType) : ExprType -> Set where
  _===_ : forall {a} -> Expr t a -> Expr t a -> Expr t bool
  !_    : forall x {p : HasKey x t} -> Expr t (ftype (fst (lookup x t {p})))
  val   : forall {a} -> Field a -> Expr t (ftype a)

-- Exercise: add more interesting queries. For instance,
-- 1. Make it possible to rename fields to allow combining tables with overlapping column names.
-- 2. SQL supports counting and ordering results. Add this to our queries.


-- Queries are
--  read "tablename"
--       corresponding  to select tablename
--  p ⊗ p'    which is an outer join of two queries
--  select t q     ist
--                query q where t
--  proj as q
--    is where you select one field in a query
--
data Query (s : Schema) : TableType -> Set where
  read   : (x : TableName){p : HasKey x s} -> Query s (lookup x s {p})
  _⊗_    : forall {t t'}{p : Disjoint t t'} ->
           Query s t -> Query s t' -> Query s (t ++ t')
  proj   : forall {t} xs {p : HasKeys xs t} ->
           Query s t -> Query s (project xs t {p})
  select : forall {t} -> Expr t bool -> Query s t -> Query s t

-- This might have to be changed when you add more interesting queries.

data SQL : Set where
  SELECT_FROM_WHERE_ : List FieldName -> List TableName -> List String -> SQL


-- sepBy takes a list of strings, concatenates them but putting in between
--   the first argument.
sepBy : String -> List String -> String
sepBy _ [] = ""
sepBy _ (x ∷ []) = x
sepBy i (x ∷ xs) = x +++ i +++ sepBy i xs

showField : forall {a} -> Field a -> String
showField {string} s = "'" +++ s +++ "'" --listToString (vecToList s) +++ "'"  -- TODO: escaping
showField {integer} n = showℤ n


-- New row type without names [later perhaps NamedRows with the n
--

{-
showRow : forall {t} -> Row t -> String
showRow []        = ""
showRow (_∷_ {name = name} x []) = name +++ " = " +++ showField x
showRow (_∷_ {name = name} x xs) = name +++ " = " +++ showField x +++ ", " +++ showRow xs
-}

showExpr : forall {t a} -> Expr t a -> String
showExpr (e₁ === e₂) = showExpr e₁ +++ " = " +++ showExpr e₂
showExpr (! x) = x
showExpr (val c) = showField c

showSQL : SQL -> String
-- no where clause if that part is missing (pattern match):
showSQL (SELECT as FROM ts WHERE []) =
  "SELECT " +++ sepBy ", " as +++ " FROM " +++ sepBy ", " ts
showSQL (SELECT as FROM ts WHERE cs) =
  "SELECT " +++ sepBy ", " as +++ " FROM " +++ sepBy ", " ts +++
  " WHERE " +++ sepBy " AND " cs

toSQL : forall {s t} -> Query s t -> SQL
toSQL {s} (read x {p}) = SELECT (Data.List.map fst (lookup x s {p})) FROM x ∷ [] WHERE []
toSQL (q₁ ⊗ q₂) with toSQL q₁ | toSQL q₂
... | SELECT as₁ FROM ts₁ WHERE cs₁
    | SELECT as₂ FROM ts₂ WHERE cs₂ = SELECT (as₁ ++ as₂) FROM (nub (ts₁ ++ ts₂)) WHERE (cs₁ ++ cs₂)
toSQL (proj as q) with toSQL q
... | SELECT _ FROM ts WHERE cs = SELECT as FROM ts WHERE cs
toSQL (select c q) with toSQL q
... | SELECT as FROM ts WHERE cs = SELECT as FROM ts WHERE (showExpr c ∷ cs)
