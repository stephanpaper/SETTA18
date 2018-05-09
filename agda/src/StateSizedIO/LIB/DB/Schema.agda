module StateSizedIO.LIB.DB.Schema where

open import Data.Bool
open import Data.String renaming (_++_ to _+++_) hiding (length)
open import Data.Nat
open import Data.List
open import Data.Product hiding (map)
open import Data.Vec hiding (map)
open import Data.Integer
open import Data.Unit
open import Data.Fin

open import StateSizedIO.LIB.HDBC.HDBC

open import Relation.Nullary.Decidable hiding (map)


open import StateSizedIO.LIB.library



-- Type
--
data FieldType : Set where
  string  : FieldType
  integer : FieldType


_==Type_ : FieldType → FieldType → Bool
string ==Type string = true
integer ==Type integer = true
_ ==Type _ = false


-- Definition
--
TableName = String
FieldName = String

isNull = Bool
isPrimaryKey = Bool

Attribute = FieldName × FieldType × isNull × isPrimaryKey

TableType = List Attribute
Schema    = List (TableName × TableType)




-- Access
--
nrTables : (schema : List (TableName × TableType)) → ℕ
nrTables = length

nrColumns : (schema : List (TableName × TableType))
            (tableNr : Fin (nrTables schema)) → ℕ
nrColumns schema tableNr = length (proj₂ (nth schema tableNr))

colName : (schema  : Schema)
          (tableNr : Fin (nrTables schema))
          (colNr   : Fin (nrColumns schema tableNr))
          → String
colName schema tableNr colNr = proj₁ (nth (proj₂ (nth schema tableNr)) colNr)

colType : (schema  : Schema)
          (tableNr : Fin (nrTables schema))
          (colNr   : Fin (nrColumns schema tableNr))
          → FieldType
colType schema tableNr colNr = proj₁ (proj₂ (nth (proj₂ (nth schema tableNr)) colNr))



tableName : (schema  : Schema)
            (tableNr : Fin (nrTables schema))
            → String
tableName schema tableNr = proj₁ (nth schema tableNr)

tableType : (schema  : Schema)
            (tableNr : Fin (nrTables schema))
            → TableType
tableType schema tableNr = proj₂ (nth schema tableNr)

tableFields : (schema  : Schema)
            (tableNr : Fin (nrTables schema))
            → List FieldType
tableFields schema tableNr = map (λ x → proj₁ (proj₂ x)) (proj₂ (nth schema tableNr))




ForeignKeys : (schema : Schema)
              (let nrtables = (nrTables schema))
              (let nrcolumns = (nrColumns schema))

              (mytable : Fin nrtables)
             → Set
ForeignKeys schema mytable =
  let nrtables = (nrTables schema)
      nrcolumns = (nrColumns schema)
      columnType = colType schema
  in List (Σ[ mycol ∈ Fin (nrcolumns mytable) ] (
                    (Σ[ k ∈ Fin nrtables ] (
                         Σ[ j ∈ Fin (nrcolumns k) ] (T

                             (columnType mytable mycol ==Type columnType k j))))))


SchemaWithForeignKeys : Set
SchemaWithForeignKeys = (Σ[ schema ∈ Schema ]
                          List
                           (Σ[ mytable ∈ Fin (nrTables schema)] ForeignKeys schema mytable))



-- Row definition
--
Field : FieldType → Set
Field string = String
Field integer = ℤ


Row : List FieldType → Set
Row [] = ⊤
Row (l ∷ t) = Field l × Row t

{-

exampleFunction : (l : List FieldType) → (r : Row l) →  ℕ
exampleFunction [] r = {!!}
exampleFunction (x ∷ l) (proj₃ , proj₄) = {!!}

-}


tableRowType : (schema  : Schema)
            (tableNr : Fin (nrTables schema))
            → Set
tableRowType schema tableNr = Row (tableFields schema tableNr)


row2SqlVal : ∀ {fields} → Row fields → List SqlVal
row2SqlVal {[]} tt = []
row2SqlVal {string ∷ fields} (str , xs) = sqlString str ∷ row2SqlVal xs
row2SqlVal {integer ∷ fields} (int , xs) = sqlInteger int ∷ row2SqlVal xs


--
-- Type Aliases
--
notNull : Bool
notNull = false

isPrimKey : Bool
isPrimKey = true

notPrimKey : Bool
notPrimKey = false
