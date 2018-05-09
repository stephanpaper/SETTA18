module StateSizedIO.LIB.DB.Serialization where

open import Data.Bool
open import Data.String renaming (_++_ to _+++_)
open import Data.Nat
open import Data.List
open import Data.Product hiding (map)
open import Data.Vec hiding (map)
open import Data.Integer
open import Data.Unit
open import Data.Fin

open import Relation.Nullary.Decidable hiding (map)


open import StateSizedIO.LIB.library
open import StateSizedIO.LIB.DB.Schema


rowToQuestionsmarks : TableType → String
rowToQuestionsmarks xs = concatIntersperse "," (map (λ _ → "?") xs)

insertCommand : (schema : Schema)(tableNr : Fin (nrTables schema)) → String
insertCommand schema tblNr = "INSERT INTO "
                            +++ tableName schema tblNr +++
                            " VALUES (" +++ rowToQuestionsmarks (tableType schema tblNr) +++ ")"



printForeignKeys : (schema : Schema)
                  (let nrtables = (nrTables schema))
                  (mytable : Fin nrtables)
                  (keys : ForeignKeys schema mytable)
                  → String
printForeignKeys schema mytable [] = ""
printForeignKeys schema mytable ((nrCol , (foreignTable , nrForeignColumn , _)) ∷ keys) =
  "FOREIGN KEY(" +++ columnName +++ ") REFERENCES " +++
  foreighTableName +++ " ( " +++ foreignColumnName +++ " )," +++ "\n" +++ printForeignKeys schema mytable keys
  where
    columnName : String
    columnName = colName schema mytable nrCol
    --
    foreignColumnName : String
    foreignColumnName = colName schema foreignTable nrForeignColumn
    --
    foreighTableName : String
    foreighTableName = tableName schema foreignTable
