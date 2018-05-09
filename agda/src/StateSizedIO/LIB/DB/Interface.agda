



module StateSizedIO.LIB.DB.Interface where

open import Data.String.Base  hiding (show)
open import Data.List renaming (_++_ to _++List_)
open import Data.List.Categorical
open import Data.Nat
open import Data.Nat.Show
open import Data.Fin

open import StateSizedIO.LIB.HDBC.HDBC
open import StateSizedIO.LIB.DB.Schema

open import StateSizedIO.LIB.DB.Serialization


open import StateSizedIO.LIB.library

open import NativeIO renaming (NativeIO to IO; nativeReturn to return; _native>>=_ to _>>=_)


insertRows : Connection →
             (schema : Schema) →
             (table : Fin (nrTables schema)) →
             List (Row (tableFields schema table)) →
             IO Unit

insertRows conn schema table xs =
  nativePrepare conn (insertCommand schema table) >>= λ statement →

  mapM ioMonad (λ x → nativeExecute statement (row2SqlVal x)) xs >>= λ x →
  nativeCommit conn >>= λ _ →
  return _
