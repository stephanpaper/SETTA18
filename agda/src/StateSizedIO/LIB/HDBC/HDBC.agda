module StateSizedIO.LIB.HDBC.HDBC where

open import Data.Bool.Base
open import Data.Integer
open import Data.Nat.Base hiding (_+_)
open import Data.String.Base renaming (_++_ to _++Str_)

open import Data.Product renaming (map to mapProduct)
open import Data.Integer
open import Data.List

open import Function

open import StateSizedIO.LIB.library

open import NativeIO renaming (NativeIO to IO; nativeReturn to return; _native>>=_ to _>>=_)


--
-- TODO: implement lazy row retrevial as Toni suggested
-- (Return a type for the lazy list and operations to get the next row)
--
--

--
-- TODO: once we use only our IO (not NativeIO)
--       we must use consistently "naitveFunctionName" here (i.e., it is mixed/sometimes omitted)
--

{-# FOREIGN GHC import qualified Database.HDBC.Sqlite3 #-}
{-# FOREIGN GHC import qualified Database.HDBC #-}
{-# FOREIGN GHC import qualified Control.Monad #-}
{-# FOREIGN GHC import qualified Database.HDBC.SqlValue #-}


{-# FOREIGN GHC import qualified Data.ByteString #-}
{-# FOREIGN GHC import qualified Data.Int #-}
{-# FOREIGN GHC import qualified Data.ByteString.Char8 #-}
{-# FOREIGN GHC import qualified Data.Text #-}


-- check later if we need safer conversion functions
--

{-# FOREIGN GHC
  data SqlValueShort = SqlStringShort Data.Text.Text
                     | SqlIntShort Integer
                     | SqlNullShort
                     | SqlUndefinedShort


  toSqlValueShort :: Database.HDBC.SqlValue -> SqlValueShort
  toSqlValueShort (Database.HDBC.SqlByteString s) = SqlStringShort $ Data.Text.pack $ Data.ByteString.Char8.unpack  s
  toSqlValueShort (Database.HDBC.SqlInt64 x) = SqlIntShort $ fromIntegral x
  toSqlValueShort Database.HDBC.SqlNull = SqlNullShort
  toSqlValueShort _ = SqlUndefinedShort

  -- throws an exception (Non-exhaustive patterns) for the value SqlUndefinedShort!
  --
  toSqlValue :: SqlValueShort -> Database.HDBC.SqlValue
  toSqlValue (SqlStringShort str) =  Database.HDBC.SqlValue.SqlString (Data.Text.unpack str)
  toSqlValue (SqlIntShort x) =  Database.HDBC.SqlValue.SqlInt64 (fromIntegral x)
  toSqlValue SqlNullShort = Database.HDBC.SqlValue.SqlNull
  toSqlValue SqlUndefinedShort = error "ERROR!!! toSqlValue function with SqlUndefinedShort, can't convert it."

#-}

data SqlVal : Set where
  sqlString    : String → SqlVal
  sqlInteger   : ℤ → SqlVal
  sqlNull      : SqlVal
  sqlUndefined : SqlVal

{-# COMPILE GHC SqlVal = data SqlValueShort (SqlStringShort | SqlIntShort | SqlNullShort | SqlUndefinedShort) #-}


postulate SqlValue : Set
{-# COMPILE GHC SqlValue = type Database.HDBC.SqlValue.SqlValue #-}

postulate toSqlVal : SqlValue → SqlVal
{-# COMPILE GHC toSqlVal = toSqlValueShort #-}

postulate  toSqlValue : SqlVal → SqlValue
{-# COMPILE GHC toSqlValue = toSqlValue #-}

toStringSqlVal : SqlVal → String
toStringSqlVal (sqlString s)   = s
toStringSqlVal (sqlInteger x)  = Data.Integer.show x
toStringSqlVal sqlNull         = "SqlValNull"
toStringSqlVal sqlUndefined    = "SqlValUndefined"

toTypeNameSqlVal : SqlVal → String
toTypeNameSqlVal (sqlString _)   = "[String]"
toTypeNameSqlVal (sqlInteger _)  = "[Integer]"
toTypeNameSqlVal sqlNull         = "SqlValNull"
toTypeNameSqlVal sqlUndefined    = "SqlValUndefined"


toStringListSqlVal : List SqlVal → String
toStringListSqlVal (x ∷ xs) = toStringSqlVal x ++Str "\n" ++Str toStringListSqlVal xs
toStringListSqlVal [] = ""



-- Types
--
postulate Connection : Set
{-# COMPILE GHC Connection = type Database.HDBC.Sqlite3.Connection #-}


postulate Statement : Set
{-# COMPILE GHC Statement = type Database.HDBC.Statement #-}

postulate PairStringSqlValue : Set
{-# COMPILE GHC PairStringSqlValue = type (String, Database.HDBC.SqlValue.SqlValue) #-}


-- trivial helpers
--
postulate fstString : PairStringSqlValue → String
{-# COMPILE GHC fstString = (\(a , b) -> Data.Text.pack a) #-}

postulate sndSqlValue : PairStringSqlValue → SqlValue
{-# COMPILE GHC sndSqlValue = (\(a , b) -> b) #-}

convertPair : PairStringSqlValue → String × SqlValue
convertPair x = fstString x , sndSqlValue x

-- connect to Sqlite database
--
postulate nativeConnectDB : String → IO Connection
{-# COMPILE GHC nativeConnectDB = (\tableName -> Database.HDBC.Sqlite3.connectSqlite3 (Data.Text.unpack tableName)) #-}


--
-- HDBC interface
--

postulate nativeDisconnect : Connection → IO Unit
{-# COMPILE GHC nativeDisconnect = Database.HDBC.disconnect #-}

postulate nativeCommit : Connection → IO Unit
{-# COMPILE GHC nativeCommit = Database.HDBC.commit #-}

postulate nativeRollback : Connection → IO Unit
{-# COMPILE GHC nativeRollback = Database.HDBC.rollback #-}


-- returns the number of modified rows
--
postulate nativeRunSqlValue : Connection → String → List SqlValue → IO ℤ
{-# COMPILE GHC nativeRunSqlValue = (\conn str values -> Database.HDBC.run conn (Data.Text.unpack str) values) #-}

nativeRunSqlValueAgda : Connection → String → List SqlVal → IO ℤ
nativeRunSqlValueAgda conn str values = nativeRunSqlValue conn str (map toSqlValue values)

postulate nativePrepare : Connection → String → IO Statement
{-# COMPILE GHC nativePrepare = (\conn str -> Database.HDBC.prepare conn (Data.Text.unpack str)) #-}



postulate nativeExecuteSqlValue : Statement → List SqlValue → IO ℤ
{-# COMPILE GHC nativeExecuteSqlValue = Database.HDBC.execute #-}

nativeExecute : Statement → List SqlVal → IO ℤ
nativeExecute statement list = nativeExecuteSqlValue statement (map toSqlValue list)



postulate runSqlValue : Connection → String → List SqlValue → IO ℤ
{-# COMPILE GHC runSqlValue = (\conn str list -> Database.HDBC.run conn (Data.Text.unpack str) list) #-}


nativeRun : Connection → String → List SqlVal → IO ℤ
nativeRun conn str list = runSqlValue conn str (map toSqlValue list)


postulate getTables : Connection → IO (List String)
{-# COMPILE GHC getTables = (\conn -> (Database.HDBC.getTables conn) >>= (\x -> return $ map Data.Text.pack x) ) #-}


postulate fetchAllRowsALStrictSqlValue : Statement → IO (List (List PairStringSqlValue))
{-# COMPILE GHC fetchAllRowsALStrictSqlValue = (\statement -> (Database.HDBC.fetchAllRowsAL' statement)) #-}

nativeFetchAllRowsAL' : Statement → IO (List (List (String × SqlVal)))
nativeFetchAllRowsAL' statement = fetchAllRowsALStrictSqlValue statement >>= λ list →
                            return (map (map (λ y → mapProduct (λ x → x) toSqlVal (convertPair y))) list)

nativePrintList : List (List (String × SqlVal)) → String
nativePrintList l = unlines (map concat' listListString)
  where
    concat' = foldr (λ x y → x ++Str ", " ++Str y) ""
    toStr : String × SqlVal → String
    toStr (str , val) = "(" ++Str str ++Str ", " ++Str toStringSqlVal val ++Str " " ++Str toTypeNameSqlVal val ++Str ")"
    listListString = map (map toStr) l



dropTableIfExisits : Connection → (tableName : String) →  IO Unit
dropTableIfExisits conn tableName = nativeRun conn ("DROP TABLE IF EXISTS " ++Str tableName) [] >>= λ _ → return _
