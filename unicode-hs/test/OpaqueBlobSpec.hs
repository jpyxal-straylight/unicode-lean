{-# LANGUAGE TypeApplications #-}
{-|
  Tests for "Unicode.Codec.OpaqueBlob" — mirrors the @*_is_blob@,
  @*_not_blob@, and @Utf8Blob.ofBytes?_self@ theorems from
  @Unicode/Codec/OpaqueBlob.lean@.

  The size bound is type-level; tests use 'TypeApplications' to fix the
  bound at each call site, matching the Lean's @Utf8Blob (maxBytes :
  Nat)@ shape.
-}
module OpaqueBlobSpec (tests) where

import Data.Maybe (isJust, isNothing)
import qualified Data.ByteString as BS
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import Unicode.Codec.OpaqueBlob
  ( isUtf8Blob
  , utf8BlobBytes
  , utf8BlobMaxBytes
  , utf8BlobOfBytes
  )

tests :: TestTree
tests = testGroup "Unicode.Codec.OpaqueBlob"
  [ predicate
  , construction
  , sizeBoundEnforcement
  , roundtrip
  ]

predicate :: TestTree
predicate = testGroup "isUtf8Blob"
  [ testCase "empty is a blob" $
      assertEqual "" True (isUtf8Blob BS.empty)
  , testCase "hello is a blob" $
      assertEqual "" True $
        isUtf8Blob (BS.pack [0x68, 0x65, 0x6C, 0x6C, 0x6F])
  , testCase "héllo is a blob" $
      assertEqual "" True $
        isUtf8Blob (BS.pack [0x68, 0xC3, 0xA9, 0x6C, 0x6C, 0x6F])
  , testCase "日本 is a blob" $
      assertEqual "" True $
        isUtf8Blob (BS.pack [0xE6, 0x97, 0xA5, 0xE6, 0x9C, 0xAC])
  , testCase "bidi override (E2 80 AE) IS a blob (predicate accepts)" $
      assertEqual "" True (isUtf8Blob (BS.pack [0xE2, 0x80, 0xAE]))
  , testCase "invalid start byte (80) is not a blob" $
      assertEqual "" False (isUtf8Blob (BS.pack [0x80]))
  ]

construction :: TestTree
construction = testGroup "utf8BlobOfBytes"
  [ testCase "valid bytes within bound succeed" $
      assertEqual "" True $
        isJust (utf8BlobOfBytes @32 (BS.pack [0x68, 0x65, 0x6C, 0x6C, 0x6F]))
  , testCase "invalid UTF-8 rejected" $
      assertEqual "" True $
        isNothing (utf8BlobOfBytes @32 (BS.pack [0x80]))
  ]

sizeBoundEnforcement :: TestTree
sizeBoundEnforcement = testGroup "size bound"
  [ testCase "bytes over the size bound rejected" $
      assertEqual "" True $
        isNothing (utf8BlobOfBytes @2 (BS.pack [0x68, 0x65, 0x6C]))
  , testCase "bytes exactly at the size bound accepted" $
      assertEqual "" True $
        isJust (utf8BlobOfBytes @3 (BS.pack [0x68, 0x65, 0x6C]))
  ]

roundtrip :: TestTree
roundtrip = testGroup "field accessors"
  [ testCase "utf8BlobBytes recovers original bytes" $
      let bs = BS.pack [0x68, 0x65, 0x6C, 0x6C, 0x6F]
      in case utf8BlobOfBytes @16 bs of
           Just blob -> assertEqual "" bs (utf8BlobBytes blob)
           Nothing   -> assertEqual "should have accepted" True False
  , testCase "utf8BlobMaxBytes reflects type-level bound" $
      case utf8BlobOfBytes @16 (BS.pack [0x68]) of
        Just blob -> assertEqual "" 16 (utf8BlobMaxBytes blob)
        Nothing   -> assertEqual "should have accepted" True False
  ]
