{-|
  Tests for "Unicode.Codec.ValidatedUtf8" — mirrors the @*_validates@
  and @*_rejected@ theorems from @Unicode/Codec/ValidatedUtf8.lean@,
  plus the @unwrap_bytes@ roundtrip lemma.
-}
module ValidatedUtf8Spec (tests) where

import Data.Maybe (isJust, isNothing)
import qualified Data.ByteString as BS
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import Unicode.Codec.ValidatedUtf8 (unwrap, validateUtf8)

tests :: TestTree
tests = testGroup "Unicode.Codec.ValidatedUtf8"
  [ positives
  , negatives
  , roundtrip
  ]

positives :: TestTree
positives = testGroup "validate accepts"
  [ testCase "empty validates" $
      assertEqual "" True (isJust (validateUtf8 BS.empty))
  , testCase "hello validates" $
      assertEqual "" True $
        isJust (validateUtf8 (BS.pack [0x68, 0x65, 0x6C, 0x6C, 0x6F]))
  , testCase "héllo validates" $
      assertEqual "" True $
        isJust (validateUtf8 (BS.pack [0x68, 0xC3, 0xA9, 0x6C, 0x6C, 0x6F]))
  , testCase "日本 validates" $
      assertEqual "" True $
        isJust (validateUtf8 (BS.pack [0xE6, 0x97, 0xA5, 0xE6, 0x9C, 0xAC]))
  ]

negatives :: TestTree
negatives = testGroup "validate rejects"
  [ testCase "bare continuation (80) rejected" $
      assertEqual "" True (isNothing (validateUtf8 (BS.pack [0x80])))
  , testCase "overlong (C0 80) rejected" $
      assertEqual "" True (isNothing (validateUtf8 (BS.pack [0xC0, 0x80])))
  , testCase "surrogate (ED A0 80) rejected" $
      assertEqual "" True $
        isNothing (validateUtf8 (BS.pack [0xED, 0xA0, 0x80]))
  ]

roundtrip :: TestTree
roundtrip = testGroup "unwrap"
  [ testCase "unwrap of validated bytes recovers original" $
      let bs = BS.pack [0x68, 0x65, 0x6C, 0x6C, 0x6F]
      in case validateUtf8 bs of
           Just v  -> assertEqual "" bs (unwrap v)
           Nothing -> assertEqual "validateUtf8 should accept hello" True False
  ]
