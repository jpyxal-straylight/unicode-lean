{-# LANGUAGE TypeApplications #-}
{-|
  Tests for "Unicode.Codec.Identifier" — mirrors the @isStart_*@,
  @isContinue_*@, @*_is_identifier@, and @*_not@ theorems from
  @Unicode/Codec/Identifier.lean@. The 'IdentifierUtf8' refinement uses
  a type-level size bound, mirroring the Lean structure parameter.
-}
module IdentifierSpec (tests) where

import Data.Maybe (isJust, isNothing)
import qualified Data.ByteString as BS
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import Unicode.Codec.Identifier
  ( identifierUtf8Bytes
  , identifierUtf8OfBytes
  , isIdentifierContinueByte
  , isIdentifierStartByte
  , isValidIdentifierBytes
  )

tests :: TestTree
tests = testGroup "Unicode.Codec.Identifier"
  [ byteClassStart
  , byteClassContinue
  , aggregate
  , refinement
  ]

byteClassStart :: TestTree
byteClassStart = testGroup "isIdentifierStartByte"
  [ testCase "A (0x41) is a start byte" $
      assertEqual "" True (isIdentifierStartByte 0x41)
  , testCase "z (0x7A) is a start byte" $
      assertEqual "" True (isIdentifierStartByte 0x7A)
  , testCase "_ (0x5F) is a start byte" $
      assertEqual "" True (isIdentifierStartByte 0x5F)
  , testCase "9 (0x39) is NOT a start byte" $
      assertEqual "" False (isIdentifierStartByte 0x39)
  , testCase "SPACE (0x20) is NOT a start byte" $
      assertEqual "" False (isIdentifierStartByte 0x20)
  ]

byteClassContinue :: TestTree
byteClassContinue = testGroup "isIdentifierContinueByte"
  [ testCase "9 (0x39) IS a continue byte" $
      assertEqual "" True (isIdentifierContinueByte 0x39)
  , testCase "SPACE (0x20) is NOT a continue byte" $
      assertEqual "" False (isIdentifierContinueByte 0x20)
  ]

aggregate :: TestTree
aggregate = testGroup "isValidIdentifierBytes"
  [ testCase "hello is an identifier" $
      assertEqual "" True $
        isValidIdentifierBytes (BS.pack [0x68, 0x65, 0x6C, 0x6C, 0x6F])
  , testCase "var_1 is an identifier" $
      assertEqual "" True $
        isValidIdentifierBytes (BS.pack [0x76, 0x61, 0x72, 0x5F, 0x31])
  , testCase "_ (underscore alone) is an identifier" $
      assertEqual "" True $
        isValidIdentifierBytes (BS.pack [0x5F])
  , testCase "empty is NOT an identifier" $
      assertEqual "" False (isValidIdentifierBytes BS.empty)
  , testCase "1var (leading digit) is NOT an identifier" $
      assertEqual "" False $
        isValidIdentifierBytes (BS.pack [0x31, 0x76, 0x61, 0x72])
  , testCase "\"a b\" (embedded space) is NOT an identifier" $
      assertEqual "" False $
        isValidIdentifierBytes (BS.pack [0x61, 0x20, 0x62])
  , testCase "high-bit byte after A is NOT an identifier" $
      assertEqual "" False $
        isValidIdentifierBytes (BS.pack [0x41, 0xFF])
  ]

refinement :: TestTree
refinement = testGroup "IdentifierUtf8 refinement"
  [ testCase "valid identifier within bound succeeds" $
      assertEqual "" True $
        isJust (identifierUtf8OfBytes @16 (BS.pack [0x68, 0x65, 0x6C, 0x6C, 0x6F]))
  , testCase "invalid identifier rejected" $
      assertEqual "" True $
        isNothing (identifierUtf8OfBytes @16 (BS.pack [0x31, 0x76]))
  , testCase "size bound enforced" $
      assertEqual "" True $
        isNothing (identifierUtf8OfBytes @2 (BS.pack [0x68, 0x65, 0x6C]))
  , testCase "identifierUtf8Bytes recovers original bytes" $
      let bs = BS.pack [0x68, 0x65, 0x6C, 0x6C, 0x6F]
      in case identifierUtf8OfBytes @16 bs of
           Just ident -> assertEqual "" bs (identifierUtf8Bytes ident)
           Nothing    -> assertEqual "should have accepted" True False
  ]
