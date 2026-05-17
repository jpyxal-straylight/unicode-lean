{-|
  Tests for "Unicode.Codec.Utf8" — mirrors the closed-form theorems in
  @Unicode/Codec/Utf8.lean@ + @Unicode/Codec/Utf8Roundtrip.lean@.

  Three groups:

  1. Concrete unit tests — one per @theorem step_*@ and @*_rejected@
     in the Lean source. Same inputs, same expected outputs.

  2. Per-byte-class QuickCheck — mirrors @decode_encode_2byte_fin@,
     @decode_encode_3byte_fin@, @decode_encode_4byte_plane_*@ via
     bounded random sampling.

  3. Exhaustive roundtrip — every valid scalar codepoint
     (0..0x10FFFF excluding the surrogate block) encodes-then-decodes
     to itself. Haskell counterpart of the Lean
     @decode_encode_codepoint@ theorem.
-}
module Utf8Spec (tests) where

import Data.Bits ((.&.))
import qualified Data.ByteString as BS
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)
import Test.Tasty.QuickCheck (testProperty, withMaxSuccess)
import Test.QuickCheck (Gen, choose, forAll, suchThat)

import Unicode.Codec.Strict
  ( Utf8RejectKind
      ( CodepointBeyondMax
      , InvalidContinuationByte
      , InvalidStartByte
      , OverlongEncoding
      , SurrogateCodepoint
      , TruncatedSequence
      )
  )
import Unicode.Codec.Utf8
  ( Utf8State (ExpectCont, ExpectStart)
  , Utf8StepResult (Continue, Emit, Reject)
  , decodeToCodepoints
  , encodeCodepoint
  , firstInvalidUtf8Offset
  , isValidUtf8
  , utf8DecodeStep
  )

tests :: TestTree
tests = testGroup "Unicode.Codec.Utf8"
  [ concreteStepTests
  , concreteValidationTests
  , concreteDecodeTests
  , quickCheckRoundtrips
  , exhaustiveRoundtrip
  ]

concreteStepTests :: TestTree
concreteStepTests = testGroup "decoder step"
  [ testCase "step_ascii_A" $
      assertEqual ""
        (Emit 0x41 ExpectStart)
        (utf8DecodeStep ExpectStart 0x41)
  , testCase "step_ascii_nul" $
      assertEqual ""
        (Emit 0x00 ExpectStart)
        (utf8DecodeStep ExpectStart 0x00)
  , testCase "step_invalid_start_80" $
      assertEqual "" (Reject InvalidStartByte) (utf8DecodeStep ExpectStart 0x80)
  , testCase "step_invalid_start_C0" $
      assertEqual "" (Reject InvalidStartByte) (utf8DecodeStep ExpectStart 0xC0)
  , testCase "step_invalid_start_C1" $
      assertEqual "" (Reject InvalidStartByte) (utf8DecodeStep ExpectStart 0xC1)
  , testCase "step_invalid_start_F5" $
      assertEqual "" (Reject InvalidStartByte) (utf8DecodeStep ExpectStart 0xF5)
  , testCase "step_invalid_start_FF" $
      assertEqual "" (Reject InvalidStartByte) (utf8DecodeStep ExpectStart 0xFF)
  , testCase "step_2byte_start_C3" $
      assertEqual ""
        (Continue (ExpectCont 1 (0xC3 .&. 0x1F) 0x80))
        (utf8DecodeStep ExpectStart 0xC3)
  , testCase "step_3byte_start_E2" $
      assertEqual ""
        (Continue (ExpectCont 2 (0xE2 .&. 0x0F) 0x800))
        (utf8DecodeStep ExpectStart 0xE2)
  , testCase "step_4byte_start_F0" $
      assertEqual ""
        (Continue (ExpectCont 3 (0xF0 .&. 0x07) 0x10000))
        (utf8DecodeStep ExpectStart 0xF0)
  , testCase "step_cont_with_ascii_rejects" $
      assertEqual ""
        (Reject InvalidContinuationByte)
        (utf8DecodeStep (ExpectCont 1 0x03 0x80) 0x41)
  ]

concreteValidationTests :: TestTree
concreteValidationTests = testGroup "validation"
  [ testCase "empty_is_valid" $
      assertEqual "" True (isValidUtf8 BS.empty)
  , testCase "hello_is_valid" $
      assertEqual "" True (isValidUtf8 (BS.pack [0x68, 0x65, 0x6C, 0x6C, 0x6F]))
  , testCase "ascii_digits_valid" $
      assertEqual "" True $
        isValidUtf8 (BS.pack [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39])
  , testCase "accented_is_valid (héllo)" $
      assertEqual "" True $
        isValidUtf8 (BS.pack [0x68, 0xC3, 0xA9, 0x6C, 0x6C, 0x6F])
  , testCase "cjk_is_valid (日本)" $
      assertEqual "" True $
        isValidUtf8 (BS.pack [0xE6, 0x97, 0xA5, 0xE6, 0x9C, 0xAC])
  , testCase "bare_continuation_rejected" $
      assertEqual ""
        (Just (0, InvalidStartByte))
        (firstInvalidUtf8Offset (BS.pack [0x80]))
  , testCase "overlong_2byte_NUL_rejected (C0 80)" $
      assertEqual ""
        (Just (0, InvalidStartByte))
        (firstInvalidUtf8Offset (BS.pack [0xC0, 0x80]))
  , testCase "overlong_3byte_rejected (E0 80 80)" $
      assertEqual ""
        (Just (0, OverlongEncoding))
        (firstInvalidUtf8Offset (BS.pack [0xE0, 0x80, 0x80]))
  , testCase "truncated_3byte_rejected (E2 80)" $
      assertEqual ""
        (Just (2, TruncatedSequence))
        (firstInvalidUtf8Offset (BS.pack [0xE2, 0x80]))
  , testCase "surrogate_rejected (ED A0 80)" $
      assertEqual ""
        (Just (2, SurrogateCodepoint))
        (firstInvalidUtf8Offset (BS.pack [0xED, 0xA0, 0x80]))
  , testCase "beyond_max_rejected (F4 90 80 80)" $
      assertEqual ""
        (Just (3, CodepointBeyondMax))
        (firstInvalidUtf8Offset (BS.pack [0xF4, 0x90, 0x80, 0x80]))
  ]

concreteDecodeTests :: TestTree
concreteDecodeTests = testGroup "decode"
  [ testCase "hello decodes to [h,e,l,l,o]" $
      assertEqual ""
        [0x68, 0x65, 0x6C, 0x6C, 0x6F]
        (decodeToCodepoints (BS.pack [0x68, 0x65, 0x6C, 0x6C, 0x6F]))
  , testCase "empty decodes to []" $
      assertEqual "" [] (decodeToCodepoints BS.empty)
  , testCase "héllo decodes correctly" $
      assertEqual ""
        [0x68, 0xE9, 0x6C, 0x6C, 0x6F]
        (decodeToCodepoints (BS.pack [0x68, 0xC3, 0xA9, 0x6C, 0x6C, 0x6F]))
  , testCase "U+202E bidi override survives roundtrip" $
      assertEqual ""
        [0x61, 0x202E, 0x62]
        (decodeToCodepoints (BS.pack [0x61, 0xE2, 0x80, 0xAE, 0x62]))
  ]

quickCheckRoundtrips :: TestTree
quickCheckRoundtrips = testGroup "QuickCheck per-byte-class"
  [ testProperty "1-byte (ASCII)" $ withMaxSuccess 1000 $
      forAll genAscii prop_roundtrip
  , testProperty "2-byte" $ withMaxSuccess 1000 $
      forAll gen2Byte prop_roundtrip
  , testProperty "3-byte BMP non-surrogate" $ withMaxSuccess 2000 $
      forAll gen3ByteBmp prop_roundtrip
  , testProperty "4-byte supplementary" $ withMaxSuccess 5000 $
      forAll gen4Byte prop_roundtrip
  ]
  where
    genAscii :: Gen Int
    genAscii = choose (0x00, 0x7F)
    gen2Byte :: Gen Int
    gen2Byte = choose (0x80, 0x7FF)
    gen3ByteBmp :: Gen Int
    gen3ByteBmp = choose (0x800, 0xFFFF) `suchThat` (\cp -> not (cp >= 0xD800 && cp <= 0xDFFF))
    gen4Byte :: Gen Int
    gen4Byte = choose (0x10000, 0x10FFFF)
    prop_roundtrip :: Int -> Bool
    prop_roundtrip cp = decodeToCodepoints (encodeCodepoint cp) == [cp]

exhaustiveRoundtrip :: TestTree
exhaustiveRoundtrip = testGroup "exhaustive"
  [ testCase "every valid scalar codepoint roundtrips" $ do
      let bad = [ cp
                | cp <- [0 .. 0x10FFFF]
                , not (cp >= 0xD800 && cp <= 0xDFFF)
                , decodeToCodepoints (encodeCodepoint cp) /= [cp]
                ]
      assertEqual "codepoints that failed to roundtrip" [] bad
  ]
