{-|
  Tests for "Unicode.Codec.Utf16" — mirrors the closed-form theorems in
  @Unicode/Codec/Utf16.lean@.
-}
module Utf16Spec (tests) where

import qualified Data.ByteString as BS
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import Unicode.Codec.Utf16 (decodeOneBE, decodeOneLE, encodeOneBE, encodeOneLE)

tests :: TestTree
tests = testGroup "Unicode.Codec.Utf16"
  [ illFormed
  , exhaustiveRoundtripBE
  , exhaustiveRoundtripLE
  ]

illFormed :: TestTree
illFormed = testGroup "ill-formed rejection"
  [ testCase "decodeOneBE_lone_high_surrogate (D8 00)" $
      assertEqual "" Nothing (decodeOneBE (BS.pack [0xD8, 0x00]))
  , testCase "decodeOneBE_lone_low_surrogate (DC 00)" $
      assertEqual "" Nothing (decodeOneBE (BS.pack [0xDC, 0x00]))
  , testCase "decodeOneBE_high_then_not_low (D8 00 00 41)" $
      assertEqual "" Nothing (decodeOneBE (BS.pack [0xD8, 0x00, 0x00, 0x41]))
  , testCase "decodeOneBE_length_3 rejected" $
      assertEqual "" Nothing (decodeOneBE (BS.pack [0x00, 0x00, 0x00]))
  , testCase "decodeOneBE_length_5 rejected" $
      assertEqual "" Nothing (decodeOneBE (BS.pack [0x00, 0x00, 0x00, 0x00, 0x00]))
  , testCase "decodeOneLE_lone_high_surrogate (00 D8)" $
      assertEqual "" Nothing (decodeOneLE (BS.pack [0x00, 0xD8]))
  , testCase "decodeOneLE_lone_low_surrogate (00 DC)" $
      assertEqual "" Nothing (decodeOneLE (BS.pack [0x00, 0xDC]))
  ]

exhaustiveRoundtripBE :: TestTree
exhaustiveRoundtripBE = testGroup "exhaustive BE"
  [ testCase "every valid scalar codepoint roundtrips through UTF-16 BE" $ do
      let bad = [ cp
                | cp <- [0 .. 0x10FFFF]
                , not (cp >= 0xD800 && cp <= 0xDFFF)
                , decodeOneBE (encodeOneBE cp) /= Just cp
                ]
      assertEqual "codepoints that failed to roundtrip (BE)" [] bad
  ]

exhaustiveRoundtripLE :: TestTree
exhaustiveRoundtripLE = testGroup "exhaustive LE"
  [ testCase "every valid scalar codepoint roundtrips through UTF-16 LE" $ do
      let bad = [ cp
                | cp <- [0 .. 0x10FFFF]
                , not (cp >= 0xD800 && cp <= 0xDFFF)
                , decodeOneLE (encodeOneLE cp) /= Just cp
                ]
      assertEqual "codepoints that failed to roundtrip (LE)" [] bad
  ]
