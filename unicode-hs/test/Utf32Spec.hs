{-|
  Tests for "Unicode.Codec.Utf32" — mirrors the closed-form theorems in
  @Unicode/Codec/Utf32.lean@.
-}
module Utf32Spec (tests) where

import qualified Data.ByteString as BS
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import Unicode.Codec.Utf32 (decodeOneBE, decodeOneLE, encodeOneBE, encodeOneLE)

tests :: TestTree
tests = testGroup "Unicode.Codec.Utf32"
  [ illFormed
  , exhaustiveRoundtripBE
  , exhaustiveRoundtripLE
  ]

illFormed :: TestTree
illFormed = testGroup "ill-formed rejection"
  [ testCase "decodeOneBE_surrogate_rejected (encode 0xD800)" $
      assertEqual "" Nothing (decodeOneBE (encodeOneBE 0xD800))
  , testCase "decodeOneBE_beyondMax_rejected (encode 0x110000)" $
      assertEqual "" Nothing (decodeOneBE (encodeOneBE 0x110000))
  , testCase "decodeOneLE_surrogate_rejected (encode 0xD800)" $
      assertEqual "" Nothing (decodeOneLE (encodeOneLE 0xD800))
  , testCase "decodeOneLE_beyondMax_rejected (encode 0x110000)" $
      assertEqual "" Nothing (decodeOneLE (encodeOneLE 0x110000))
  , testCase "decodeOneBE_too_short" $
      assertEqual "" Nothing (decodeOneBE (BS.pack [0x00, 0x00, 0x00]))
  , testCase "decodeOneBE_too_long" $
      assertEqual "" Nothing
        (decodeOneBE (BS.pack [0x00, 0x00, 0x00, 0x41, 0x00]))
  ]

exhaustiveRoundtripBE :: TestTree
exhaustiveRoundtripBE = testGroup "exhaustive BE"
  [ testCase "every valid scalar codepoint roundtrips through UTF-32 BE" $ do
      let bad = [ cp
                | cp <- [0 .. 0x10FFFF]
                , not (cp >= 0xD800 && cp <= 0xDFFF)
                , decodeOneBE (encodeOneBE cp) /= Just cp
                ]
      assertEqual "codepoints that failed to roundtrip (BE)" [] bad
  ]

exhaustiveRoundtripLE :: TestTree
exhaustiveRoundtripLE = testGroup "exhaustive LE"
  [ testCase "every valid scalar codepoint roundtrips through UTF-32 LE" $ do
      let bad = [ cp
                | cp <- [0 .. 0x10FFFF]
                , not (cp >= 0xD800 && cp <= 0xDFFF)
                , decodeOneLE (encodeOneLE cp) /= Just cp
                ]
      assertEqual "codepoints that failed to roundtrip (LE)" [] bad
  ]
