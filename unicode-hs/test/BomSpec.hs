{-|
  Tests for "Unicode.Codec.Bom" — mirrors the @detect_*@ theorems in
  @Unicode/Codec/Bom.lean@. Critical case: @FF FE 00 00@ resolves as
  UTF-32LE, not UTF-16LE followed by two NUL bytes.

  Imports the module qualified so the @BomKind.Utf8@ / @BomKind.Utf16BE@
  ctor names don't collide with the codec module names.
-}
module BomSpec (tests) where

import qualified Data.ByteString as BS
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import qualified Unicode.Codec.Bom as Bom

tests :: TestTree
tests = testGroup "Unicode.Codec.Bom"
  [ detectConcrete
  , detectPrecedence
  , detectNegative
  , stripBehaviour
  ]

detectConcrete :: TestTree
detectConcrete = testGroup "concrete BOM detection"
  [ testCase "detect_utf8_bom (EF BB BF)" $
      assertEqual ""
        (Just (Bom.Utf8, 3))
        (Bom.detect (BS.pack [0xEF, 0xBB, 0xBF]))
  , testCase "detect_utf8_bom_with_content" $
      assertEqual ""
        (Just (Bom.Utf8, 3))
        (Bom.detect (BS.pack [0xEF, 0xBB, 0xBF, 0x41]))
  , testCase "detect_utf16_be_bom (FE FF)" $
      assertEqual ""
        (Just (Bom.Utf16BE, 2))
        (Bom.detect (BS.pack [0xFE, 0xFF]))
  , testCase "detect_utf16_le_bom (FF FE)" $
      assertEqual ""
        (Just (Bom.Utf16LE, 2))
        (Bom.detect (BS.pack [0xFF, 0xFE]))
  , testCase "detect_utf32_be_bom (00 00 FE FF)" $
      assertEqual ""
        (Just (Bom.Utf32BE, 4))
        (Bom.detect (BS.pack [0x00, 0x00, 0xFE, 0xFF]))
  , testCase "detect_utf32_le_bom (FF FE 00 00)" $
      assertEqual ""
        (Just (Bom.Utf32LE, 4))
        (Bom.detect (BS.pack [0xFF, 0xFE, 0x00, 0x00]))
  ]

detectPrecedence :: TestTree
detectPrecedence = testGroup "precedence"
  [ testCase "detect_prefers_utf32_over_utf16 (FF FE 00 00 → UTF-32LE)" $
      assertEqual ""
        (Just (Bom.Utf32LE, 4))
        (Bom.detect (BS.pack [0xFF, 0xFE, 0x00, 0x00]))
  ]

detectNegative :: TestTree
detectNegative = testGroup "no BOM"
  [ testCase "detect_empty" $
      assertEqual "" Nothing (Bom.detect BS.empty)
  , testCase "detect_ascii (Hello)" $
      assertEqual "" Nothing
        (Bom.detect (BS.pack [0x48, 0x65, 0x6C, 0x6C, 0x6F]))
  ]

stripBehaviour :: TestTree
stripBehaviour = testGroup "strip"
  [ testCase "strip removes UTF-8 BOM, leaves content" $
      assertEqual ""
        (Just Bom.Utf8, BS.pack [0x41])
        (Bom.strip (BS.pack [0xEF, 0xBB, 0xBF, 0x41]))
  , testCase "strip on no-BOM input is identity" $
      assertEqual ""
        (Nothing, BS.pack [0x41, 0x42])
        (Bom.strip (BS.pack [0x41, 0x42]))
  , testCase "strip handles UTF-32LE precedence (FF FE 00 00 → UTF-32LE, content empty)" $
      assertEqual ""
        (Just Bom.Utf32LE, BS.empty)
        (Bom.strip (BS.pack [0xFF, 0xFE, 0x00, 0x00]))
  ]
