{-|
  Tests for "Unicode.Codec.Noncharacters" — mirrors the @isNoncharacter_*@
  theorems plus the count/enumeration lemmas from
  @Unicode/Codec/Noncharacters.lean@.
-}
module NoncharactersSpec (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import Unicode.Codec.Noncharacters (allNoncharacters, isNoncharacter)

tests :: TestTree
tests = testGroup "Unicode.Codec.Noncharacters"
  [ bmpBlock
  , planeEnds
  , negatives
  , enumeration
  ]

bmpBlock :: TestTree
bmpBlock = testGroup "BMP block (FDD0..FDEF)"
  [ testCase "FDD0 is a noncharacter" $
      assertEqual "" True (isNoncharacter 0xFDD0)
  , testCase "FDEF is a noncharacter" $
      assertEqual "" True (isNoncharacter 0xFDEF)
  , testCase "every codepoint in FDD0..FDEF is a noncharacter" $
      assertEqual ""
        [] [ cp | cp <- [0xFDD0 .. 0xFDEF], not (isNoncharacter cp) ]
  , testCase "FDCF (just below block) is not a noncharacter" $
      assertEqual "" False (isNoncharacter 0xFDCF)
  , testCase "FDF0 (just above block) is not a noncharacter" $
      assertEqual "" False (isNoncharacter 0xFDF0)
  ]

planeEnds :: TestTree
planeEnds = testGroup "plane ends (nnFFFE / nnFFFF, n=0..16)"
  [ testCase "FFFE is a noncharacter" $
      assertEqual "" True (isNoncharacter 0xFFFE)
  , testCase "FFFF is a noncharacter" $
      assertEqual "" True (isNoncharacter 0xFFFF)
  , testCase "1FFFE is a noncharacter" $
      assertEqual "" True (isNoncharacter 0x1FFFE)
  , testCase "1FFFF is a noncharacter" $
      assertEqual "" True (isNoncharacter 0x1FFFF)
  , testCase "10FFFE is a noncharacter" $
      assertEqual "" True (isNoncharacter 0x10FFFE)
  , testCase "10FFFF is a noncharacter" $
      assertEqual "" True (isNoncharacter 0x10FFFF)
  , testCase "110000 (beyond max) is not flagged" $
      assertEqual "" False (isNoncharacter 0x110000)
  ]

negatives :: TestTree
negatives = testGroup "regular codepoints"
  [ testCase "A (U+0041) is not a noncharacter" $
      assertEqual "" False (isNoncharacter 0x0041)
  , testCase "é (U+00E9) is not a noncharacter" $
      assertEqual "" False (isNoncharacter 0x00E9)
  , testCase "ぁ (U+3042) is not a noncharacter" $
      assertEqual "" False (isNoncharacter 0x3042)
  , testCase "😀 (U+1F600) is not a noncharacter" $
      assertEqual "" False (isNoncharacter 0x1F600)
  ]

enumeration :: TestTree
enumeration = testGroup "enumeration"
  [ testCase "allNoncharacters has exactly 66 elements" $
      assertEqual "" 66 (length allNoncharacters)
  , testCase "every enumerated noncharacter satisfies isNoncharacter" $
      assertEqual ""
        [] [ cp | cp <- allNoncharacters, not (isNoncharacter cp) ]
  , testCase "every enumerated noncharacter is in the valid scalar range" $
      assertEqual ""
        []
        [ cp
        | cp <- allNoncharacters
        , cp < 0 || cp > 0x10FFFF || (cp >= 0xD800 && cp <= 0xDFFF)
        ]
  ]
