{-|
Module      : Unicode.Codec.Noncharacters
Description : Detection and enumeration of the 66 designated Unicode noncharacters.

Haskell port of @Unicode.Codec.Noncharacters@ from unicode-lean.

Two categories per UAX #44 §5.6 / Unicode Standard 17.0 §23.7:

  * BMP block:    U+FDD0 .. U+FDEF                (32 codepoints)
  * Plane ends:   U+nnFFFE / U+nnFFFF for n=0..16 (34 codepoints)

Total: 66.

Noncharacters are reserved for internal use; conformant Unicode text
MUST NOT contain them in interchange. They are technically valid scalar
codepoints (in the range and not surrogates), so a scalar-codepoint
predicate accepts them; downstream consumers that reject noncharacters
layer this predicate on top.
-}
module Unicode.Codec.Noncharacters
  ( isNoncharacter
  , allNoncharacters
  ) where

import Data.Bits ((.&.))

-- | True iff @cp@ is one of the 66 designated Unicode noncharacters.
isNoncharacter :: Int -> Bool
isNoncharacter cp =
  inBmpBlock || inPlaneEnd
  where
    inBmpBlock = cp >= 0xFDD0 && cp <= 0xFDEF
    low16      = cp .&. 0xFFFF
    inPlaneEnd = cp <= 0x10FFFF && (low16 == 0xFFFE || low16 == 0xFFFF)

-- | Enumerate the 66 noncharacters in ascending order.
allNoncharacters :: [Int]
allNoncharacters =
  bmpBlock ++ planeEnds
  where
    bmpBlock  = [0xFDD0 .. 0xFDEF]
    planeEnds = concatMap (\n -> [ n * 0x10000 + 0xFFFE
                                 , n * 0x10000 + 0xFFFF ]) [0 .. 16]
