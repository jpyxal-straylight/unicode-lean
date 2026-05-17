{-|
  Consolidated test entry point. Each per-module spec exports its own
  'TestTree' under the @tests@ name; this module assembles them under a
  single Tasty defaultMain so the build's checkPhase runs every spec.

  Test layout mirrors the per-module shape of unicode-lean's
  @Unicode/Codec/*.lean@ files. Concrete unit tests reproduce the
  Lean theorems; per-byte-class QuickCheck and exhaustive scalar-
  codepoint enumeration cover the closed-form roundtrip lemmas.
-}
module Main (main) where

import Test.Tasty (defaultMain, testGroup)

import qualified Utf8Spec
import qualified Utf16Spec
import qualified Utf32Spec
import qualified BomSpec
import qualified NoncharactersSpec
import qualified ValidatedUtf8Spec
import qualified OpaqueBlobSpec
import qualified IdentifierSpec

main :: IO ()
main = defaultMain $
  testGroup "unicode-hs"
    [ Utf8Spec.tests
    , Utf16Spec.tests
    , Utf32Spec.tests
    , BomSpec.tests
    , NoncharactersSpec.tests
    , ValidatedUtf8Spec.tests
    , OpaqueBlobSpec.tests
    , IdentifierSpec.tests
    ]
