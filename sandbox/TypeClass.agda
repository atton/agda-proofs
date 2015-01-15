-- type class example
-- http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.InstanceArguments?from=ReferenceManual.Non-canonicalImplicitArguments

open import Function
open import Data.Bool
open import Data.Nat

record Eq (t : Set) : Set where
  field _==_ : t → t → Bool
  _/=_ : t → t → Bool
  a /= b = not $ a == b


open module EqWithImplicits {t : Set} {{eqT : Eq t}} = Eq eqT

instance
   postulate  
     eqℕ    : Eq ℕ
     eqBool : Eq Bool


test = 5 == 3 ∧ true /= false
