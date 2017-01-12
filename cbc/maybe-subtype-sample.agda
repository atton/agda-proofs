module maybe-subtype-sample where

open import subtype 


return : {_ : Context A} {_ : Meta (Context A)} {{_ : N.DataSegment A}} {{_ : M.DataSegment A}} -> A -> Meta A
return {c} {mc} {{nd}} {{md}} a = record {context = con ; maybeElem = just a}
  where
    con = record { elem = a }


fmap : {B : Set} {{_ : M.DataSegment A}} {{_ : M.DataSegment B}} -> M.CodeSegment A B -> Meta (Context A) -> Meta (Context B)
fmap code x = {!!} -- exec code x
