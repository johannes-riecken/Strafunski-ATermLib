{-# LANGUAGE FlexibleContexts, DefaultSignatures, InstanceSigs, RankNTypes, ScopedTypeVariables, TypeApplications, TypeOperators #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (c) Joost Visser 2004
-- License     :  LGPL
--
-- Maintainer  :  joost.visser@di.uminho.pt
-- Stability   :  experimental
-- Portability :  portable
--
-- This module is part of the ATerm library for Haskell. It provides the class
-- ATermConvertible of types that are convertible to and from ATerms. Additionally,
-- it provides default instances of this class for some predefined Prelude
-- types.
--
-----------------------------------------------------------------------------

module Data.ATerm.Conversion where

import Control.Monad (guard)
import Data.ATerm.AbstractSyntax
import Data.ATerm.ReadWrite
import Data.Char
import Data.Maybe (fromJust)
import Data.Ratio
import GHC.Generics

-----------------------------------------------------------------------------
-- * Conversion to and from ATerms

class ATermConvertible t where
  -- | Convert to an ATerm.
  toATerm   :: t -> ATerm
  default toATerm :: (Generic t, GATermConvertible' (Rep t)) => t -> ATerm
  toATerm = gtoATerm' . from
  -- | Convert from an ATerm.
  fromATerm :: ATerm -> t
  default fromATerm :: (Generic t, GFromATermMaybe' (Rep t)) => ATerm -> t
  fromATerm = to . fromJust . gfromATermMaybe'

-- | Auxiliary function for reporting errors.
fromATermError :: String -> ATerm -> a
fromATermError t u
  = error ("Cannot convert ATerm to "++t++": "++err u)
    where err u = case u of
		  AAppl s _ -> '!':s
		  AList _   -> "!AList"
		  _ -> "!AInt"

-----------------------------------------------------------------------------
-- * Conversion of ATerms to and from Strings

-- | Convert to a textual ATerm representation without sharing (TXT format).
toATermString 		:: ATermConvertible t => t -> String
toATermString t		=  writeATerm (toATerm t)

-- | Convert to a textual ATerm representation with full sharing (TAF format).
toSharedATermString 	:: ATermConvertible t => t -> String
toSharedATermString t	= writeSharedATerm (toATerm t)

-- | Convert from a textual ATerm representation.
fromATermString 	:: ATermConvertible t => String -> t
fromATermString	s 	= fromATerm (readATerm s)

-----------------------------------------------------------------------------
-- * Instances for basic types
                                                                      -- Lists
instance {-# OVERLAPPABLE #-} ATermConvertible a => ATermConvertible [a] where
  toATerm as 		= AList (map toATerm as)
  fromATerm (AList as)	= map fromATerm as
  fromATerm t		= fromATermError "Prelude.[]" t

                                                                      -- Maybe
instance ATermConvertible a => ATermConvertible (Maybe a) where
  toATerm Nothing		= AAppl "None" []
  toATerm (Just a)  		= AAppl "Just" [toATerm a]
  fromATerm (AAppl "None" [])	= Nothing
  fromATerm (AAppl "Some" [a])	= Just (fromATerm a)
  fromATerm t			= fromATermError "Prelude.Maybe" t

                                                                   -- 2-Tuples
instance (ATermConvertible a, ATermConvertible b)
      => ATermConvertible (a,b) where
  toATerm (a,b)			    = AAppl "Tuple2" [toATerm a, toATerm b]
  fromATerm (AAppl "Tuple2" [a,b])  = (fromATerm a,fromATerm b)
  fromATerm t			    = fromATermError "Prelude.(,)" t

                                                                     -- Either
instance (ATermConvertible a, ATermConvertible b)
      => ATermConvertible (Either a b) where
  toATerm (Left a)		    = AAppl "Left" [toATerm a]
  toATerm (Right b)		    = AAppl "Right" [toATerm b]
  fromATerm (AAppl "Left" [a])      = Left (fromATerm a)
  fromATerm (AAppl "Right" [b])     = Right (fromATerm b)
  fromATerm t			    = fromATermError "Prelude.Either" t

                                                                     -- String
instance {-# OVERLAPS #-} ATermConvertible String where
  toATerm s			= AAppl (show s) []
  fromATerm (AAppl s [])  	= read s
  fromATerm t			= fromATermError "Prelude.String" t

                                                                   -- Integral
instance {-# OVERLAPS #-} Integral n => ATermConvertible n where
  toATerm i			= AInt (toInteger i)
  fromATerm (AInt i)  		= fromInteger i
  fromATerm t			= fromATermError "Prelude.Integral" t

                                                                       -- Bool
instance ATermConvertible Bool where
  toATerm True			= AAppl "True" []
  toATerm False			= AAppl "False" []
  fromATerm (AAppl "True" [])	= True
  fromATerm (AAppl "False" [])	= False
  fromATerm t			= fromATermError "Prelude.Bool" t
                                                                       -- Bool

instance ATermConvertible () where
  toATerm ()			= AAppl "()" []
  fromATerm (AAppl "()" [])	= ()
  fromATerm t			= fromATermError "Prelude.()" t

                                                                       -- Char
instance ATermConvertible Char where
  toATerm c			= AInt (toInteger . ord $ c)
  fromATerm (AInt c)		= chr . fromInteger $ c
  fromATerm t			= fromATermError "Prelude.Char" t

                                                                      -- Ratio
instance (Integral a, ATermConvertible a)
      => ATermConvertible (Ratio a) where
  toATerm xy	= AAppl "Ratio" [toATerm (numerator xy),
                                 toATerm (denominator xy)]
  fromATerm (AAppl "Ratio" [x,y])
		= fromATerm x%fromATerm y
  fromATerm t	= fromATermError "Ratio.Ratio" t

-----------------------------------------------------------------------------
-- * Generic instances

class GFromATermMaybe' f where
    gfromATermMaybe' :: ATerm -> Maybe (f a)

instance GFromATermMaybe' V1 where
    gfromATermMaybe' x = case x of

instance GFromATermMaybe' U1 where
    gfromATermMaybe' _ = Just U1

instance ATermConvertible c => GFromATermMaybe' (K1 i c) where
    gfromATermMaybe' :: forall c a. ATermConvertible c => ATerm -> Maybe (K1 i c a)
    gfromATermMaybe' x@(AAppl str xs) = Just . K1 $ fromATerm @c x
    gfromATermMaybe' x@(AInt _) = Just . K1 $ fromATerm @c x

instance (GFromATermMaybe' f) => GFromATermMaybe' (M1 D t f) where
    gfromATermMaybe' x = M1 <$> gfromATermMaybe' x

instance (GFromATermList' f, Constructor t) => GFromATermMaybe' (M1 C t f) where
    gfromATermMaybe' xs@(AAppl x zs) = guard (x == conName y) *> (M1 <$> gfromATermList' zs) where
        y :: M1 C t f a
        y = undefined

instance (GFromATermMaybe' f) => GFromATermMaybe' (M1 S t f) where
    gfromATermMaybe' x = M1 <$> gfromATermMaybe' x

instance (GFromATermMaybe' f, GFromATermMaybe' g) => GFromATermMaybe' (f :+: g) where
    gfromATermMaybe' x = case gfromATermMaybe' x of
        Just x' -> Just (L1 x')
        Nothing -> case gfromATermMaybe' x of
            Just x' -> Just (R1 x')
            Nothing -> Nothing


class GFromATermList' f where
    gfromATermList' :: [ATerm] -> Maybe (f a)

instance GFromATermList' U1 where
    gfromATermList' _ = Just U1

instance GFromATermMaybe' f => GFromATermList' (M1 S t f) where
    gfromATermList' [x] = gfromATermMaybe' x

instance (GFromATermMaybe' f, GFromATermList' g) => GFromATermList' (f :*: g) where
    gfromATermList' (x:xs) = (:*:) <$> gfromATermMaybe' x <*> gfromATermList' xs


class GATermConvertible' f where
    gtoATerm' :: f a -> ATerm

instance ATermConvertible c => GATermConvertible' (K1 i c) where
    gtoATerm' (K1 x) = toATerm x

instance (GATermListConvertible' f, Constructor t) => GATermConvertible' (M1 C t f) where
    gtoATerm' x@(M1 x') = AAppl (conName x) (gtoATermList' x')

instance GATermConvertible' f => GATermConvertible' (M1 D t f) where
    gtoATerm' x@(M1 x') = gtoATerm' x'

instance GATermConvertible' f => GATermConvertible' (M1 S t f) where
    gtoATerm' x@(M1 x') = gtoATerm' x'

instance (GATermConvertible' f, GATermConvertible' g) => GATermConvertible' (f :+: g) where
    gtoATerm' (L1 x) = gtoATerm' x
    gtoATerm' (R1 x) = gtoATerm' x

class GATermListConvertible' f where
    gtoATermList' :: f a -> [ATerm]

instance GATermListConvertible' U1 where
    gtoATermList' _ = []

instance GATermConvertible' f => GATermListConvertible' (M1 S t f) where
    gtoATermList' x = [gtoATerm' x]

instance {-# OVERLAPS #-} (GATermConvertible' f, GATermListConvertible' g) => GATermListConvertible' (f :*: g) where
    gtoATermList' (x :*: xs) = gtoATerm' x : gtoATermList' xs

------------------------------------------------------------------------------
