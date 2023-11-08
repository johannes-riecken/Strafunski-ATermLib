{-# LANGUAGE EmptyCase, FlexibleContexts, DefaultSignatures, InstanceSigs, RankNTypes, ScopedTypeVariables, TypeApplications, TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
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
  default fromATerm :: (Generic t, GFromATermEither' (Rep t)) => ATerm -> t
  fromATerm = to . errorOnLeft . gfromATermEither' where
    errorOnLeft (Right x) = x
    errorOnLeft (Left err) = error err
  fromATermEither :: ATerm -> Either Error t
  default fromATermEither :: (Generic t, GFromATermEither' (Rep t)) => ATerm -> Either Error t
  fromATermEither = fmap to . gfromATermEither'

-- | Auxiliary function for reporting errors.
fromATermError :: String -> ATerm -> a
fromATermError t u
  = error ("Cannot convert ATerm to "++t++": "++err u)
    where err u = case u of
		  AAppl s _ -> '!':s
		  AList _   -> "!AList"
		  _ -> "!AInt"

fromATermError' :: String -> ATerm -> String
fromATermError' t u = ("Cannot convert ATerm to "++t++": "++err u)
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
  fromATermEither (AAppl s []) = Right $ read s
  fromATermEither t = Left (fromATermError' "Prelude.Either" t)

                                                                   -- Integral
instance {-# OVERLAPS #-} Integral n => ATermConvertible n where
  toATerm i			= AInt (toInteger i)
  fromATerm (AInt i)  		= fromInteger i
  fromATerm t			= fromATermError "Prelude.Integral" t
  fromATermEither (AInt i)  		= Right $ fromInteger i
  fromATermEither t			= Left $ fromATermError' "Prelude.Integral" t

                                                                       -- Bool
instance ATermConvertible Bool where
  toATerm True			= AAppl "True" []
  toATerm False			= AAppl "False" []
  fromATerm (AAppl "True" [])	= True
  fromATerm (AAppl "False" [])	= False
  fromATerm t			= fromATermError "Prelude.Bool" t
  fromATermEither (AAppl "True" [])	= Right True
  fromATermEither (AAppl "False" [])	= Right False
  fromATermEither t			= Left $ fromATermError' "Prelude.Bool" t
                                                                       -- Bool

instance ATermConvertible () where
  toATerm ()			= AAppl "()" []
  fromATerm (AAppl "()" [])	= ()
  fromATerm t			= fromATermError "Prelude.()" t
  fromATermEither (AAppl "()" [])	= Right ()
  fromATermEither t			= Left $ fromATermError' "Prelude.()" t

                                                                       -- Char
instance ATermConvertible Char where
  toATerm c			= AInt (toInteger . ord $ c)
  fromATerm (AInt c)		= chr . fromInteger $ c
  fromATerm t			= fromATermError "Prelude.Char" t
  fromATermEither (AInt c)		= Right . chr . fromInteger $ c
  fromATermEither t			= Left $ fromATermError' "Prelude.Char" t

                                                                      -- Ratio
instance (Integral a, ATermConvertible a)
      => ATermConvertible (Ratio a) where
  toATerm xy	= AAppl "Ratio" [toATerm (numerator xy),
                                 toATerm (denominator xy)]
  fromATerm (AAppl "Ratio" [x,y])
		= fromATerm x%fromATerm y
  fromATerm t	= fromATermError "Ratio.Ratio" t
  fromATermEither (AAppl "Ratio" [x,y])
		= Right $ fromATerm x%fromATerm y
  fromATermEither t	= Left $ fromATermError' "Ratio.Ratio" t

-----------------------------------------------------------------------------
-- * Generic instances

class GFromATermEither' f where
    gfromATermEither' :: ATerm -> Either Error (f a)

instance GFromATermEither' V1 where
    gfromATermEither' x = case x of {}

instance GFromATermEither' U1 where
    gfromATermEither' _ = Right U1

instance ATermConvertible c => GFromATermEither' (K1 i c) where
    gfromATermEither' :: forall c a. ATermConvertible c => ATerm -> Either Error (K1 i c a)
    gfromATermEither' x@(AAppl str xs) = Right . K1 $ fromATerm @c x
    gfromATermEither' x@(AInt _) = Right . K1 $ fromATerm @c x
    gfromATermEither' x@(AList xs) = Right . K1 $ fromATerm @c x

instance (GFromATermEither' f) => GFromATermEither' (M1 D t f) where
    gfromATermEither' x = M1 <$> gfromATermEither' x

instance (GFromATermList' f, Constructor t) => GFromATermEither' (M1 C t f) where
    gfromATermEither' xs@(AAppl x zs) = if x == conName y then
        M1 <$> gfromATermList' zs else
        Left ("constructor mismatch: got " <> x <> ", want " <> conName y) where
        y :: M1 C t f a
        y = undefined
    gfromATermEither' xs = Left ("expected AAppl, got " <> show xs)

instance (GFromATermEither' f) => GFromATermEither' (M1 S t f) where
    gfromATermEither' x = M1 <$> gfromATermEither' x

instance (GFromATermEither' f, GFromATermEither' g) => GFromATermEither' (f :+: g) where
    gfromATermEither' x = case gfromATermEither' x of
        Right x' -> Right (L1 x')
        Left err -> case gfromATermEither' x of
            Right x' -> Right (R1 x')
            Left err -> Left ("error in (:+:): " <> err)

type Error = String

class GFromATermList' f where
    gfromATermList' :: [ATerm] -> Either Error (f a)

instance GFromATermList' U1 where
    gfromATermList' _ = Right U1

instance GFromATermEither' f => GFromATermList' (M1 S t f) where
    gfromATermList' [x] = gfromATermEither' x
    gfromATermList' xxs = Left ("want singleton list, got list of length " <> show (length xxs))

instance ATermConvertible c => GFromATermList' (K1 i c) where
    gfromATermList' [x] = Right . K1 $ fromATerm x

instance (GFromATermList' f, GFromATermList' g) => GFromATermList' (f :*: g) where
    gfromATermList' xxs = (:*:) <$> gfromATermList' (take n xxs) <*> gfromATermList' (drop n xxs) where
        n = length xxs `div` 2


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

instance {-# OVERLAPS #-} (GATermListConvertible' f, GATermListConvertible' g) => GATermListConvertible' (f :*: g) where
    gtoATermList' (x :*: y) = gtoATermList' x <> gtoATermList' y

------------------------------------------------------------------------------
