-- {-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE MultiWayIf                 #-}
{-# LANGUAGE RankNTypes                 #-}

{-# OPTIONS_GHC -fno-warn-orphans       #-}
-- We have some orphan Action instances here, but since Action is a multi-param
-- class there is really no better place to put them.

-----------------------------------------------------------------------------
-- |
-- Module      :  Diagrams.Core.Types
-- Copyright   :  (c) 2011-2015 diagrams-core team (see LICENSE)
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  diagrams-discuss@googlegroups.com
--
-- The core library of primitives forming the basis of an embedded
-- domain-specific language for describing and rendering diagrams.
--
-- "Diagrams.Core.Types" defines types and classes for
-- primitives, diagrams, and backends.
--
-----------------------------------------------------------------------------

{- ~~~~ Note [breaking up Types module]

   Although it's not as bad as it used to be, this module has a lot of
   stuff in it, and it might seem a good idea in principle to break it up
   into smaller modules.  However, it's not as easy as it sounds: everything
   in this module cyclically depends on everything else.
-}

module Diagrams.Core.Types where
  -- (
  --   -- * Annotations

  --   -- ** Static annotations
  --   Annotation(..)
  -- , applyAnnotation, href, opacityGroup, groupOpacity

  --   -- ** Up annotations
  -- , UpAnnots
  -- , upAnnots
  -- , envelope, trace, refmap, query

  --  -- ** Down annotations
  -- , DownAnnots, downT, transfFromAnnot

  --   -- ** Basic type definitions
  -- , QDiaLeaf(..)
  -- , QDiagram(..)
  -- , Diagram

  --   -- ** Creating diagrams
  -- , mkQD, mkQD', pointDiagram

  --   -- *** Other
  -- , setEnvelope
  -- , setTrace

  --   -- * Subdiagrams

  -- -- , Subdiagram(..), mkSubdiagram
  -- -- , getSub, rawSub
  -- -- , location
  -- -- , subPoint

  --   -- * Subdiagram maps

  -- , RefMap(..)

  --   -- * Primtives
  --   -- $prim

  -- , Prim(..)
  -- , _Prim

  --   -- * Backends

  -- , Backend(..)

  --   -- ** Null backend

  -- , NullBackend, D

  --   -- ** Number classes
  -- , TypeableFloat

  --   -- * Renderable

  -- , Renderable(..)

 -- ) where

import           Control.Arrow             (second, (***))
import           Control.Lens              hiding (transform)
import           Control.Monad             (mplus)
import           Data.List                 (isSuffixOf)
import qualified Data.Map                  as M
import qualified Data.Set                  as Set
import qualified Data.Sequence             as Seq
import           Data.Sequence             (ViewL (..), viewl)
import Data.Bool (bool)
import Data.Function (on)
import           Data.Maybe                (fromMaybe, listToMaybe)
import           Data.Semigroup
import qualified Data.Traversable          as T
import           Data.Typeable

import           Data.Monoid.Action
import           Data.Monoid.Coproduct
import           Data.Monoid.WithSemigroup
import           Data.Tree.DUAL.Internal

import           Diagrams.Core.Envelope
import           Diagrams.Core.HasOrigin
import           Diagrams.Core.Juxtapose
import           Diagrams.Core.Names
import           Diagrams.Core.Points
import           Diagrams.Core.Query
import           Diagrams.Core.Style
import           Diagrams.Core.Trace
import           Diagrams.Core.Transform
import           Diagrams.Core.V

import           Linear.Affine
import           Linear.Metric
import           Linear.Vector

-- XXX TODO: add lots of actual diagrams to illustrate the
-- documentation!  Haddock supports \<\<inline image urls\>\>.

-- | Class of numbers that are 'RealFloat' and 'Typeable'. This class is used to
--   shorten type constraints.
class (Typeable n, RealFloat n) => TypeableFloat n
instance (Typeable n, RealFloat n) => TypeableFloat n
-- use class instead of type constraint so users don't need constraint kinds pragma

------------------------------------------------------------------------
-- Annotations
------------------------------------------------------------------------

-- Up annotations ------------------------------------------------------

-- | Monoidal annotations which travel up the diagram tree, /i.e./ which
--   are aggregated from component diagrams to the whole:
--
--   * envelopes (see "Diagrams.Core.Envelope").
--     The envelopes are \"deletable\" meaning that at any point we can
--     throw away the existing envelope and replace it with a new one;
--     sometimes we want to consider a diagram as having a different
--     envelope unrelated to its \"natural\" envelope.
--
--   * traces (see "Diagrams.Core.Trace"), also
--     deletable.
--
--   * name/subdiagram associations (see "Diagrams.Core.Names")
--
--   * query functions (see "Diagrams.Core.Query")
newtype UpAnnots v n m = UpAnnots (Envelope v n, Trace v n, RefMap v n m, Query v n m)
  deriving (Typeable, Semigroup, Monoid, Functor)

instance Show (UpAnnots v n m) where
  show _ = "<UpAnnots>"


type instance V (UpAnnots v n m) = v
type instance N (UpAnnots v n m) = n

instance r ~ UpAnnots v' n' m' => Rewrapped (UpAnnots v n m) r
instance Wrapped (UpAnnots v n m) where
  type Unwrapped (UpAnnots v n m) = (Envelope v n, Trace v n, RefMap v n m, Query v n m)
  _Wrapped' = iso (\(UpAnnots a) -> a) UpAnnots

instance (Metric v, OrderedField n) => Transformable (UpAnnots v n m) where
  transform = over _Wrapped . transform

-- | Throw away all references.
instance (OrderedField n) => Applicative (UpAnnots v n) where
  pure q = UpAnnots (Envelope mempty, Trace $ \_ _ -> mempty, RefMap mempty, pure q)
  UpAnnots (e1, t1, _, q1) <*> UpAnnots (e2, t2, _, q2)
    = UpAnnots (e1 <> e2, t1 <> t2, RefMap mempty, q1 <*> q2)

-- | Makes 0 sense.
instance (Additive v, OrderedField n) => Monad (UpAnnots v n) where
  return = pure
  UpAnnots (e1, t1, _, q1) >>= f
    = UpAnnots (e1 <> e2, t1 <> t2, RefMap mempty, q2)
    where
      UpAnnots (e2, t2, _, q2) = f $ runQuery q1 origin


-- | Internal affine traversal over the top level upwards annotations.
--   Changing the 'RefMap' of an up can cause problems with references.
--   This is exported from 'Diagrams.Core.Types' for debugging purposes.
upAnnots :: Traversal' (QDiagram b v n m) (UpAnnots v n m)
upAnnots = _Wrapped' . _u

-- | Traversal over the envelope of a diagram. Does nothing for the
--   empty diagram.
envelope :: Traversal' (QDiagram b v n m) (Envelope v n)
envelope = upAnnots . _Wrapped' . _1

-- | Traversal over the trace of a diagram. Does nothing for the
--   empty diagram.
trace :: Traversal' (QDiagram b v n m) (Trace v n)
trace = upAnnots . _Wrapped' . _2

-- | Internal traversal over the reference map of a diagram.
--   Manually editing a reference map will likely end up in an
--   mal-formed reference between diagram. This is exported from
--   'Diagrams.Core.Types' for debugging purposes.
refmap :: Traversal' (QDiagram b v n m) (RefMap v n m)
refmap = upAnnots . _Wrapped' . _3

-- | Traversal over the query of a diagram. Does nothing for the
--   empty diagram.
query :: Traversal' (QDiagram b v n m) (Query v n m)
query = upAnnots . _Wrapped' . _4

-- todo: set on empty diagram

-- | Replace the envelope of a diagram.
setEnvelope :: Envelope v n -> QDiagram b v n m -> QDiagram b v n m
setEnvelope = set envelope

-- | Replace the envelope of a diagram.
setTrace :: Trace v n -> QDiagram b v n m -> QDiagram b v n m
setTrace = set trace

-- Down annotations ----------------------------------------------------

-- | Monoidal annotations which travel down the diagram tree,
--   /i.e./ which accumulate along each path to a leaf (and which can
--   act on the upwards-travelling annotations):
--
--   * styles (see "Diagrams.Core.Style")
type DownAnnots v n = Transformation v n :+: Style v n

  -- Note that we  put the transformations and styles together using a
  -- coproduct because the transformations can act on the styles.

downT :: Transformation v n -> DownAnnots v n
downT = inL

downSty :: Style v n -> DownAnnots v n
downSty = inR

instance Show (Transformation v n) where
  show _ = "<Transform>"

-- | Extract the (total) transformation from a downwards annotation
--   value.
transfFromAnnot :: (Additive v, Num n) => DownAnnots v n -> Transformation v n
transfFromAnnot = killR

-- Static annotation ---------------------------------------------------

-- | Static annotations which can be placed at a particular node of a
--   diagram tree.
data Annotation (v :: * -> *) n
  = Href String    -- ^ Hyperlink
  | OpacityGroup Double
  -- | Fading (QDiagram b v n Any)
  deriving Show

type instance V (Annotation v n) = v
type instance N (Annotation v n) = n

instance Transformable (Annotation v n) where
  transform _ = id

instance HasStyle (Annotation v n) where
  applyStyle _ = id

-- | Apply a static annotation at the root of a diagram.
applyAnnotation :: Annotation v n -> QDiagram b v n m -> QDiagram b v n m
applyAnnotation an (QD dt) = QD (annot an dt)

-- | Make a diagram into a hyperlink.  Note that only some backends
--   will honor hyperlink annotations.
href :: String -> QDiagram b v n m -> QDiagram b v n m
href = applyAnnotation . Href

-- | Change the transparency of a 'Diagram' as a group.
opacityGroup, groupOpacity :: Double -> QDiagram b v n m -> QDiagram b v n m
opacityGroup = applyAnnotation . OpacityGroup
groupOpacity = applyAnnotation . OpacityGroup

------------------------------------------------------------------------
-- Primitives
------------------------------------------------------------------------

-- $prim
-- Ultimately, every diagram is essentially a tree whose leaves are
-- /primitives/, basic building blocks which can be rendered by
-- backends. However, not every backend must be able to render every
-- type of primitive; the collection of primitives a given backend knows
-- how to render is determined by instances of 'Renderable'.

-- | A value of type @Prim b v n@ is an opaque (existentially quantified)
--   primitive which backend @b@ knows how to render in vector space @v@.
data Prim b v n where
  Prim :: (Transformable p, Typeable p, Renderable p b) => p -> Prim b (V p) (N p)

_Prim :: (Transformable p, Typeable p, Renderable p b) => Prism' (Prim b (V p) (N p)) p
_Prim = prism' Prim (\(Prim p) -> cast p)

type instance V (Prim b v n) = v
type instance N (Prim b v n) = n

-- | The 'Transformable' instance for 'Prim' just pushes calls to
--   'transform' down through the 'Prim' constructor.
instance Transformable (Prim b v n) where
  transform t (Prim p) = Prim (transform t p)

-- | The 'Renderable' instance for 'Prim' just pushes calls to
--   'render' down through the 'Prim' constructor.
instance Renderable (Prim b v n) b where
  render b (Prim p) = render b p

-- Leafs ---------------------------------------------------------------

-- | A leaf in a 'QDiagram' tree is either a 'Prim', or a \"delayed\"
--   @QDiagram@ which expands to a real @QDiagram@ once it learns the
--   \"final context\" in which it will be rendered.  For example, in
--   order to decide how to draw an arrow, we must know the precise
--   transformation applied to it (since the arrow head and tail are
--   scale-invariant).
data QDiaLeaf b v n m
  = PrimLeaf (Prim b v n)
  | DelayedLeaf (DownAnnots v n -> n -> n -> QDiagram b v n m)
    -- ^ The @QDiagram@ produced by a @DelayedLeaf@ function /must/
    --   already apply any transformation in the given
    --   @DownAnnots@ (that is, the transformation will not
    --   be applied by the context).
  deriving Functor

instance Show (QDiaLeaf b v n m) where
  show PrimLeaf {} = "PrimLeaf"
  show _           = "DelayedLeaf"

------------------------------------------------------------------------
-- Referencing subdiagrams
------------------------------------------------------------------------

-- | Tape describing how to get back a diagram. The list is the elements
--   of the Concat branches of the internal DALTree. The number is the
--   number of Annotation elements expected.
data Tape = Tape [Int] !Int
  deriving (Show, Ord, Eq)

-- | A 'Subref' is an internal reference to a named diagram embedded
--   within another diagram.
data Subref v n m = Subref (UpAnnots v n m) Tape
  deriving (Show, Functor)

-- | @updateTape a b@ updates tape @b@ for changes made to the tree from
--   traversing down to tape @a@.
updateTape :: Tape -> Tape -> Tape
updateTape (Tape xs _) (Tape ys a) = Tape (go xs ys) a
  where
    go []     js  = js
    go (i:is) jss@(j:js)
      -- Alter the tape according to how the branch was split. When i/=0
      -- the branch is split in three (with i in the middle). When i=0,
      -- the branch is split in two (with i at the start).
      | i <  j    = bool 1 2 (i==0) : (j - i - 1) : js
      | i == j    = bool 0 1 (i==0) : (j - i) : go is js
      | otherwise = 0 : jss

-- If they point to the same thing, they're the same.
instance Eq (Subref v n m) where
  (==) = (==) `on` view reftape

instance Ord (Subref v n m) where
  compare = compare `on` view reftape

reftape :: Lens' (Subref v n m) Tape
reftape f (Subref u t) = f t <&> \t' -> Subref u t'

refpath :: Lens' (Subref v n m) [Int]
refpath = reftape . x
  where x f (Tape p i) = f p <&> \p' -> Tape p' i

subup :: Lens' (Subref v n m) (UpAnnots v n m)
subup f (Subref u t) = f u <&> \u' -> Subref u' t

-- Make a reference to the top level a diagram. When two diagrams are
-- combined or a diagram is traversed, this reference gets updated
-- accordingly.
subref :: (Ord n, Monoid m) => QDiagram b v n m -> Subref v n m
subref qd = Subref (qd ^. upAnnots) (Tape [] 0)
  where
    -- The number of annotations before a Concat or Leaf.
    i = case qd ^? dal of
          Just t  -> go 0 t
          Nothing -> -1
    go i = \case
      Down _ t  -> go i t
      Annot _ t -> go (i+1) t
      _         -> i

-- TEMPOARY

dal :: Traversal' (QDiagram b v n m) (DALTree (DownAnnots v n) (Annotation v n) (QDiaLeaf b v n m))
dal f (QD (DUALTree u d)) = QD . DUALTree u <$> f d
dal _ _                   = pure (QD EmptyDUAL)

-- | Give the current diagram a name that can be referenced with
--   'named'.
name :: (Ord n, Monoid m, IsName nm) => nm -> QDiagram b v n m -> QDiagram b v n m
name (toName -> Name nms) d = over (refmap . _Wrapped') addNames d
  where
    addNames m    = foldl addAName m nms
    addAName m nm = M.insertWith (<>) nm (Set.singleton $ subref d) m

named :: (Metric v, OrderedField n, Semigroup m)
      => IsName nm => nm -> Traversal' (QDiagram b v n m) (QDiagram b v n m)
named nm f d =
  case indexRef (toName nm) (d^.refmap) ^? _Wrapped . _head of
    Just (Subref u t) -> tapeDiaTraverse u t f d
    Nothing           -> pure d

-- -- | Push @d@ annotations down to the selected leaf. None of the old @d@
-- --   annotations be above will remain. Static @a@ annotations are acted
-- --   on by the accumilated @d@ annotation when it's reached.
-- tapeTraverse :: (Applicative f, Monoid d)
--              => Tape -> (d -> DALTree d a l -> f (DALTree d a l)) -> DALTree d a l
--              -> f (DALTree d a l)
-- tapeTraverse (Tape t _) f = go mempty t where
--   -- The result is a little funny because it returns any a annotations
--   -- present, even though they could have been made after the tape was
--   -- formed. Need to think about this.
--   go d []         = f d
--   -- Search for the next Concat and get element i from it.
--   go d iss@(i:is) = \case
--     Down d' t -> go (d `mappend` d') iss t
--     Annot a t -> Annot a <$> go d iss t
--     -- Everything on the left and right of the target receives the d
--     -- annotation accumulated so far. The target has its d annotation
--     -- pushed further down.
--     Concat ts
--       | (sL, sR') <- Seq.splitAt i ts
--       , t :< sR   <- viewl sR' ->
--           go d is t <&> \t' -> list $
--             if | null sL   -> [t', dw sR]
--                | null sR   -> [dw sL, t']
--                | otherwise -> [dw sL, t', dw sR]
--       where dw = Down d . Concat
--     -- The search has failed. We keep any accumulated down annotations.
--     -- This isn't a great solution but generally speaking the tape given
--     -- should point to something that exists.
--     l             -> pure (Down d l)
--     where list a = Concat (Seq.fromList a)

-- | Push @d@ annotations down to the selected leaf. None of the old @d@
--   annotations be above will remain. Static @a@ annotations are acted
--   on by the accumilated @d@ annotation when it's reached.
tapeTraverse :: forall f d u a l. (Action d u, Applicative f, Monoid' d, Semigroup u)
             => u
             -> Tape
             -> (d -> DUALTree d u a l -> f (DUALTree d u a l))
             -> DUALTree d u a l
             -> f (DUALTree d u a l)
tapeTraverse u (Tape p _) f EmptyDUAL       = pure EmptyDUAL
tapeTraverse u (Tape p _) f (DUALTree u0 t) = unAnnots <>~ u0 $ go mempty p t where
  -- The result is a little funny because it returns any a annotations
  -- present, even though they could have been made after the tape was
  -- formed. Need to think about this.
  go :: d -> [Int] -> DALTree d a l -> f (DUALTree d u a l)
  go d []         = f d . DUALTree u
  -- Search for the next Concat and get element i from it.
  go d iss@(i:is) = \case
      Down d' t -> go (d `mappend` d') iss t
      Annot a t -> annot a <$> go d iss t
      -- Everything on the left and right of the target receives the d
      -- annotation accumulated so far. The target has its d annotation
      -- pushed further down.
      Concat ts
        | (sL, sR') <- Seq.splitAt i ts
        , t :< sR   <- viewl sR' ->
            go d is t <&> \(DUALTree u' t') -> DUALTree u' $ list $
              if | null sL   -> [t', dw sR]
                 | null sR   -> [dw sL, t']
                 | otherwise -> [dw sL, t', dw sR]
            where dw = Down d . Concat
      -- The search has failed. We keep any accumulated down annotations.
      -- This isn't a great solution but generally speaking the tape given
      -- should point to something that exists.
      l             -> pure (down d $ DUALTree u l)
      where list a = Concat (Seq.fromList a)
            unU (DUALTree _ x) = x


tapeDiaTraverse :: (Applicative f, Metric v, OrderedField n, Semigroup m)
                => UpAnnots v n m
                -> Tape
                -> (QDiagram b v n m -> f (QDiagram b v n m))
                -> QDiagram b v n m
                -> f (QDiagram b v n m)
tapeDiaTraverse u t f dia = QD <$> fdual
  where
    fdual    = tapeTraverse u t g (dia ^. _Wrapped)
    g d dual = view _Wrapped <$> f (QD . down d $ dual)

-- Reference maps ------------------------------------------------------

-- | A 'RefMap' in an internal mapping of 'AName's to a set of 'Subref's.

-- | A 'RefMap' is a map associating names to subdiagrams. There can
--   be multiple associations for any given name, but each name can
--   point to a subdiagram once (enforced by the set).
newtype RefMap v n m = RefMap (M.Map AName (Set.Set (Subref v n m)))
  deriving Show

type instance V (RefMap v n m) = v
type instance N (RefMap v n m) = n

instance Rewrapped (RefMap v n m) (RefMap v' n' m')
instance Wrapped (RefMap v n m) where
  type Unwrapped (RefMap v n m) = M.Map AName (Set.Set (Subref v n m))
  _Wrapped' = iso (\(RefMap m) -> m) RefMap

instance Functor (RefMap v n) where
  fmap = over (_Wrapped . mapped . sets Set.map . mapped)

indexRef :: Name -> RefMap v n m -> Set.Set (Subref v n m)
indexRef (Name nms) (RefMap m) = foldl1 Set.intersection matches
  where matches = m ^.. foldMap ix nms

-- Traversal over all tape paths of up annotations. This is only a valid
-- traversal if you don't make two paths in the same RefMap Set overlap.
paths :: Traversal' (UpAnnots v n m) [Int]
paths = _Wrapped' . _3 . _Wrapped' . each
      . _Wrapping Set.fromList . each . refpath

instance Semigroup (RefMap v n m) where
  RefMap s1 <> RefMap s2 = RefMap $ M.unionWith (<>) s1 s2

-- | 'RefMap's form a monoid with the empty map as the identity, and
--   map union as the binary operation.  No information is ever lost:
--   if two maps have the same name in their domain, the resulting map
--   will associate that name to the concatenation of the information
--   associated with that name.
instance Monoid (RefMap v n m) where
  mempty  = RefMap mempty
  mappend = (<>)

type instance V (RefMap v n m) = v
type instance N (RefMap v n m) = n

instance (OrderedField n, Metric v) => HasOrigin (RefMap v n m) where
  moveOriginTo _ = id

instance (Metric v, Floating n) => Transformable (RefMap v n m) where
  transform _ = id

------------------------------------------------------------------------
-- QDiagram
------------------------------------------------------------------------

-- | The fundamental diagram type.  The type variables are as follows:
--
--   * @b@ represents the backend, such as @SVG@ or @Cairo@.  Note
--     that each backend also exports a type synonym @B@ for itself,
--     so the type variable @b@ may also typically be instantiated by
--     @B@, meaning \"use whatever backend is in scope\".
--
--   * @v@ represents the vector space of the diagram.  Typical
--     instantiations include @V2@ (for a two-dimensional diagram) or
--     @V3@ (for a three-dimensional diagram).
--
--   * @n@ represents the numerical field the diagram uses.  Typically
--     this will be a concrete numeric type like @Double@.
--
--   * @m@ is the monoidal type of \"query annotations\": each point
--     in the diagram has a value of type @m@ associated to it, and
--     these values are combined according to the 'Monoid' instance
--     for @m@.  Most often, @m@ is simply instantiated to 'Any',
--     associating a simple @Bool@ value to each point indicating
--     whether the point is inside the diagram; 'Diagram' is a synonym
--     for @QDiagram@ with @m@ thus instantiated to @Any@.
--
--   Diagrams can be combined via their 'Monoid' instance, transformed
--   via their 'Transformable' instance, and assigned attributes via
--   their 'HasStyle' instance.
--
--   Note that the @Q@ in @QDiagram@ stands for \"Queriable\", as
--   distinguished from 'Diagram', where @m@ is fixed to @Any@.  This
--   is not really a very good name, but it's probably not worth
--   changing it at this point.
newtype QDiagram b v n m
  = QD (DUALTree (DownAnnots v n) (UpAnnots v n m) (Annotation v n) (QDiaLeaf b v n m))
-- #if __GLASGOW_HASKELL__ >= 707
  deriving (Show, Typeable)
-- #else

-- instance forall b v. (Typeable b, Typeable1 v) => Typeable2 (QDiagram b v) where
--   typeOf2 _ = mkTyConApp (mkTyCon3 "diagrams-core" "Diagrams.Core.Types" "QDiagram") [] `mkAppTy`
--               typeOf (undefined :: b)                                                   `mkAppTy`
--               typeOf1 (undefined :: v n)
-- #endif

type instance V (QDiagram b v n m) = v
type instance N (QDiagram b v n m) = n

instance Rewrapped (QDiagram b v n m) (QDiagram b' v' n' m')
instance Wrapped (QDiagram b v n m) where
  type Unwrapped (QDiagram b v n m) =
    DUALTree (DownAnnots v n) (UpAnnots v n m) (Annotation v n) (QDiaLeaf b v n m)
  _Wrapped' = iso (\(QD d) -> d) QD

-- | @Diagram b@ is a synonym for @'QDiagram' b (V b) (N b) 'Any'@.  That is,
--   the default sort of diagram is one where querying at a point
--   simply tells you whether the diagram contains that point or not.
--   Transforming a default diagram into one with a more interesting
--   query can be done via the 'Functor' instance of @'QDiagram' b v n@ or
--   the 'value' function.
type Diagram b = QDiagram b (V b) (N b) Any

-- Construction --------------------------------------------------------

-- | Create a \"point diagram\", which has no content, no trace, an
--   empty query, and a point envelope.
pointDiagram :: (Metric v, OrderedField n, Monoid m) => Point v n -> QDiagram b v n m
pointDiagram p = QD $ leafU (mempty & _Wrapped . _1 .~ pointEnvelope p)

-- | Create a diagram from a single primitive, along with an envelope,
--   trace, subdiagram map, and query function.
mkQD :: Prim b v n -> Envelope v n -> Trace v n -> Query v n m
     -> QDiagram b v n m
mkQD p = mkQD' (PrimLeaf p)

-- | Create a diagram from a generic QDiaLeaf, along with an envelope,
--   trace, subdiagram map, and query function.
mkQD' :: QDiaLeaf b v n m -> Envelope v n -> Trace v n -> Query v n m
      -> QDiagram b v n m
mkQD' l e t q = QD $ leaf (UpAnnots (e,t,mempty,q)) l

-- Instances -----------------------------------------------------------

instance (OrderedField n, Semigroup m) => Semigroup (QDiagram b v n m) where
  -- Swap order so that primitives of d2 come first, i.e. will be
  -- rendered first, i.e. will be on the bottom.
  QD (DUALTree u2 t2) <> QD (DUALTree u1 t1) = QD $
    -- Ugly cases to get tapes to record concatenation correctly. The
    -- concatenation of the internal DALTree is the same as the
    -- semigroup instance, we just need to know what happened for the
    -- tape.
    case (t1,t2) of
      (Concat a, Concat b) -> mk (a <> b) $ u1         <> pf (_head +~ l a) u2
      (Concat a, b       ) -> mk (a |> b) $ u1         <> pf (l a:) u2
      (a       , Concat b) -> mk (a <| b) $ pf (0:) u1 <> pf (_head +~ 1) u2
      (a, b)   -> mk (Seq.fromList [a,b]) $ pf (0:) u1 <> pf (1:) u2
    where mk t m = DUALTree m (Concat t)
          pf     = over paths
          l      = Seq.length

  QD EmptyDUAL <> t2          = t2
  t1           <> QD EmptyDUAL = t1

-- instance (Metric v, OrderedField n, Semigroup m)
--   => Semigroup (QDiagram b v n m) where
  -- QD d1 <> QD d2 = QD (d2 <> d1)

-- | Diagrams form a monoid since each of their components do: the
--   empty diagram has no primitives, an empty envelope, an empty
--   trace, no named subdiagrams, and a constantly empty query
--   function.
--
--   Diagrams compose by aligning their respective local origins.  The
--   new diagram has all the primitives and all the names from the two
--   diagrams combined, and query functions are combined pointwise.
--   The first diagram goes on top of the second.  \"On top of\"
--   probably only makes sense in vector spaces of dimension lower
--   than 3, but in theory it could make sense for, say, 3-dimensional
--   diagrams when viewed by 4-dimensional beings.
instance (Metric v, OrderedField n, Semigroup m)
  => Monoid (QDiagram b v n m) where
  mempty  = QD mempty
  mappend = (<>)

instance Functor (QDiagram b v n) where
  fmap f = over _Wrapped
             $ (_u . mapped %~ f) -- up annots
             . (fmap . fmap) f      -- leaves

instance (Metric v, OrderedField n, Semigroup m) => HasStyle (QDiagram b v n m) where
  applyStyle = over _Wrapped' . down . downSty

instance (Metric v, OrderedField n, Monoid' m)
    => Juxtaposable (QDiagram b v n m) where
  juxtapose = juxtaposeDefault

instance (Metric v, OrderedField n, Monoid' m)
    => Enveloped (QDiagram b v n m) where
  getEnvelope = view envelope

instance (Metric v, OrderedField n, Semigroup m)
    => Traced (QDiagram b v n m) where
  getTrace = view trace

-- | Every diagram has an intrinsic \"local origin\" which is the
--   basis for all combining operations.
instance (Metric v, OrderedField n, Semigroup m)
    => HasOrigin (QDiagram b v n m) where
  moveOriginTo = translate . (origin .-.)

-- | Diagrams can be transformed by transforming each of their
--   components appropriately.
instance (OrderedField n, Metric v, Semigroup m)
    => Transformable (QDiagram b v n m) where
  transform = over _Wrapped' . down . downT

-- | All refs on the applying diagram are wiped. All refs on the appied
--   diagram get applied from the head diagram.
-- instance (OrderedField n) => Applicative (QDiagram b v n) where
--   pure a = QD $ leafU (pure a)

--   QD (DUALTree u1 t1) <*> QD (DUALTree u2 t2)
--     = QD $ DUALTree (u1 <*> u2) (t1 <> t2)

-- -- | Diagrams can be qualified so that all their named points can
-- --   now be referred to using the qualification prefix.
-- instance (Metric v, OrderedField n, Semigroup m)
--     => Qualifiable (QDiagram b v n m) where
--   n .>> d = over subMap (n .>>) d

------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Backends
------------------------------------------------------------------------

-- | Abstract diagrams are rendered to particular formats by
--   /backends/.  Each backend/vector space combination must be an
--   instance of the 'Backend' class.
--
--   A minimal complete definition consists of 'Render', 'Result',
--   'Options', and 'renderDia'. However, most backends will want to
--   implement 'adjustDia' as well; the default definition does
--   nothing.  Some useful standard definitions are provided in the
--   @Diagrams.TwoD.Adjust@ module from the @diagrams-lib@ package.
class Backend b v n where

  -- | An intermediate representation used for rendering primitives.
  --   (Typically, this will be some sort of monad, but it need not
  --   be.)  The 'Renderable' class guarantees that a backend will be
  --   able to convert primitives into this type; how these rendered
  --   primitives are combined into an ultimate 'Result' is completely
  --   up to the backend.
  data Render b v n :: *

  -- | The result of running/interpreting a rendering operation.
  type Result b v n :: *

  -- | Backend-specific rendering options.
  data Options b v n :: *

  -- | 'adjustDia' allows the backend to make adjustments to the final
  --   diagram (e.g. to adjust the size based on the options) before
  --   rendering it. It returns a modified options record, the
  --   transformation applied to the diagram (which can be used to
  --   convert attributes whose value is @Measure@, or transform
  --   /e.g./ screen coordinates back into local diagram coordinates),
  --   and the adjusted diagram itself.
  --
  --   See the diagrams-lib package (particularly the
  --   @Diagrams.TwoD.Adjust@ module) for some useful implementations.
  adjustDia :: (Additive v, Monoid' m, Num n) => b -> Options b v n
            -> QDiagram b v n m -> (Options b v n, Transformation v n, QDiagram b v n m)
  adjustDia _ o d = (o,mempty,d)

  -- | Given some options, take a representation of a diagram as a
  --   tree and render it.  The 'RTree' has already been simplified
  --   and has all measurements converted to @Output@ units.
  renderDUAL :: Monoid' m => b -> Options b v n -> Transformation v n -> QDiagram b v n m -> Result b v n

  -- See Note [backend token]

-- | The @D@ type is provided for convenience in situations where you
--   must give a diagram a concrete, monomorphic type, but don't care
--   which one.  Such situations arise when you pass a diagram to a
--   function which is polymorphic in its input but monomorphic in its
--   output, such as 'width', 'height', 'phantom', or 'names'.  Such
--   functions compute some property of the diagram, or use it to
--   accomplish some other purpose, but do not result in the diagram
--   being rendered.  If the diagram does not have a monomorphic type,
--   GHC complains that it cannot determine the diagram's type.
--
--   For example, here is the error we get if we try to compute the
--   width of an image (this example requires @diagrams-lib@):
--
--   @
--   ghci> width (image (uncheckedImageRef \"foo.png\" 200 200))
--   \<interactive\>:11:8:
--       No instance for (Renderable (DImage n0 External) b0)
--         arising from a use of `image'
--       The type variables `n0', `b0' are ambiguous
--       Possible fix: add a type signature that fixes these type variable(s)
--       Note: there is a potential instance available:
--         instance Fractional n => Renderable (DImage n a) NullBackend
--           -- Defined in `Diagrams.TwoD.Image'
--       Possible fix:
--         add an instance declaration for
--         (Renderable (DImage n0 External) b0)
--       In the first argument of `width', namely
--         `(image (uncheckedImageRef \"foo.png\" 200 200))'
--       In the expression:
--         width (image (uncheckedImageRef \"foo.png\" 200 200))
--       In an equation for `it':
--           it = width (image (uncheckedImageRef \"foo.png\" 200 200))
--   @
--
--   GHC complains that there is no instance for @Renderable (DImage n0
--   External) b0@; what is really going on is that it does not have enough
--   information to decide what backend to use (hence the
--   uninstantiated @n0@ and @b0@). This is annoying because /we/ know that the
--   choice of backend cannot possibly affect the width of the image
--   (it's 200! it's right there in the code!); /but/ there is no way
--   for GHC to know that.
--
--   The solution is to annotate the call to 'image' with the type
--   @'D' 'V2' 'Double'@, like so:
--
--   @
--   ghci> width (image (uncheckedImageRef \"foo.png\" 200 200) :: D V2 Double)
--   200.00000000000006
--   @
--
--   (It turns out the width wasn't 200 after all...)
--
--   As another example, here is the error we get if we try to compute
--   the width of a radius-1 circle:
--
--   @
--   ghci> width (circle 1)
--   \<interactive\>:12:1:
--       Couldn't match expected type `V2' with actual type `V a0'
--       The type variable `a0' is ambiguous
--       Possible fix: add a type signature that fixes these type variable(s)
--       In the expression: width (circle 1)
--       In an equation for `it': it = width (circle 1)
--   @
--
--   There's even more ambiguity here.  Whereas 'image' always returns
--   a 'Diagram', the 'circle' function can produce any 'TrailLike'
--   type, and the 'width' function can consume any 'Enveloped' type,
--   so GHC has no idea what type to pick to go in the middle.
--   However, the solution is the same:
--
--   @
--   ghci> width (circle 1 :: D V2 Double)
--   1.9999999999999998
--   @

type D v n = QDiagram NullBackend v n Any


-- | A null backend which does no actual rendering.  It is provided
--   mainly for convenience in situations where you must give a
--   diagram a concrete, monomorphic type, but don't actually care
--   which one.  See 'D' for more explanation and examples.
--
--   It is courteous, when defining a new primitive @P@, to make an instance
--
--   > instance Renderable P NullBackend where
--   >   render _ _ = mempty
--
--   This ensures that the trick with 'D' annotations can be used for
--   diagrams containing your primitive.
data NullBackend
  deriving Typeable

-- Note: we can't make a once-and-for-all instance
--
-- > instance Renderable a NullBackend where
-- >   render _ _ = mempty
--
-- because it overlaps with the Renderable instance for NullPrim.

instance Monoid (Render NullBackend v n) where
  mempty      = NullBackendRender
  mappend _ _ = NullBackendRender

instance Backend NullBackend v n where
  data Render NullBackend v n = NullBackendRender
  type Result NullBackend v n = ()
  data Options NullBackend v n

  renderDUAL _ _ _ _ = ()

-- | The Renderable type class connects backends to primitives which
--   they know how to render.
class Transformable t => Renderable t b where
  render :: b -> t -> Render b (V t) (N t)
  -- ^ Given a token representing the backend and a
  --   transformable object, render it in the appropriate rendering
  --   context.

  -- See Note [backend token]

{-
~~~~ Note [backend token]

A bunch of methods here take a "backend token" as an argument.  The
backend token is expected to carry no actual information; it is solely
to help out the type system. The problem is that all these methods
return some associated type applied to b (e.g. Render b) and unifying
them with something else will never work, since type families are not
necessarily injective.
-}
