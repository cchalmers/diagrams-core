{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE ExistentialQuantification  #-}
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

{-# OPTIONS_GHC -fno-warn-orphans       #-}
-- We have some orphan Action instances here, but since Action is a multi-param
-- class there is really no better place to put them.

-----------------------------------------------------------------------------
-- |
-- Module      :  Diagrams.Core.Types
-- Copyright   :  (c) 2011-2013 diagrams-core team (see LICENSE)
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

module Diagrams.Core.Types
       (
         -- * Diagrams

         -- ** Annotations

         -- *** Static annotations
         Annotation(Href)
       , applyAnnotation, href

         -- *** Dynamic (monoidal) annotations
       , UpAnnots, DownAnnots, transfToAnnot, transfFromAnnot

         -- ** Basic type definitions
       , QDiaLeaf(..), withQDiaLeaf
       , QDiagram(..), Diagram

         -- * Operations on diagrams
         -- ** Creating diagrams
       , mkQD, mkQD', pointDiagram

         -- ** Extracting information
       , envelope, trace, subMap, names, query, sample
       , value, resetValue, clearValue

         -- ** Combining diagrams

         -- | For many more ways of combining diagrams, see
         -- "Diagrams.Combinators" from the diagrams-lib package.

       , atop

         -- ** Modifying diagrams
         -- *** Names
       , nameSub
       , lookupName
       , withName
       , withNameAll
       , withNames
       , localize

         -- *** Other
       , setEnvelope
       , setTrace

         -- * Measurements
       , Measure(..)
       , fromMeasure
       , fromOutput
       , atMost, atLeast
       , scaleLocal

         -- * Subdiagrams

       , Subdiagram(..), mkSubdiagram
       , getSub, rawSub
       , location
       , subPoint

         -- * Subdiagram maps

       , SubMap(..)

       , fromNames, rememberAs, lookupSub

         -- * Primtives
         -- $prim

       , Prim(..)

         -- * Backends

       , Backend(..)
       , DNode(..)
       , DTree
       , RNode(..)
       , RTree

         -- ** Null backend

       , NullBackend, D

         -- ** Number classes
       , TypeableFloat
       , DataFloat

         -- * Renderable

       , Renderable(..)

       ) where

import           Control.Arrow             (first, second, (***))
import           Control.Lens              (Lens', Rewrapped, Wrapped (..), iso, lens, over, view,
                                            (^.), _Wrapped, _Wrapping)
import           Control.Monad             (mplus)
import           Data.Data
import           Data.List                 (isSuffixOf)
import qualified Data.Map                  as M
import           Data.Maybe                (fromMaybe, listToMaybe)
import           Data.Semigroup
import qualified Data.Traversable          as T
import           Data.Tree

import           Data.Monoid.Action
import           Data.Monoid.Coproduct
import           Data.Monoid.Deletable
import           Data.Monoid.MList
import           Data.Monoid.WithSemigroup
import qualified Data.Tree.DUAL            as D

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

import           Control.Applicative       hiding (empty)
import           Data.Foldable             (Foldable)
import           Data.Traversable

-- XXX TODO: add lots of actual diagrams to illustrate the
-- documentation!  Haddock supports \<\<inline image urls\>\>.

-- | Class of numbers that are 'RealFloat' and 'Typeable'.
class (RealFloat n, Typeable n) => TypeableFloat n
instance (RealFloat n, Typeable n) => TypeableFloat n
-- use class instead of type constaint so users don't need constraint kinds pragma

-- | Class of numbers that are 'RealFloat', 'Typeable' and 'Data'.
class (TypeableFloat n, Data n) => DataFloat n
instance (TypeableFloat n, Typeable n, Data n) => DataFloat n

------------------------------------------------------------
--  Measurement Units  -------------------------------------
------------------------------------------------------------
-- | Type of measurement units for attributes.
data Measure n = Output n
               | Normalized n
               | Local n
               | Global n

               | MinM (Measure n) (Measure n)
               | MaxM (Measure n) (Measure n)
               | ZeroM
               | PlusM (Measure n) (Measure n)
  deriving (Typeable, Functor, Foldable, Traversable)

deriving instance (Eq n)               => Eq (Measure n)
deriving instance (Ord n)              => Ord (Measure n)
deriving instance (Show n)             => Show (Measure n)
deriving instance (Typeable n, Data n) => Data (Measure n)

-- Bogus applicative instance for Additive class (liftU2, liftI2). Not sure if 
-- there's a better way.
instance Applicative Measure where
  pure = Output

  Output w     <*> m2 = fmap w m2
  Normalized w <*> m2 = fmap w m2
  Local w      <*> m2 = fmap w m2
  Global w     <*> m2 = fmap w m2
  PlusM w1 w2  <*> m2 = PlusM (w1 <*> m2) (w2 <*> m2)
  MinM w1 w2   <*> m2 = MinM (w1 <*> m2) (w2 <*> m2)
  MaxM w1 w2   <*> m2 = MaxM (w1 <*> m2) (w2 <*> m2)
  ZeroM        <*> _  = ZeroM

instance Additive Measure where
  zero = ZeroM

  ZeroM ^+^ m     = m
  m     ^+^ ZeroM = m
  m1    ^+^ m2    = PlusM m1 m2

-- | Scale a measure. Only Local units are scaled.
scaleLocal :: Num n => n -> Measure n -> Measure n
scaleLocal s m = case m of
  Local x     -> Local (s * x)
  PlusM m1 m2 -> PlusM (scaleLocal s m1) (scaleLocal s m2)
  MinM m1 m2  -> MinM (scaleLocal s m1) (scaleLocal s m2)
  MaxM m1 m2  -> MaxM (scaleLocal s m1) (scaleLocal s m2)
  y           -> y

-- | Extract a measure using the given global and normalized scales.
fromMeasure :: (Num n, Ord n) => n -> n -> Measure n -> n
fromMeasure g n m =
  case m of
    Output s     -> s
    Local s      -> s
    Global s     -> g * s
    Normalized s -> n * s

    PlusM m1 m2  -> fromMeasure g n m1 + fromMeasure g n m2
    MinM m1 m2   -> min (fromMeasure g n m1) (fromMeasure g n m2)
    MaxM m1 m2   -> max (fromMeasure g n m1) (fromMeasure g n m2)
    ZeroM        -> 0

-- | Compute the larger of two 'Measure's.  Useful for setting lower
--   bounds.
atLeast :: Measure n -> Measure n -> Measure n
atLeast = MaxM

-- | Compute the smaller of two 'Measure's.  Useful for setting upper
--   bounds.
atMost :: Measure n -> Measure n -> Measure n
atMost = MinM

type instance V (Measure n) = Measure
type instance N (Measure n) = n

-- | Retrieve the 'Output' value of a 'Measure v' or throw an exception.
--   Only 'Ouput' measures should be left in the 'RTree' passed to the backend.
fromOutput :: Measure n -> n
fromOutput (Output w)     = w
fromOutput (Normalized _) = fromOutputErr "Normalized"
fromOutput (Local _)      = fromOutputErr "Local"
fromOutput (Global _)     = fromOutputErr "Global"
fromOutput (MinM _ _)     = fromOutputErr "MinM"
fromOutput (MaxM _ _)     = fromOutputErr "MaxM"
fromOutput (ZeroM)        = fromOutputErr "ZeroM"
fromOutput (PlusM _ _)    = fromOutputErr "PlusM"

fromOutputErr :: String -> a
fromOutputErr s = error $ "fromOutput: Cannot pass " ++ s ++ " to backends, must be Output."


--   Eventually we may use a GADT like:
--
--     data Measure o v where
--       Output     :: Scalar v -> Measure O v
--       Normalized :: Scalar v -> Measure A v
--       Global     :: Scalar v -> Measure A v
--       Local      :: Scale v  -> Measure A v
--
--   to check this at compile time. But for now we throw a runtime error.
--
--   [BAY 4 April 2014] I tried switching to such a GADT.  One tricky
--   bit is that you have to use Output :: Scalar v -> Measure o v,
--   not Measure O v: the reason is that operations like addition have
--   to take two values of the same type, so in order to be able to
--   add Output to something else, Output must be able to have an A
--   annotation.  That all works fine.  The problem is with gmapAttrs,
--   which has to preserve type: so we can't generically convert from
--   Measure A to Measure O.

--   How about using 
--
--     fromOutput = fromMeasure 100 100
--
--   you avoid the runtime error and can say 'Normalized' and 'Global' units 
--   are guessed.
--

------------------------------------------------------------
--  Diagrams  ----------------------------------------------
------------------------------------------------------------

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
type UpAnnots b v n m = Deletable (Envelope v n)
                  ::: Deletable (Trace v n)
                  ::: Deletable (SubMap b v n m)
                  ::: Query v n m
                  ::: ()

-- | Monoidal annotations which travel down the diagram tree,
--   /i.e./ which accumulate along each path to a leaf (and which can
--   act on the upwards-travelling annotations):
--
--   * styles (see "Diagrams.Core.Style")
--
--   * names (see "Diagrams.Core.Names")
type DownAnnots v n = (Transformation v n :+: Style v n)
                ::: Name
                ::: ()

  -- Note that we have to put the transformations and styles together
  -- using a coproduct because the transformations can act on the
  -- styles.

-- | Inject a transformation into a default downwards annotation
--   value.
transfToAnnot :: Transformation v n -> DownAnnots v n
transfToAnnot
  = inj
  . (inL :: Transformation v n -> Transformation v n :+: Style v n)

-- | Extract the (total) transformation from a downwards annotation
--   value.
transfFromAnnot :: (Num n, HasLinearMap v) => DownAnnots v n -> Transformation v n
transfFromAnnot = option mempty killR . fst

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
  deriving (Functor)

withQDiaLeaf :: (Prim b v n -> r)
            -> ((DownAnnots v n -> n -> n -> QDiagram b v n m) -> r)
            -> QDiaLeaf b v n m -> r
withQDiaLeaf f _ (PrimLeaf p)    = f p
withQDiaLeaf _ g (DelayedLeaf dgn) = g dgn

-- | Static annotations which can be placed at a particular node of a
--   diagram tree.
data Annotation
  = Href String    -- ^ Hyperlink
  deriving Show

-- | Apply a static annotation at the root of a diagram.
applyAnnotation
  :: (HasLinearMap v, Metric v, OrderedField n, Semigroup m)
  => Annotation -> QDiagram b v n m -> QDiagram b v n m
applyAnnotation an (QD dt) = QD (D.annot an dt)

-- | Make a diagram into a hyperlink.  Note that only some backends
--   will honor hyperlink annotations.
href :: (HasLinearMap v, Metric v, OrderedField n, Semigroup m)
  => String -> QDiagram b v n m -> QDiagram b v n m
href = applyAnnotation . Href

-- | The fundamental diagram type.  The type variables are as follows:
--
--   * @b@ represents the backend, such as @SVG@ or @Cairo@.  Note
--     that each backend also exports a type synonym @B@ for itself,
--     so the type variable @b@ may also typically be instantiated by
--     @B@, meaning \"use whatever backend is in scope\".
--
--   * @v@ represents the vector space of the diagram.  Typical
--     instantiations include @R2@ (for a two-dimensional diagram) or
--     @R3@ (for a three-dimensional diagram).
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
  = QD (D.DUALTree (DownAnnots v n) (UpAnnots b v n m) Annotation (QDiaLeaf b v n m))
  deriving Typeable

instance Wrapped (QDiagram b v n m) where
  type Unwrapped (QDiagram b v n m) =
        D.DUALTree (DownAnnots v n) (UpAnnots b v n m) Annotation (QDiaLeaf b v n m)
  _Wrapped' = iso (\(QD d) -> d) QD

instance Rewrapped (QDiagram b v n m) (QDiagram b' v' n' m')

type instance V (QDiagram b v n m) = v
type instance N (QDiagram b v n m) = n

-- | @Diagram b v n@ is a synonym for @'QDiagram' b v n 'Any'@.  That is,
--   the default sort of diagram is one where querying at a point
--   simply tells you whether the diagram contains that point or not.
--   Transforming a default diagram into one with a more interesting
--   query can be done via the 'Functor' instance of @'QDiagram' b@ or
--   the 'value' function.
type Diagram b v n = QDiagram b v n Any

-- | Create a \"point diagram\", which has no content, no trace, an
--   empty query, and a point envelope.
pointDiagram :: (Metric v, Fractional n)
             => Point v n -> QDiagram b v n m
pointDiagram p = QD $ D.leafU (inj . toDeletable $ pointEnvelope p)

-- | A useful variant of 'getU' which projects out a certain
--   component.
getU' :: (Monoid u', u :>: u') => D.DUALTree d u a l -> u'
getU' = maybe mempty (option mempty id . get) . D.getU

-- | Get the envelope of a diagram.
envelope :: forall b v n m. ( OrderedField n, Metric v
                            , HasLinearMap v, Monoid' m)
         => Lens' (QDiagram b v n m) (Envelope v n)
envelope = lens (unDelete . getU' . view _Wrapped') (flip setEnvelope)

-- | Replace the envelope of a diagram.
setEnvelope :: forall b v n m. ( OrderedField n, Metric v
                               , HasLinearMap v, Monoid' m)
          => Envelope v n -> QDiagram b v n m -> QDiagram b v n m
setEnvelope e =
    over _Wrapped' ( D.applyUpre (inj . toDeletable $ e)
                . D.applyUpre (inj (deleteL :: Deletable (Envelope v n)))
                . D.applyUpost (inj (deleteR :: Deletable (Envelope v n)))
              )

-- | Get the trace of a diagram.
trace :: (Metric v, HasLinearMap v, OrderedField n, Semigroup m) =>
         Lens' (QDiagram b v n m) (Trace v n)
trace = lens (unDelete . getU' . view _Wrapped') (flip setTrace)

-- | Replace the trace of a diagram.
setTrace :: forall b v n m. ( OrderedField n, Metric v
                            , HasLinearMap v, Semigroup m)
         => Trace v n -> QDiagram b v n m -> QDiagram b v n m
setTrace t = over _Wrapped' ( D.applyUpre (inj . toDeletable $ t)
                         . D.applyUpre (inj (deleteL :: Deletable (Trace v n)))
                         . D.applyUpost (inj (deleteR :: Deletable (Trace v n)))
                       )

-- | Get the subdiagram map (/i.e./ an association from names to
--   subdiagrams) of a diagram.
subMap :: (HasLinearMap v, Metric v, Semigroup m, OrderedField n)
       => Lens' (QDiagram b v n m) (SubMap b v n m)
subMap = lens (unDelete . getU' . view _Wrapped') (flip setMap)
  where
    setMap :: (HasLinearMap v, Metric v, Semigroup m, OrderedField n) =>
              SubMap b v n m -> QDiagram b v n m -> QDiagram b v n m
    setMap m = over _Wrapped' ( D.applyUpre . inj . toDeletable $ m)

-- | Get a list of names of subdiagrams and their locations.
names :: (HasLinearMap v, Metric v, Semigroup m, OrderedField n)
      => QDiagram b v n m -> [(Name, [Point v n])]
names = (map . second . map) location . M.assocs . view (subMap . _Wrapped')

-- | Attach an atomic name to a certain subdiagram, computed from the
--   given diagram /with the mapping from name to subdiagram
--   included/.  The upshot of this knot-tying is that if @d' = d #
--   named x@, then @lookupName x d' == Just d'@ (instead of @Just
--   d@).
nameSub :: ( IsName nm
           , HasLinearMap v, Metric v, OrderedField n, Semigroup m)
        => (QDiagram b v n m -> Subdiagram b v n m) -> nm -> QDiagram b v n m -> QDiagram b v n m
nameSub s n d = d'
  where d' = over _Wrapped' (D.applyUpre . inj . toDeletable $ fromNames [(n,s d')]) d

-- | Lookup the most recent diagram associated with (some
--   qualification of) the given name.
lookupName :: (IsName nm, HasLinearMap v, Metric v, Semigroup m, OrderedField n)
           => nm -> QDiagram b v n m -> Maybe (Subdiagram b v n m)
lookupName n d = lookupSub (toName n) (d^.subMap) >>= listToMaybe

-- | Given a name and a diagram transformation indexed by a
--   subdiagram, perform the transformation using the most recent
--   subdiagram associated with (some qualification of) the name,
--   or perform the identity transformation if the name does not exist.
withName :: (IsName nm, HasLinearMap v, Metric v
            , Semigroup m, OrderedField n)
         => nm -> (Subdiagram b v n m -> QDiagram b v n m -> QDiagram b v n m)
         -> QDiagram b v n m -> QDiagram b v n m
withName n f d = maybe id f (lookupName n d) d

-- | Given a name and a diagram transformation indexed by a list of
--   subdiagrams, perform the transformation using the
--   collection of all such subdiagrams associated with (some
--   qualification of) the given name.
withNameAll :: (IsName nm, HasLinearMap v, Metric v
               , Semigroup m, OrderedField n)
            => nm -> ([Subdiagram b v n m] -> QDiagram b v n m -> QDiagram b v n m)
            -> QDiagram b v n m -> QDiagram b v n m
withNameAll n f d = f (fromMaybe [] (lookupSub (toName n) (d^.subMap))) d

-- | Given a list of names and a diagram transformation indexed by a
--   list of subdiagrams, perform the transformation using the
--   list of most recent subdiagrams associated with (some qualification
--   of) each name.  Do nothing (the identity transformation) if any
--   of the names do not exist.
withNames :: (IsName nm, HasLinearMap v, Metric v
             , Semigroup m, OrderedField n)
          => [nm] -> ([Subdiagram b v n m] -> QDiagram b v n m -> QDiagram b v n m)
          -> QDiagram b v n m -> QDiagram b v n m
withNames ns f d = maybe id f ns' d
  where
    nd = d^.subMap
    ns' = T.sequence (map ((listToMaybe=<<) . ($ nd) . lookupSub . toName) ns)

-- | \"Localize\" a diagram by hiding all the names, so they are no
--   longer visible to the outside.
localize :: forall b v n m. ( HasLinearMap v, Metric v
                          , OrderedField n, Semigroup m
                          )
         => QDiagram b v n m -> QDiagram b v n m
localize = over _Wrapped' ( D.applyUpre  (inj (deleteL :: Deletable (SubMap b v n m)))
                   . D.applyUpost (inj (deleteR :: Deletable (SubMap b v n m)))
                   )


-- | Get the query function associated with a diagram.
query :: Monoid m => QDiagram b v n m -> Query v n m
query = getU' . view _Wrapped'

-- | Sample a diagram's query function at a given point.
sample :: Monoid m => QDiagram b v n m -> Point v n -> m
sample = runQuery . query

-- | Set the query value for 'True' points in a diagram (/i.e./ points
--   \"inside\" the diagram); 'False' points will be set to 'mempty'.
value :: Monoid m => m -> QDiagram b v n Any -> QDiagram b v n m
value m = fmap fromAny
  where fromAny (Any True)  = m
        fromAny (Any False) = mempty

-- | Reset the query values of a diagram to @True@/@False@: any values
--   equal to 'mempty' are set to 'False'; any other values are set to
--   'True'.
resetValue :: (Eq m, Monoid m) => QDiagram b v n m -> QDiagram b v n Any
resetValue = fmap toAny
  where toAny m | m == mempty = Any False
                | otherwise   = Any True

-- | Set all the query values of a diagram to 'False'.
clearValue :: QDiagram b v n m -> QDiagram b v n Any
clearValue = fmap (const (Any False))

-- | Create a diagram from a single primitive, along with an envelope,
--   trace, subdiagram map, and query function.
mkQD :: Prim b v n -> Envelope v n -> Trace v n -> SubMap b v n m -> Query v n m
     -> QDiagram b v n m
mkQD p = mkQD' (PrimLeaf p)

-- | Create a diagram from a generic QDiaLeaf, along with an envelope,
--   trace, subdiagram map, and query function.
mkQD' :: QDiaLeaf b v n m -> Envelope v n -> Trace v n -> SubMap b v n m -> Query v n m
      -> QDiagram b v n m
mkQD' l e t n q
  = QD $ D.leaf (toDeletable e *: toDeletable t *: toDeletable n *: q *: ()) l

------------------------------------------------------------
--  Instances
------------------------------------------------------------

---- Monoid

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
instance (HasLinearMap v, Metric v, OrderedField n, Semigroup m)
  => Monoid (QDiagram b v n m) where
  mempty  = QD D.empty
  mappend = (<>)

instance (HasLinearMap v, Metric v, OrderedField n, Semigroup m)
  => Semigroup (QDiagram b v n m) where
  (QD d1) <> (QD d2) = QD (d2 <> d1)
    -- swap order so that primitives of d2 come first, i.e. will be
    -- rendered first, i.e. will be on the bottom.

-- | A convenient synonym for 'mappend' on diagrams, designed to be
--   used infix (to help remember which diagram goes on top of which
--   when combining them, namely, the first on top of the second).
atop :: (HasLinearMap v, OrderedField n, Metric v, Semigroup m)
     => QDiagram b v n m -> QDiagram b v n m -> QDiagram b v n m
atop = (<>)

infixl 6 `atop`

---- Functor

instance Functor (QDiagram b v n) where
  fmap f = over (_Wrapping QD)
           ( (D.mapU . second . second)
             ( (first . fmap . fmap . fmap)   f
             . (second . first . fmap . fmap) f
             )
           . (fmap . fmap) f
           )

---- Applicative

-- XXX what to do with this?
-- A diagram with queries of result type @(a -> b)@ can be \"applied\"
--   to a diagram with queries of result type @a@, resulting in a
--   combined diagram with queries of result type @b@.  In particular,
--   all components of the two diagrams are combined as in the
--   @Monoid@ instance, except the queries which are combined via
--   @(<*>)@.

-- instance (Backend b v n, Num n, Ord n)
--            => Applicative (QDiagram b v n) where
--   pure a = Diagram mempty mempty mempty (Query $ const a)
-- 
--   (Diagram ps1 bs1 ns1 smp1) <*> (Diagram ps2 bs2 ns2 smp2)
--     = Diagram (ps1 <> ps2) (bs1 <> bs2) (ns1 <> ns2) (smp1 <*> smp2)

---- HasStyle

instance (HasLinearMap v, Metric v, OrderedField n, Semigroup m)
      => HasStyle (QDiagram b v n m) where
  applyStyle = over _Wrapped' . D.applyD . inj
             . (inR :: Style v n -> Transformation v n :+: Style v n)

---- Juxtaposable

instance (HasLinearMap v, Metric v, OrderedField n, Monoid' m)
      => Juxtaposable (QDiagram b v n m) where
  juxtapose = juxtaposeDefault

---- Enveloped

instance (HasLinearMap v, Metric v, OrderedField n, Monoid' m)
         => Enveloped (QDiagram b v n m) where
  getEnvelope = view envelope

---- Traced

instance (HasLinearMap v, Metric v, OrderedField n, Semigroup m)
         => Traced (QDiagram b v n m) where
  getTrace = view trace

---- HasOrigin

-- | Every diagram has an intrinsic \"local origin\" which is the
--   basis for all combining operations.
instance (HasLinearMap v, Metric v, OrderedField n, Semigroup m)
      => HasOrigin (QDiagram b v n m) where
  moveOriginTo = translate . (origin .-.)

---- Transformable

-- | Diagrams can be transformed by transforming each of their
--   components appropriately.
instance (HasLinearMap v, OrderedField n, Metric v, Semigroup m)
      => Transformable (QDiagram b v n m) where
  transform = over _Wrapped' . D.applyD . transfToAnnot

---- Qualifiable

-- | Diagrams can be qualified so that all their named points can
--   now be referred to using the qualification prefix.
instance (HasLinearMap v, Metric v, OrderedField n, Semigroup m)
      => Qualifiable (QDiagram b v n m) where
  (|>) = over _Wrapped' . D.applyD . inj . toName


------------------------------------------------------------
--  Subdiagrams
------------------------------------------------------------

-- | A @Subdiagram@ represents a diagram embedded within the context
--   of a larger diagram.  Essentially, it consists of a diagram
--   paired with any accumulated information from the larger context
--   (transformations, attributes, etc.).

data Subdiagram b v n m = Subdiagram (QDiagram b v n m) (DownAnnots v n)

type instance V (Subdiagram b v n m) = v
type instance N (Subdiagram b v n m) = n

-- | Turn a diagram into a subdiagram with no accumulated context.
mkSubdiagram :: QDiagram b v n m -> Subdiagram b v n m
mkSubdiagram d = Subdiagram d empty

-- | Create a \"point subdiagram\", that is, a 'pointDiagram' (with no
--   content and a point envelope) treated as a subdiagram with local
--   origin at the given point.  Note this is not the same as
--   @mkSubdiagram . pointDiagram@, which would result in a subdiagram
--   with local origin at the parent origin, rather than at the given
--   point.
subPoint :: (HasLinearMap v, Metric v, OrderedField n, Semigroup m)
         => Point v n -> Subdiagram b v n m
subPoint p = Subdiagram
               (pointDiagram origin)
               (transfToAnnot $ translation (p .-. origin))

instance Functor (Subdiagram b v n) where
  fmap f (Subdiagram d a) = Subdiagram (fmap f d) a

instance (OrderedField n, Metric v, HasLinearMap v, Monoid' m)
      => Enveloped (Subdiagram b v n m) where
  getEnvelope (Subdiagram d a) = transform (transfFromAnnot a) $ getEnvelope d

instance (OrderedField n, HasLinearMap v, Metric v, Semigroup m)
      => Traced (Subdiagram b v n m) where
  getTrace (Subdiagram d a) = transform (transfFromAnnot a) $ getTrace d

instance (HasLinearMap v, Metric v, OrderedField n)
      => HasOrigin (Subdiagram b v n m) where
  moveOriginTo = translate . (origin .-.)

instance ( HasLinearMap v, Metric v, Floating n)
    => Transformable (Subdiagram b v n m) where
  transform t (Subdiagram d a) = Subdiagram d (transfToAnnot t <> a)

-- | Get the location of a subdiagram; that is, the location of its
--   local origin /with respect to/ the vector space of its parent
--   diagram.  In other words, the point where its local origin
--   \"ended up\".
location :: (Num n, HasLinearMap v) => Subdiagram b v n m -> Point v n
location (Subdiagram _ a) = transform (transfFromAnnot a) origin

-- | Turn a subdiagram into a normal diagram, including the enclosing
--   context.  Concretely, a subdiagram is a pair of (1) a diagram and
--   (2) a \"context\" consisting of an extra transformation and
--   attributes.  @getSub@ simply applies the transformation and
--   attributes to the diagram to get the corresponding \"top-level\"
--   diagram.
getSub :: ( HasLinearMap v, Metric v
          , Floating n, Ord n
          , Semigroup m
          )
       => Subdiagram b v n m -> QDiagram b v n m
getSub (Subdiagram d a) = over _Wrapped' (D.applyD a) d

-- | Extract the \"raw\" content of a subdiagram, by throwing away the
--   context.
rawSub :: Subdiagram b v n m -> QDiagram b v n m
rawSub (Subdiagram d _) = d

------------------------------------------------------------
--  Subdiagram maps  ---------------------------------------
------------------------------------------------------------

-- | A 'SubMap' is a map associating names to subdiagrams. There can
--   be multiple associations for any given name.
newtype SubMap b v n m = SubMap (M.Map Name [Subdiagram b v n m])
  -- See Note [SubMap Set vs list]

instance Wrapped (SubMap b v n m) where
    type Unwrapped (SubMap b v n m) = M.Map Name [Subdiagram b v n m]
    _Wrapped' = iso (\(SubMap m) -> m) SubMap

instance Rewrapped (SubMap b v n m) (SubMap b' v' n' m')

-- ~~~~ [SubMap Set vs list]
-- In some sense it would be nicer to use
-- Sets instead of a list, but then we would have to put Ord
-- constraints on v everywhere. =P

type instance V (SubMap b v n m) = v
type instance N (SubMap b v n m) = n

instance Functor (SubMap b v n) where
  fmap = over _Wrapped . fmap . map . fmap

instance Semigroup (SubMap b v n m) where
  SubMap s1 <> SubMap s2 = SubMap $ M.unionWith (++) s1 s2

-- | 'SubMap's form a monoid with the empty map as the identity, and
--   map union as the binary operation.  No information is ever lost:
--   if two maps have the same name in their domain, the resulting map
--   will associate that name to the concatenation of the information
--   associated with that name.
instance Monoid (SubMap b v n m) where
  mempty  = SubMap M.empty
  mappend = (<>)

instance (OrderedField n, Metric v, HasLinearMap v)
      => HasOrigin (SubMap b v n m) where
  moveOriginTo = over _Wrapped' . moveOriginTo

instance (Metric v, Floating n, HasLinearMap v)
  => Transformable (SubMap b v n m) where
  transform = over _Wrapped' . transform

-- | 'SubMap's are qualifiable: if @ns@ is a 'SubMap', then @a |>
--   ns@ is the same 'SubMap' except with every name qualified by
--   @a@.
instance Qualifiable (SubMap b v n m) where
  a |> (SubMap m) = SubMap $ M.mapKeys (a |>) m

-- | Construct a 'SubMap' from a list of associations between names
--   and subdiagrams.
fromNames :: IsName a => [(a, Subdiagram b v n m)] -> SubMap b v n m
fromNames = SubMap . M.fromListWith (++) . map (toName *** (:[]))

-- | Add a name/diagram association to a submap.
rememberAs :: IsName a => a -> QDiagram b v n m -> SubMap b v n m -> SubMap b v n m
rememberAs n b = over _Wrapped' $ M.insertWith (++) (toName n) [mkSubdiagram b]

-- | A name acts on a name map by qualifying every name in it.
instance Action Name (SubMap b v n m) where
  act = (|>)

instance Action Name a => Action Name (Deletable a) where
  act n (Deletable l a r) = Deletable l (act n a) r

-- Names do not act on other things.

instance Action Name (Query v n m)
instance Action Name (Envelope v n)
instance Action Name (Trace v n)

-- | Look for the given name in a name map, returning a list of
--   subdiagrams associated with that name.  If no names match the
--   given name exactly, return all the subdiagrams associated with
--   names of which the given name is a suffix.
lookupSub :: IsName nm => nm -> SubMap b v n m -> Maybe [Subdiagram b v n m]
lookupSub a (SubMap m)
  = M.lookup n m `mplus`
    (flattenNames . filter ((n `nameSuffixOf`) . fst) . M.assocs $ m)
  where (Name n1) `nameSuffixOf` (Name n2) = n1 `isSuffixOf` n2
        flattenNames [] = Nothing
        flattenNames xs = Just . concatMap snd $ xs
        n = toName a

------------------------------------------------------------
--  Primitives  --------------------------------------------
------------------------------------------------------------

-- $prim
-- Ultimately, every diagram is essentially a tree whose leaves are /primitives/,
-- basic building blocks which can be rendered by backends.  However,
-- not every backend must be able to render every type of primitive;
-- the collection of primitives a given backend knows how to render is
-- determined by instances of 'Renderable'.

-- | A value of type @Prim b v n@ is an opaque (existentially quantified)
--   primitive which backend @b@ knows how to render in vector space @v@.
data Prim b v n where
  Prim :: (Transformable p, Typeable p, Renderable p b) => p -> Prim b (V p) (N p)

type instance V (Prim b v n) = v
type instance N (Prim b v n) = n

-- | The 'Transformable' instance for 'Prim' just pushes calls to
--   'transform' down through the 'Prim' constructor.
instance HasLinearMap v => Transformable (Prim b v n) where
  transform v (Prim p) = Prim (transform v p)

-- | The 'Renderable' instance for 'Prim' just pushes calls to
--   'render' down through the 'Prim' constructor.
instance HasLinearMap v => Renderable (Prim b v n) b where
  render b (Prim p) = render b p

------------------------------------------------------------
-- Backends  -----------------------------------------------
------------------------------------------------------------

data DNode b v n a = DStyle (Style v n)
                 | DTransform (Transformation v n)
                 | DAnnot a
                 | DDelay
                   -- ^ @DDelay@ marks a point where a delayed subtree
                   --   was expanded.  Such subtrees already take all
                   --   non-frozen transforms above them into account,
                   --   so when later processing the tree, upon
                   --   encountering a @DDelay@ node we must drop any
                   --   accumulated non-frozen transformation.
                 | DPrim (Prim b v n)
                 | DEmpty

-- | A 'DTree' is a raw tree representation of a 'QDiagram', with all
--   the @u@-annotations removed.  It is used as an intermediate type
--   by diagrams-core; backends should not need to make use of it.
--   Instead, backends can make use of 'RTree', which 'DTree' gets
--   compiled and optimized to.
type DTree b v n a = Tree (DNode b v n a)

data RNode b v n a = RStyle (Style v n) -- ^ A style node.
                   | RAnnot a
                   | RPrim (Prim b v n) -- ^ A primitive.
                   | REmpty

-- | An 'RTree' is a compiled and optimized representation of a
--   'QDiagram', which can be used by backends.  They have the
--   following invariant which backends may rely upon:
--
--   * @RPrim@ nodes never have any children.
type RTree b v n a = Tree (RNode b v n a)

-- | Abstract diagrams are rendered to particular formats by
--   /backends/.  Each backend/vector space combination must be an
--   instance of the 'Backend' class.
--
--   A minimal complete definition consists of 'Render', 'Result',
--   'Options', and 'renderRTree'. However, most backends will want to
--   implement 'adjustDia' as well; the default definition does
--   nothing.  Some useful standard definitions are provided in the
--   @Diagrams.TwoD.Adjust@ module from the @diagrams-lib@ package.
class HasLinearMap v => Backend b v n where

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
  adjustDia :: (Monoid' m, Num n) => b -> Options b v n
            -> QDiagram b v n m -> (Options b v n, Transformation v n, QDiagram b v n m)
  adjustDia _ o d = (o,mempty,d)

  -- | Given some options, take a representation of a diagram as a
  --   tree and render it.  The 'RTree' has already been simplified
  --   and has all measurements converted to @Output@ units.
  renderRTree :: b -> Options b v n -> RTree b v n Annotation -> Result b v n

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
--   ghci> width (image \"foo.png\" 200 200)
--   \<interactive\>:8:8:
--       No instance for (Renderable Diagrams.TwoD.Image.Image b0)
--         arising from a use of `image'
--       Possible fix:
--         add an instance declaration for
--         (Renderable Diagrams.TwoD.Image.Image b0)
--       In the first argument of `width', namely
--         `(image \"foo.png\" 200 200)'
--       In the expression: width (image \"foo.png\" 200 200)
--       In an equation for `it': it = width (image \"foo.png\" 200 200)
--   @
--
--   GHC complains that there is no instance for @Renderable Image
--   b0@; what is really going on is that it does not have enough
--   information to decide what backend to use (hence the
--   uninstantiated @b0@). This is annoying because /we/ know that the
--   choice of backend cannot possibly affect the width of the image
--   (it's 200! it's right there in the code!); /but/ there is no way
--   for GHC to know that.
--
--   The solution is to annotate the call to 'image' with the type
--   @'D' 'R2'@, like so:
--
--   @
--   ghci> width (image \"foo.png\" 200 200 :: D R2)
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
--   \<interactive\>:4:1:
--       Couldn't match type `V a0' with `R2'
--       In the expression: width (circle 1)
--       In an equation for `it': it = width (circle 1)
--   @
--
--   There's even more ambiguity here.  Whereas 'image' always returns
--   a 'Diagram', the 'circle' function can produce any 'PathLike'
--   type, and the 'width' function can consume any 'Enveloped' type,
--   so GHC has no idea what type to pick to go in the middle.
--   However, the solution is the same:
--
--   @
--   ghci> width (circle 1 :: D R2)
--   1.9999999999999998
--   @

type D v n = Diagram NullBackend v n


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

instance HasLinearMap v => Backend NullBackend v n where
  data Render NullBackend v n = NullBackendRender
  type Result NullBackend v n = ()
  data Options NullBackend v n

  renderRTree _ _ _ = ()

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
