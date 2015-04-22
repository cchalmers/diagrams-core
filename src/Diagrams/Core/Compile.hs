{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE LambdaCase            #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Diagrams.Core.Compile
-- Copyright   :  (c) 2013-2015 diagrams-core team (see LICENSE)
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  diagrams-discuss@googlegroups.com
--
-- This module provides tools for compiling @QDiagrams@ into a more
-- convenient and optimized tree form, suitable for use by backends.
--
-----------------------------------------------------------------------------

module Diagrams.Core.Compile
  ( -- * Tools for backends
    foldDia
  , foldDia'

    -- * Backend API

  , renderDia
  , renderDiaT
  )
  where

import           Data.Monoid.Coproduct
import           Data.Monoid.MList
import           Data.Monoid.WithSemigroup (Monoid')
import           Data.Semigroup
import           Data.Tree.DUAL            (foldDUAL)
import           Data.Typeable
import qualified Data.Foldable as F

import           Diagrams.Core.Envelope    (OrderedField, size)
import           Diagrams.Core.Style
import           Diagrams.Core.Transform
import           Diagrams.Core.Types
import           Diagrams.Core.Style

import           Linear.Metric hiding (qd)

-- Typeable1 is a depreciated synonym in ghc > 707
#if __GLASGOW_HASKELL__ >= 707
#define Typeable1 Typeable
#endif

foldDia' :: (HasLinearMap v, Floating n, Typeable n, Monoid r)
        => (Style v n -> Prim b v n -> r)
        -> (Annotation v n -> r -> r)
        -> n -- 'global' to 'output' scale factor
        -> n -- 'normalised' to 'output' scale factor
        -> QDiagram b v n m -- ^ diagram to fold
        -> r
foldDia' primF aF g n (QD dual) = foldDUAL lF aF dual
  where
    lF d = \case
      PrimLeaf p    ->
        let (tr, sty) = untangle d
        in  primF sty (transform tr p)
      DelayedLeaf f ->
        let (QD dia) = f d g n
        in  foldDUAL lF aF dia

foldDia :: (HasLinearMap v, Metric v, OrderedField n, Typeable n, Monoid' m, Monoid r)
        => (Style v n -> Prim b v n -> r)
        -> (Annotation v n -> r -> r)
        -> Transformation v n
        -> QDiagram b v n m -- ^ diagram to fold
        -> r
foldDia primF annF t d = foldDia' primF annF g n d
  where
    g = avgScale t
    n = normalizedFactor (size d)

-- | Get the normalized scale factor from a vector. For the
--   'normalizedFactor' of a diagram use this with the 'size' of the
--   diagram.
--
--   Note: The 'global' factor is the 'avgScale' of the output
--   transform.
normalizedFactor :: (Foldable v, Floating n) => v n -> n
normalizedFactor v = F.product v ** 1 / fromIntegral (F.length v)

-- | Render a diagram, returning also the transformation which was
--   used to convert the diagram from its (\"global\") coordinate
--   system into the output coordinate system.  The inverse of this
--   transformation can be used, for example, to convert output/screen
--   coordinates back into diagram coordinates.  See also 'adjustDia'.
renderDiaT
  :: (Backend b v n , HasLinearMap v, Metric v, Typeable1 v,
      Typeable n, OrderedField n, Monoid' m)
  => b -> Options b v n -> QDiagram b v n m -> (Transformation v n, Result b v n)
renderDiaT b opts d = (g2o, renderDUAL b opts' g2o d')
  where (opts', g2o, d') = adjustDia b opts d

-- | Render a diagram.
renderDia
  :: (Backend b v n , HasLinearMap v, Metric v, Typeable1 v,
      Typeable n, OrderedField n, Monoid' m)
  => b -> Options b v n -> QDiagram b v n m -> Result b v n
renderDia b opts d = snd (renderDiaT b opts d)

