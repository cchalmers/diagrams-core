-----------------------------------------------------------------------------
-- |
-- Module      :  Diagrams.Core
-- Copyright   :  (c) 2011 diagrams-core team (see LICENSE)
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  diagrams-discuss@googlegroups.com
--
-- The core library of primitives forming the basis of an embedded
-- domain-specific language for describing and rendering diagrams.
-- Normal users of the diagrams library should almost never need to
-- import anything from this package directly; instead, import modules
-- (especially @Diagrams.Prelude@) from the diagrams-lib package,
-- which re-exports most things of value to users.
--
-- For most library code needing access to core internals, it should
-- be sufficient to import this module, which simply re-exports useful
-- functionality from other modules in the core library.  Library
-- writers needing finer-grained access or functionality may
-- occasionally find it useful to directly import one of the
-- constituent core modules.
--
-- The diagrams library relies heavily on custom types and classes. Many
-- of the relevant definitions are in the "Diagrams.Core.Types" module.
-- Indeed the definition of the diagram type @QDiagram@ is contained in:
-- 'Diagrams.Core.Types.QDiagram'. 
--
-- The best place to start when learning
-- about diagrams\' types is the user manual:
-- <http://projects.haskell.org/diagrams/doc/manual.html#type-reference>
-- The following list shows which types are contained in each module of
-- "Diagrams.Core".
--
-- * "Diagrams.Core.Types"
--
--     * @Annotation@, 
--     * @UpAnnots b v m@, @DownAnnots v@,
--     * @QDiaLeaf b v m@, @Measure v@,
--     * @Subdiagram b v m@,  @SubMap b v m@,
--     * @Prim b v@, @Backend b v@, 
--     * @DNode b v a@, @DTree b v a@,
--     * @RNode b v a@, @RTree b v a@,
--     * @NullBackend@, @Renderable t b@,
--     * @D v@.
--
-- * "Diagrams.Core.Envelope"
--
--     * @Envelope v@, @Enveloped v@,
--     * @OrderedField s@.
--
-- * "Diagrams.Core.Juxtapose"
--
--     * @Juxtaposable a@.
--
-- * "Diagrams.Core.Names"
--
--     * @AName@, @Name@, @IsName a@,
--     * @Qualifiable q@.
--
-- * "Diagrams.Core.HasOrigin"
--
--     * @HasOrigin t@.
--
-- * "Diagrams.Core.Points"
--
--     * @Point v@.
--
-- * "Diagrams.Core.Query"
--
--     * @Query v m@.
--
-- *  "Diagrams.Core.Style"
--
--     * @AttributeClass a@, @Attribute v@,
--     * @Style v@, @HasStyle@.
--
-- * "Diagrams.Core.Trace"
--
--     * @SortedList a@,
--     * @Trace v@, @Traced a@.
--
-- * "Diagrams.Core.Transform"
--
--     * @u :-: v@, @HasLinearMap@,
--     * @Transformation v@, @Transformable t@,
--     * @TransInv t@.
--
-- * "Diagrams.Core.V"
--
--     * @V a@.
-----------------------------------------------------------------------------

module Diagrams.Core
       ( -- * Associated vector spaces

         V, N, Vn

         -- * Points

       , Point, origin, (*.)
       , _relative

         -- * Transformations

         -- ** Utilities
       , basis
       , dimension
       , determinant

         -- ** Invertible linear transformations
       , (:-:), (<->), linv, lapp

         -- ** General transformations
       , Transformation
       , inv, transp, transl
       , dropTransl
       , apply
       , papply
       , fromLinear

         -- ** Some specific transformations
       , translation, translate, moveTo, place
       , scaling, scale
       , avgScale

         -- ** The Transformable class

       , Transformable(..)

         -- ** Translational invariance

       , TransInv(TransInv)
       , eye

         -- * Names

       , AName
       , Name, IsName(..)
       , Qualifiable(..), (.>)

         -- ** Subdiagram maps

       , SubMap(..)
       , fromNames
       , rememberAs

       , lookupSub

         -- * Attributes and styles

       , AttributeClass
       , Attribute, mkAttr, mkTAttr, mkGTAttr, unwrapAttr

       , Style, HasStyle(..)
       , getAttr, combineAttr
       , applyAttr, applyTAttr, applyGTAttr

         -- * Envelopes

       , Envelope(..)
       , appEnvelope, onEnvelope, mkEnvelope
       , Enveloped(..)
       , envelopeVMay, envelopeV, envelopePMay, envelopeP
       , diameter, radius, size

         -- * Traces

       , Trace(Trace)
       , SortedList, mkSortedList, getSortedList
       , appTrace, mkTrace
       , Traced(..)
       , traceV, traceP
       , maxTraceV, maxTraceP
       , rayTraceV, rayTraceP
       , maxRayTraceV, maxRayTraceP

         -- * Things with local origins

       , HasOrigin(..), moveOriginBy

         -- * Juxtaposable things

       , Juxtaposable(..), juxtaposeDefault

         -- * Queries

       , Query(..)

         -- * Primtives

       , Prim(..)

         -- * Diagrams

       , QDiagram, Diagram, mkQD, pointDiagram
       , envelope, trace, subMap, names, query, sample
       , value, resetValue, clearValue

       , nameSub
       , withName
       , withNameAll
       , withNames
       , localize

       , href

       , setEnvelope, setTrace

       , atop

         -- ** Subdiagrams

       , Subdiagram(..), mkSubdiagram
       , getSub, rawSub
       , location
       , subPoint

         -- * Measurements
       , Measure(..)
       , fromMeasure
       , fromOutput
       , toOutput
       , atMost
       , atLeast
       , scaleLocal

         -- * Backends

       , Backend(..)
       , Renderable(..)

       , renderDia
       , renderDiaT

         -- ** The null backend

       , NullBackend, D

         -- * Convenience classes

       , HasLinearMap
       , OrderedField
       , TypeableFloat
       , DataFloat
       , Monoid'

       ) where

import           Diagrams.Core.Compile
import           Diagrams.Core.Envelope
import           Diagrams.Core.HasOrigin
import           Diagrams.Core.Juxtapose
import           Diagrams.Core.Names
import           Diagrams.Core.Points
import           Diagrams.Core.Query
import           Diagrams.Core.Style
import           Diagrams.Core.Trace
import           Diagrams.Core.Transform
import           Diagrams.Core.Types
import           Diagrams.Core.V

import           Data.Monoid.WithSemigroup (Monoid')
