import Mathlib.Tactic

import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Convergent
import LeanMachines.Refinement.Relational.Abstract

import LeanMachinesExamples.EventB.Bridge.Bridge2

/-!

## Third refinement

In the third refinement, il y a l'ajout de sensors aux entrées et sorties de l'île et le continent.


-/

namespace BridgeSpec
inductive Sensor where | On | Off
  deriving Repr, BEq, DecidableEq

structure Bridge3 (ctx : Context) where
  ML_OUT_SR : Sensor
  ML_IN_SR : Sensor
  IL_OUT_SR : Sensor
  IL_IN_SR : Sensor
  /-- Traffic light: from mainland. -/
  mainlandTL : Color
  /-- A flag to allow/disallow cars entering from mainland. -/
  mainlandPass : Bool
  /-- Traffic light: from island. -/
  islandTL : Color
  /-- A flag to allow/disallow cars entering from the island. -/
  islandPass : Bool
