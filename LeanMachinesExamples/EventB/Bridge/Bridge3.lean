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

structure Bridge3 (ctx : Context)  extends (Bridge2 ctx)  where
  ML_OUT_SR : Sensor
  ML_IN_SR : Sensor
  IL_OUT_SR : Sensor
  IL_IN_SR : Sensor
  A : Natural
  B : Natural
  C : Natural
  ml_out_10 : Bool
  ml_in_10 : Bool
  il_out_10 : Bool
  il_in_10 : Bool

-- page 60 à 71
def Bridge3.invariant_12 (b : Bridge3 ctx) :=
  b.IL_IN_SR = Sensor.On → b.A > 0
def Bridge3.invariant_13 (b : Bridge3 ctx) :=
  b.IL_OUT_SR = Sensor.On → b.B > 0
def Bridge3.invariant_14 (b : Bridge3 ctx) :=
  b.ML_IN_SR = Sensor.On → b.C > 0

def Bridge3.invariant_15 (b : Bridge3 ctx) :=
  b.ml_out_10 → b.mainlandTL = Color.Green
def Bridge3.invariant_16 (b : Bridge3 ctx) :=
  b.il_out_10 → b.islandTL = Color.Green

def Bridge3.invariant_17 (b : Bridge3 ctx) :=
  b.IL_IN_SR = Sensor.On → not b.il_in_10
def Bridge3.invariant_18 (b : Bridge3 ctx) :=
  b.IL_OUT_SR = Sensor.On → not b.il_out_10
def Bridge3.invariant_19 (b : Bridge3 ctx) :=
  b.ML_IN_SR = Sensor.On → not b.ml_in_10
def Bridge3.invariant_20 (b : Bridge3 ctx) :=
  b.ML_OUT_SR = Sensor.On → not b.ml_out_10

def Bridge3.invariant_21 (b : Bridge3 ctx) :=
  b.il_in_10 ∧ b.ml_out_10 → b.A = b.nbToIsland
def Bridge3.invariant_22 (b : Bridge3 ctx) :=
  not b.il_in_10 ∧ b.ml_out_10 → b.A = b.nbToIsland + 1
def Bridge3.invariant_23 (b : Bridge3 ctx) :=
  b.il_in_10 ∧ not b.ml_out_10 → b.A = b.nbToIsland - 1
def Bridge3.invariant_24 (b : Bridge3 ctx) :=
  not b.il_in_10 ∧ not b.ml_out_10 → b.A = b.nbToIsland

def Bridge3.invariant_25 (b : Bridge3 ctx) :=
  b.il_in_10 ∧ b.il_out_10 → b.B = b.nbOnIsland
def Bridge3.invariant_26 (b : Bridge3 ctx) :=
  b.il_in_10 ∧ not b.il_out_10 →  b.B = b.nbOnIsland + 1
def Bridge3.invariant_27 (b : Bridge3 ctx) :=
  not b.il_in_10 ∧ b.il_out_10 → b.B = b.nbOnIsland - 1
def Bridge3.invariant_28 (b : Bridge3 ctx) :=
  not b.il_in_10 ∧ not b.il_out_10 → b.B = b.nbOnIsland


def Bridge3.invariant_29 (b : Bridge3 ctx) :=
  b.il_out_10 ∧ b.ml_in_10 → b.C = b.nbFromIsland
def Bridge3.invariant_30 (b : Bridge3 ctx) :=
  b.il_out_10 ∧ not b.ml_in_10 →  b.C = b.nbFromIsland + 1
def Bridge3.invariant_31 (b : Bridge3 ctx) :=
  not b.il_out_10 ∧ b.ml_in_10 →  b.C = b.nbFromIsland - 1
def Bridge3.invariant_32 (b : Bridge3 ctx) :=
  not b.il_out_10 ∧ not b.ml_in_10 → b.C = b.nbFromIsland

def Bridge3.invariant_33 (b : Bridge3 ctx) :=
  b.A = 0 ∨ b.C = 0
def Bridge3.invariant_34 (b : Bridge3 ctx) :=
  b.A  + b.B + b.C ≤ ctx.maxCars


def EnterFromMainland₁ : OrdinaryREvent (Bridge2 ctx) (Bridge3 ctx) Unit Unit :=
  newREvent'' Bridge1.EnterFromMainland.toOrdinaryEvent {
    guard := fun b3 =>  b3.nbOnIsland + b3.nbToIsland + 1 ≠ ctx.maxCars

    safety := sorry

    action := sorry

    strengthening := sorry

    simulation := sorry


}
