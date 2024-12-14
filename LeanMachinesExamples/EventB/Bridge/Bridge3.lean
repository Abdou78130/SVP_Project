import Mathlib.Tactic

import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Convergent
import LeanMachines.Refinement.Relational.Abstract

import LeanMachinesExamples.EventB.Bridge.Bridge1
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
  A : Nat
  B : Nat
  C : Nat
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

  /-- Refine invariant-/
def Bridge3.refine (b2 : Bridge2 ctx) (b3 : Bridge3 ctx) :=
  b3.toBridge2 = b2 -- this is a superposition

instance: Machine Context (Bridge3 ctx) where
  context := ctx
  invariant b := Bridge3.invariant_12 b ∧ Bridge3.invariant_13 b ∧ Bridge3.invariant_14 b
                 ∧ Bridge3.invariant_15 b ∧ Bridge3.invariant_16 b ∧ Bridge3.invariant_17 b
                 ∧ Bridge3.invariant_18 b ∧ Bridge3.invariant_19 b ∧ Bridge3.invariant_20 b
                 ∧ Bridge3.invariant_21 b ∧ Bridge3.invariant_22 b ∧ Bridge3.invariant_23 b
                 ∧ Bridge3.invariant_24 b ∧ Bridge3.invariant_25 b ∧ Bridge3.invariant_26 b
                 ∧ Bridge3.invariant_27 b ∧ Bridge3.invariant_28 b ∧ Bridge3.invariant_29 b
                 ∧ Bridge3.invariant_30 b ∧ Bridge3.invariant_31 b ∧ Bridge3.invariant_32 b
                 ∧ Bridge3.invariant_33 b ∧ Bridge3.invariant_34 b
                 ∧ Machine.invariant b.toBridge2
                   -- this is handy in case of superposition, instead of putting the
                   -- glue in the refine predicate
  reset := let r1 : Bridge2 ctx := Machine.reset
           { r1 with  ML_OUT_SR := Sensor.Off
                      ML_IN_SR := Sensor.Off
                      IL_OUT_SR := Sensor.Off
                      IL_IN_SR := Sensor.Off
                      A := (0:Nat)
                      B := (0:Nat)
                      C := (0:Nat)
                      ml_out_10 := false
                      ml_in_10 := false
                      il_out_10 := false
                      il_in_10 := false }

instance: Refinement (Bridge2 ctx) (Bridge3 ctx) where
  refine := Bridge3.refine
  refine_safe := fun b2 b3 => by
    simp [Bridge3.refine] -- trivial in case of superposition
    intros Hinv Href
    simp [Machine.invariant] at *
    simp [←Href, Hinv]


def EnterFromMainland₁ : OrdinaryREvent (Bridge2 ctx) (Bridge3 ctx) Unit Unit :=
  newREvent'' Bridge2.EnterFromMainland₁.toOrdinaryEvent {

    guard := fun b3 =>  b3.ml_out_10 ∧ b3.nbOnIsland + b3.nbToIsland + 1 ≠ ctx.maxCars

    action := sorry

    safety := sorry

    strengthening := sorry

    simulation := sorry

}

def EnterFromMainland₂ : OrdinaryREvent (Bridge2 ctx) (Bridge3 ctx) Unit Unit :=
  newREvent'' Bridge2.EnterFromMainland₂.toOrdinaryEvent {

    guard := fun b3 =>  b3.ml_out_10 ∧ b3.nbOnIsland + b3.nbToIsland + 1 = ctx.maxCars

    action := sorry

    safety := sorry

    strengthening := sorry

    simulation := sorry

}

def LeaveIsland₁ : ConvergentREvent Nat (Bridge2 ctx) (Bridge3 ctx) Unit Unit :=
  newConvergentREvent'' Bridge2.LeaveIsland₁.toConvergentEvent.toAnticipatedEvent.toOrdinaryEvent {
    guard := fun b3 => b3.il_out_10 ∧ b3.nbOnIsland ≠ 1

    action := sorry

    safety := sorry

    variant := sorry

    convergence := sorry

    strengthening := sorry

    simulation := sorry

}

def LeaveIsland₂ : ConvergentREvent Nat (Bridge2 ctx) (Bridge3 ctx) Unit Unit :=
  newConvergentREvent'' Bridge2.LeaveIsland₂.toConvergentEvent.toAnticipatedEvent.toOrdinaryEvent {
    guard := fun b3 => b3.il_out_10 ∧ b3.nbOnIsland = 1

    action := sorry

    safety := sorry

    variant := sorry

    convergence := sorry

    strengthening := sorry

    simulation := sorry

}

def LeaveToMainland : OrdinaryREvent (Bridge2 ctx) (Bridge3 ctx) Unit Unit :=
  newAbstractREvent Bridge2.LeaveToMainland.toOrdinaryEvent {

        lift := sorry

        lift_ref := sorry

        refine_uniq := sorry

        unlift := sorry

        step_ref := sorry

        step_safe := sorry

}

def EnterIsland : ConvergentREvent Nat (Bridge2 ctx) (Bridge3 ctx) Unit Unit :=
  newAbstractConvergentREvent Bridge2.EnterIsland.toConvergentEvent {

        lift := sorry

        lift_ref := sorry

        refine_uniq := sorry

        unlift := sorry

        step_ref := sorry

        step_safe := sorry

        step_variant := sorry

}

def MailandTLGreen : ConvergentRDetEvent Nat (Bridge2 ctx) (Bridge3 ctx) Unit Unit :=
  newConcreteConvergentREvent'' {
    guard := fun b3 => b3.mainlandTL = Color.Red ∧ b3.nbToIsland + b3.nbOnIsland < ctx.maxCars ∧ b3.nbFromIsland = 0
                      ∧ b3.islandPass = true ∧ b3.il_out_10 = false

    action := sorry

    safety := sorry

    variant := sorry

    convergence := sorry

    simulation := sorry

}

def IslandTLGreen : ConvergentRDetEvent Nat (Bridge2 ctx) (Bridge3 ctx) Unit Unit :=
  newConcreteConvergentREvent'' {
    guard := fun b3 => b3.islandTL = Color.Red ∧ b3.nbOnIsland > 0 ∧ b3.nbToIsland = 0 ∧ b3.mainlandPass = true
                      ∧ b3.ml_out_10 = false

    action := sorry

    safety := sorry

    variant := sorry

    convergence := sorry

    simulation := sorry

}




-- New event

def MainlandOutArr : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b => b.ML_OUT_SR = Sensor.Off ∧ not b.ml_out_10

    action := fun b => {b with ML_OUT_SR := Sensor.On}

    safety := sorry
}

def MainlandInArr : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b => b.ML_IN_SR = Sensor.Off ∧ not b.ml_in_10 ∧ b.C > 0

    action := fun b => {b with ML_IN_SR := Sensor.On}

    safety := sorry
}


def IslandInArr : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard :=  fun b => b.IL_IN_SR = Sensor.Off ∧ not b.il_in_10 ∧ b.A > 0

    action := fun b => {b with IL_IN_SR := Sensor.On}

    safety := sorry
}


def IslandOutArr : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b => b.IL_OUT_SR = Sensor.Off ∧ not b.il_out_10 ∧ b.B > 0
    action := fun b => {b with IL_OUT_SR := Sensor.On}

    safety := sorry
}

def MainlandOutDep : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b => b.ML_OUT_SR = Sensor.On ∧ b.mainlandTL = Color.Green

    action := fun b => {b with IL_OUT_SR := Sensor.Off
                               ml_out_10 := True
                               A := b.A + 1}

    safety := sorry
}

def MainlandInDep : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b => b.ML_IN_SR = Sensor.On

    action := fun b => {b with ML_IN_SR := Sensor.Off
                               ml_in_10 := True
                               C := b.C - 1}

    safety := sorry
}


def IslandInDep : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b => b.IL_IN_SR = Sensor.On

    action := fun b => {b with IL_IN_SR := Sensor.Off
                               il_in_10 := True
                               A := b.A - 1
                               B := b.B + 1}

    safety := sorry
}


def IslandOutDep : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b => b.IL_IN_SR = Sensor.On ∧ b.islandTL = Color.Green

    action := fun b => {b with IL_IN_SR := Sensor.Off
                               il_in_10 := True
                               B := b.B - 1
                               C := b.C + 1}

    safety := sorry
}
