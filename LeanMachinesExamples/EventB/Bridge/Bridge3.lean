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

    action := fun b3 =>  {b3 with nbToIsland := b3.nbToIsland + 1
                                  mainlandPass := true
                                  ml_out_10 := false}

    safety := fun b => by
      simp [Machine.invariant,
      Bridge3.invariant_12,
      Bridge3.invariant_13,
      Bridge3.invariant_14,
      Bridge3.invariant_15,
      Bridge3.invariant_16,
      Bridge3.invariant_17,
      Bridge3.invariant_18,
      Bridge3.invariant_19,
      Bridge3.invariant_20,
      Bridge3.invariant_21,
      Bridge3.invariant_22,
      Bridge3.invariant_23,
      Bridge3.invariant_24,
      Bridge3.invariant_25,
      Bridge3.invariant_26,
      Bridge3.invariant_27,
      Bridge3.invariant_28,
      Bridge3.invariant_29,
      Bridge3.invariant_30,
      Bridge3.invariant_31,
      Bridge3.invariant_32,
      Bridge3.invariant_33,
      Bridge3.invariant_34]
      intros  Hinv12 Hinv13 Hinv14 Hinv15 Hinv16 Hinv17
        Hinv18 Hinv19 Hinv20 Hinv21 Hinv22 Hinv23 Hinv24 Hinv25 Hinv26
        Hinv27 Hinv28 Hinv29 Hinv30 Hinv31 Hinv32 Hinv33_phys Hinv34_phys
        Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv33 Hinv34 Hgrd₁ Hgrd₂



    strengthening := sorry

    simulation := sorry

}

def EnterFromMainland₂ : OrdinaryREvent (Bridge2 ctx) (Bridge3 ctx) Unit Unit :=
  newREvent'' Bridge2.EnterFromMainland₂.toOrdinaryEvent {

    guard := fun b3 => b3.ml_out_10 ∧ b3.nbOnIsland + b3.nbToIsland + 1 = ctx.maxCars

    action := fun b3 => {b3 with nbToIsland := b3.nbToIsland + 1
                                 mainlandTL := Color.Red
                                 mainlandPass := true
                                 ml_out_10 := false}

    safety := sorry

    strengthening := sorry

    simulation := sorry

}

def LeaveIsland₁ : ConvergentREvent Nat (Bridge2 ctx) (Bridge3 ctx) Unit Unit :=
  newConvergentREvent'' Bridge2.LeaveIsland₁.toConvergentEvent.toAnticipatedEvent.toOrdinaryEvent {
    guard := fun b3 => b3.il_out_10 ∧ b3.nbOnIsland ≠ 1

    action := fun b3 => {b3 with nbOnIsland := b3.nbOnIsland - 1
                                 nbFromIsland := b3.nbFromIsland + 1
                                 islandPass := true
                                 il_out_10 := false}

    safety := fun b => by
      simp [Machine.invariant,
        Bridge3.invariant_12,
        Bridge3.invariant_13,
        Bridge3.invariant_14,
        Bridge3.invariant_15,
        Bridge3.invariant_16,
        Bridge3.invariant_17,
        Bridge3.invariant_18,
        Bridge3.invariant_19,
        Bridge3.invariant_20,
        Bridge3.invariant_21,
        Bridge3.invariant_22,
        Bridge3.invariant_23,
        Bridge3.invariant_24,
        Bridge3.invariant_25,
        Bridge3.invariant_26,
        Bridge3.invariant_27,
        Bridge3.invariant_28,
        Bridge3.invariant_29,
        Bridge3.invariant_30,
        Bridge3.invariant_31,
        Bridge3.invariant_32,
        Bridge3.invariant_33,
        Bridge3.invariant_34]
      intros  Hinv12 Hinv13 Hinv14 Hinv15 Hinv16 Hinv17
        Hinv18 Hinv19 Hinv20 Hinv21 Hinv22 Hinv23 Hinv24 Hinv25 Hinv26
        Hinv27 Hinv28 Hinv29 Hinv30 Hinv31 Hinv32 Hinv33_phys Hinv34_phys
        Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv33 Hinv34 Hgrd₁ Hgrd₂
      constructor
      exact fun a => Hinv12 a
      case right =>
      constructor
      exact fun a => Hinv13 a
      case right =>
      constructor
      exact fun a => Hinv14 a
      case right =>
      constructor
      exact fun a => Hinv15 a
      case right =>
      constructor
      exact fun a => Hinv17 a
      case right =>
      constructor
      exact fun a => Hinv19 a
      case right =>
      constructor
      exact fun a => Hinv20 a
      case right =>
      constructor
      exact fun a a_1 => Hinv21 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv22 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv23 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv24 a a_1
      case right =>
      constructor
      intro HX
      have HX2 : b.il_out_10 = true → b.B = b.nbOnIsland := by
        exact fun a => Hinv25 HX Hgrd₁
      have HX3 : b.B = b.nbOnIsland := by
        exact Hinv25 HX Hgrd₁
      have HX5 :  b.B = b.nbOnIsland → b.B = b.nbOnIsland + 1 - 1 := by
        exact fun a => Hinv25 HX Hgrd₁
      have HX6 : b.B = b.nbOnIsland + 1 - 1 → b.B = b.nbOnIsland - 1 + 1 := by
        simp_arith [*]
        sorry
      case right =>
      constructor
      exact fun a => Hinv27 a Hgrd₁
      case right =>
      constructor
      exact fun a => Hinv29 Hgrd₁ a
      case right =>
      constructor
      exact fun a => Hinv30 Hgrd₁ a
      case right =>
      constructor
      exact Hinv33_phys
      case right =>
      constructor
      exact Hinv34_phys
      case right =>
      constructor
      sorry



    variant := sorry

    convergence := sorry

    strengthening := sorry

    simulation := sorry

}

def LeaveIsland₂ : ConvergentREvent Nat (Bridge2 ctx) (Bridge3 ctx) Unit Unit :=
  newConvergentREvent'' Bridge2.LeaveIsland₂.toConvergentEvent.toAnticipatedEvent.toOrdinaryEvent {
    guard := fun b3 => b3.il_out_10 ∧ b3.nbOnIsland = 1

    action := fun b3 => {b3 with nbOnIsland := b3.nbOnIsland - 1
                                 nbFromIsland := b3.nbFromIsland + 1
                                 islandTL := Color.Red
                                 islandPass := true
                                 il_out_10 := false
                                 }

    safety := fun b => by
                simp [Machine.invariant,
                  Bridge3.invariant_12,
                  Bridge3.invariant_13,
                  Bridge3.invariant_14,
                  Bridge3.invariant_15,
                  Bridge3.invariant_16,
                  Bridge3.invariant_17,
                  Bridge3.invariant_18,
                  Bridge3.invariant_19,
                  Bridge3.invariant_20,
                  Bridge3.invariant_21,
                  Bridge3.invariant_22,
                  Bridge3.invariant_23,
                  Bridge3.invariant_24,
                  Bridge3.invariant_25,
                  Bridge3.invariant_26,
                  Bridge3.invariant_27,
                  Bridge3.invariant_28,
                  Bridge3.invariant_29,
                  Bridge3.invariant_30,
                  Bridge3.invariant_31,
                  Bridge3.invariant_32,
                  Bridge3.invariant_33,
                  Bridge3.invariant_34]
                intros Hinv12 Hinv13 Hinv14 Hinv15 Hinv16 Hinv17 Hinv18 Hinv19 Hinv20 Hinv21 Hinv22 Hinv23 Hinv24 Hinv25 Hinv26 Hinv27 Hinv28 Hinv29 Hinv30 Hinv31 Hinv32 Hinv33_phys Hinv34_phys Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv33 Hinv34 Hgrd₁ Hgrd₂
                constructor
                exact fun a => Hinv12 a
                case right =>
                constructor
                exact fun a => Hinv13 a
                case right =>
                constructor
                exact fun a => Hinv14 a
                case right =>
                constructor
                exact fun a => Hinv15 a
                case right =>
                constructor
                exact fun a => Hinv17 a
                case right =>
                constructor
                exact fun a => Hinv19 a
                case right =>
                constructor
                exact fun a => Hinv20 a
                case right =>
                constructor
                exact fun a a_1 => Hinv21 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv22 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv23 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv24 a a_1
                case right =>
                constructor
                apply?




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

    action := fun b3 => {b3 with mainlandTL := Color.Green
                                 islandTL := Color.Red
                                 mainlandPass := false
                                 }

    safety := fun b => by
                simp [Machine.invariant,
                  Bridge3.invariant_12,
                  Bridge3.invariant_13,
                  Bridge3.invariant_14,
                  Bridge3.invariant_15,
                  Bridge3.invariant_16,
                  Bridge3.invariant_17,
                  Bridge3.invariant_18,
                  Bridge3.invariant_19,
                  Bridge3.invariant_20,
                  Bridge3.invariant_21,
                  Bridge3.invariant_22,
                  Bridge3.invariant_23,
                  Bridge3.invariant_24,
                  Bridge3.invariant_25,
                  Bridge3.invariant_26,
                  Bridge3.invariant_27,
                  Bridge3.invariant_28,
                  Bridge3.invariant_29,
                  Bridge3.invariant_30,
                  Bridge3.invariant_31,
                  Bridge3.invariant_32,
                  Bridge3.invariant_33,
                  Bridge3.invariant_34]
                intros Hinv12 Hinv13 Hinv14 Hinv15 Hinv16 Hinv17 Hinv18 Hinv19 Hinv20 Hinv21 Hinv22 Hinv23 Hinv24 Hinv25 Hinv26 Hinv27 Hinv28 Hinv29 Hinv30 Hinv31 Hinv32 Hinv33_phys Hinv34_phys Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv33 Hinv34 Hgrd₁ Hgrd₂ H35 H36 H37
                constructor
                exact fun a => Hinv12 a
                case right =>
                constructor
                exact fun a => Hinv13 a
                case right =>
                constructor
                exact fun a => Hinv14 a
                case right =>
                constructor
                exact H37
                case right =>
                constructor
                exact fun a => Hinv17 a
                case right =>
                constructor
                exact fun a => Hinv18 a
                case right =>
                constructor
                exact fun a => Hinv19 a
                case right =>
                constructor
                exact fun a => Hinv20 a
                case right =>
                constructor
                exact fun a a_1 => Hinv21 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv22 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv23 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv24 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv25 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv26 a H37
                case right =>
                constructor
                exact fun a a_1 => Hinv27 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv28 a H37
                case right =>
                constructor
                exact fun a a_1 => Hinv29 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv30 a a_1
                case right =>
                constructor
                exact fun a a => Hinv31 H37 a
                case right =>
                constructor
                exact fun a a => Hinv32 H37 a
                case right =>
                constructor
                exact Hinv33_phys
                case right =>
                constructor
                exact Hinv34_phys

    variant := sorry

    convergence := sorry

    simulation := sorry

}

def IslandTLGreen : ConvergentRDetEvent Nat (Bridge2 ctx) (Bridge3 ctx) Unit Unit :=
  newConcreteConvergentREvent'' {
    guard := fun b3 => b3.islandTL = Color.Red ∧ b3.nbOnIsland > 0 ∧ b3.nbToIsland = 0 ∧ b3.mainlandPass = true
                      ∧ b3.ml_out_10 = false

    action := fun b3 => {b3 with islandTL := Color.Green
                                 mainlandTL := Color.Red
                                 mainlandPass := false
                                 }

    safety := fun b => by
                simp [Machine.invariant,
                  Bridge3.invariant_12,
                  Bridge3.invariant_13,
                  Bridge3.invariant_14,
                  Bridge3.invariant_15,
                  Bridge3.invariant_16,
                  Bridge3.invariant_17,
                  Bridge3.invariant_18,
                  Bridge3.invariant_19,
                  Bridge3.invariant_20,
                  Bridge3.invariant_21,
                  Bridge3.invariant_22,
                  Bridge3.invariant_23,
                  Bridge3.invariant_24,
                  Bridge3.invariant_25,
                  Bridge3.invariant_26,
                  Bridge3.invariant_27,
                  Bridge3.invariant_28,
                  Bridge3.invariant_29,
                  Bridge3.invariant_30,
                  Bridge3.invariant_31,
                  Bridge3.invariant_32,
                  Bridge3.invariant_33,
                  Bridge3.invariant_34]
                intros Hinv12 Hinv13 Hinv14 Hinv15 Hinv16 Hinv17 Hinv18 Hinv19 Hinv20 Hinv21 Hinv22 Hinv23 Hinv24 Hinv25 Hinv26 Hinv27 Hinv28 Hinv29 Hinv30 Hinv31 Hinv32 Hinv33_phys Hinv34_phys Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv33 Hinv34 Hgrd₁ Hgrd₂ H35 H36 H37
                constructor
                exact fun a => Hinv12 a
                case right =>
                constructor
                exact fun a => Hinv13 a
                case right =>
                constructor
                exact fun a => Hinv14 a
                case right =>
                constructor
                exact H37
                case right =>
                constructor
                exact fun a => Hinv17 a
                case right =>
                constructor
                exact fun a => Hinv18 a
                case right =>
                constructor
                exact fun a => Hinv19 a
                case right =>
                constructor
                exact fun a => Hinv20 a
                case right =>
                constructor
                exact fun a a_1 => Hinv21 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv22 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv23 a H37
                case right =>
                constructor
                exact fun a a_1 => Hinv24 a H37
                case right =>
                constructor
                exact fun a a_1 => Hinv25 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv26 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv27 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv28 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv29 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv30 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv31 a a_1
                case right =>
                constructor
                exact fun a a_1 => Hinv32 a a_1
                case right =>
                constructor
                exact Hinv33_phys
                case right =>
                constructor
                exact Hinv34_phys
                case right =>
                constructor
    variant := sorry

    convergence := sorry

    simulation := sorry

}




-- New event

theorem exchange (n : Nat) :
  n > 0 → 0 < n  :=
by
  intro H1
  exact H1


def MainlandOutArr : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b => b.ML_OUT_SR = Sensor.Off ∧ not b.ml_out_10

    action := fun b => {b with ML_OUT_SR := Sensor.On}

    safety := fun b => by
      simp [Machine.invariant,
      Bridge3.invariant_12,
      Bridge3.invariant_13,
      Bridge3.invariant_14,
      Bridge3.invariant_15,
      Bridge3.invariant_16,
      Bridge3.invariant_17,
      Bridge3.invariant_18,
      Bridge3.invariant_19,
      Bridge3.invariant_20,
      Bridge3.invariant_21,
      Bridge3.invariant_22,
      Bridge3.invariant_23,
      Bridge3.invariant_24,
      Bridge3.invariant_25,
      Bridge3.invariant_26,
      Bridge3.invariant_27,
      Bridge3.invariant_28,
      Bridge3.invariant_29,
      Bridge3.invariant_30,
      Bridge3.invariant_31,
      Bridge3.invariant_32,
      Bridge3.invariant_33,
      Bridge3.invariant_34]
      intros Hinv12 Hinv13 Hinv14 Hinv15 Hinv16 Hinv17 Hinv18 Hinv19 Hinv20 Hinv21 Hinv22 Hinv23 Hinv24 Hinv25 Hinv26 Hinv27 Hinv28 Hinv29 Hinv30 Hinv31 Hinv32 Hinv33_phys Hinv34_phys Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv33 Hinv34 Hgrd₁ Hgrd₂
      constructor
      exact fun a => Hinv12 a
      case right =>
      constructor
      exact fun a => Hinv13 a
      case right =>
      constructor
      exact fun a => Hinv14 a
      case right =>
      constructor
      exact fun a => Hinv15 a
      case right =>
      constructor
      exact fun a => Hinv16 a
      case right =>
      constructor
      exact fun a => Hinv17 a
      case right =>
      constructor
      exact fun a => Hinv18 a
      case right =>
      constructor
      exact fun a => Hinv19 a
      case right =>
      constructor
      exact Hgrd₂
      case right =>
      constructor
      exact fun a a_1 => Hinv21 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv22 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv23 a Hgrd₂
      case right =>
      constructor
      exact fun a a_1 => Hinv24 a Hgrd₂
      case right =>
      constructor
      exact fun a a_1 => Hinv25 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv26 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv27 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv28 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv29 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv30 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv31 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv32 a a_1
      case right =>
      constructor
      exact Hinv33_phys
      case right =>
      constructor
      exact Hinv34_phys
      case right =>
      constructor
      exact Hinv₁
      case right =>
      constructor
      exact Hinv₂
      case right =>
      constructor
      exact Hinv₃
      case right =>
      constructor
      exact Hinv₄
      case right =>
      constructor
      exact Hinv₅
      case right =>
      constructor
      exact Hinv33






      -- all_goals (repeat constructor)





}

def MainlandInArr : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b => b.ML_IN_SR = Sensor.Off ∧ not b.ml_in_10 ∧ b.C > 0

    action := fun b => {b with ML_IN_SR := Sensor.On}

    safety := fun b => by
      simp [Machine.invariant,
      Bridge3.invariant_12,
      Bridge3.invariant_13,
      Bridge3.invariant_14,
      Bridge3.invariant_15,
      Bridge3.invariant_16,
      Bridge3.invariant_17,
      Bridge3.invariant_18,
      Bridge3.invariant_19,
      Bridge3.invariant_20,
      Bridge3.invariant_21,
      Bridge3.invariant_22,
      Bridge3.invariant_23,
      Bridge3.invariant_24,
      Bridge3.invariant_25,
      Bridge3.invariant_26,
      Bridge3.invariant_27,
      Bridge3.invariant_28,
      Bridge3.invariant_29,
      Bridge3.invariant_30,
      Bridge3.invariant_31,
      Bridge3.invariant_32,
      Bridge3.invariant_33,
      Bridge3.invariant_34]
      intros Hinv12 Hinv13 Hinv14 Hinv15 Hinv16 Hinv17 Hinv18 Hinv19 Hinv20 Hinv21 Hinv22 Hinv23 Hinv24 Hinv25 Hinv26 Hinv27 Hinv28 Hinv29 Hinv30 Hinv31 Hinv32 Hinv33_phys Hinv34_phys Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv33 Hinv34 Hgrd₁ Hgrd₂ h34
      constructor
      exact fun a => Hinv12 a
      case right =>
      constructor
      exact fun a => Hinv13 a
      case right =>
      constructor
      exact h34
      case right =>
      constructor
      exact fun a => Hinv15 a
      case right =>
      constructor
      exact fun a => Hinv16 a
      case right =>
      constructor
      exact fun a => Hinv17 a
      case right =>
      constructor
      exact fun a => Hinv18 a
      case right =>
      constructor
      exact Hgrd₂
      case right =>
      constructor
      exact fun a => Hinv20 a
      case right =>
      constructor
      exact fun a a_1 => Hinv21 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv22 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv23 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv24 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv25 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv26 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv27 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv28 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv29 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv30 a Hgrd₂
      case right =>
      constructor
      exact fun a a_1 => Hinv31 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv32 a Hgrd₂
      case right =>
      constructor
      exact Hinv33_phys
      case right =>
      constructor
      exact Hinv34_phys
      case right =>
      constructor
      exact Hinv₁
      case right =>
      constructor
      exact Hinv₂
      case right =>
      constructor
      exact Hinv₃
      case right =>
      constructor
      exact Hinv₄
      case right =>
      constructor
      exact Hinv₅
      case right =>
      constructor
      exact Hinv33
      case right =>
      exact Hinv34

}


def IslandInArr : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard :=  fun b => b.IL_IN_SR = Sensor.Off ∧ not b.il_in_10 ∧ b.A > 0

    action := fun b => {b with IL_IN_SR := Sensor.On}

    safety := fun b => by
      simp [Machine.invariant,
      Bridge3.invariant_12,
      Bridge3.invariant_13,
      Bridge3.invariant_14,
      Bridge3.invariant_15,
      Bridge3.invariant_16,
      Bridge3.invariant_17,
      Bridge3.invariant_18,
      Bridge3.invariant_19,
      Bridge3.invariant_20,
      Bridge3.invariant_21,
      Bridge3.invariant_22,
      Bridge3.invariant_23,
      Bridge3.invariant_24,
      Bridge3.invariant_25,
      Bridge3.invariant_26,
      Bridge3.invariant_27,
      Bridge3.invariant_28,
      Bridge3.invariant_29,
      Bridge3.invariant_30,
      Bridge3.invariant_31,
      Bridge3.invariant_32,
      Bridge3.invariant_33,
      Bridge3.invariant_34]
      intros Hinv12 Hinv13 Hinv14 Hinv15 Hinv16 Hinv17 Hinv18 Hinv19 Hinv20 Hinv21 Hinv22 Hinv23 Hinv24 Hinv25 Hinv26 Hinv27 Hinv28 Hinv29 Hinv30 Hinv31 Hinv32 Hinv33_phys Hinv34_phys Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv33 Hinv34 Hgrd₁ Hgrd₂ h34
      constructor
      exact h34
      case right =>
      constructor
      exact fun a => Hinv13 a
      case right =>
      constructor
      exact fun a => Hinv14 a
      case right =>
      constructor
      exact fun a => Hinv15 a
      case right =>
      constructor
      exact fun a => Hinv16 a
      case right =>
      constructor
      exact Hgrd₂
      case right =>
      constructor
      exact fun a => Hinv18 a
      case right =>
      constructor
      exact fun a => Hinv19 a
      case right =>
      constructor
      exact fun a => Hinv20 a
      case right =>
      constructor
      exact fun a a_1 => Hinv21 a a_1
      case right =>
      constructor
      exact fun a a => Hinv22 Hgrd₂ a
      case right =>
      constructor
      exact fun a a_1 => Hinv23 a a_1
      case right =>
      constructor
      exact fun a a => Hinv24 Hgrd₂ a
      case right =>
      constructor
      exact fun a a_1 => Hinv25 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv26 a a_1
      case right =>
      constructor
      exact fun a a => Hinv27 Hgrd₂ a
      case right =>
      constructor
      exact fun a a => Hinv28 Hgrd₂ a
      case right =>
      constructor
      exact fun a a_1 => Hinv29 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv30 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv31 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv32 a a_1
      case right =>
      constructor
      exact Hinv33_phys
      case right =>
      constructor
      exact Hinv34_phys
      case right =>
      constructor
      exact Hinv₁
      case right =>
      constructor
      exact Hinv₂
      case right =>
      constructor
      exact Hinv₃
      case right =>
      constructor
      exact Hinv₄
      case right =>
      constructor
      exact Hinv₅
      case right =>
      constructor
      exact Hinv33
      case right =>
      exact Hinv34

}


def IslandOutArr : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b => b.IL_OUT_SR = Sensor.Off ∧ not b.il_out_10 ∧ b.B > 0
    action := fun b => {b with IL_OUT_SR := Sensor.On}

    safety := fun b => by
      simp [Machine.invariant,
      Bridge3.invariant_12,
      Bridge3.invariant_13,
      Bridge3.invariant_14,
      Bridge3.invariant_15,
      Bridge3.invariant_16,
      Bridge3.invariant_17,
      Bridge3.invariant_18,
      Bridge3.invariant_19,
      Bridge3.invariant_20,
      Bridge3.invariant_21,
      Bridge3.invariant_22,
      Bridge3.invariant_23,
      Bridge3.invariant_24,
      Bridge3.invariant_25,
      Bridge3.invariant_26,
      Bridge3.invariant_27,
      Bridge3.invariant_28,
      Bridge3.invariant_29,
      Bridge3.invariant_30,
      Bridge3.invariant_31,
      Bridge3.invariant_32,
      Bridge3.invariant_33,
      Bridge3.invariant_34]
      intros Hinv12 Hinv13 Hinv14 Hinv15 Hinv16 Hinv17 Hinv18 Hinv19 Hinv20 Hinv21 Hinv22 Hinv23 Hinv24 Hinv25 Hinv26 Hinv27 Hinv28 Hinv29 Hinv30 Hinv31 Hinv32 Hinv33_phys Hinv34_phys Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv33 Hinv34 Hgrd₁ Hgrd₂ h34
      constructor
      exact fun a => Hinv12 a
      case right =>
      constructor
      exact h34
      case right =>
      constructor
      exact fun a => Hinv14 a
      case right =>
      constructor
      exact fun a => Hinv15 a
      case right =>
      constructor
      exact fun a => Hinv16 a
      case right =>
      constructor
      exact fun a => Hinv17 a
      case right =>
      constructor
      exact Hgrd₂
      case right =>
      constructor
      exact fun a => Hinv19 a
      case right =>
      constructor
      exact fun a => Hinv20 a
      case right =>
      constructor
      exact fun a a_1 => Hinv21 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv22 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv23 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv24 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv25 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv26 a Hgrd₂
      case right =>
      constructor
      exact fun a a_1 => Hinv27 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv28 a Hgrd₂
      case right =>
      constructor
      exact fun a a_1 => Hinv29 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv30 a a_1
      case right =>
      constructor
      exact fun a a => Hinv31 Hgrd₂ a
      case right =>
      constructor
      exact fun a a => Hinv32 Hgrd₂ a
      case right =>
      constructor
      exact Hinv33_phys
      case right =>
      constructor
      exact Hinv34_phys
      case right =>
      constructor
      exact Hinv₁
      case right =>
      constructor
      exact Hinv₂
      case right =>
      constructor
      exact Hinv₃
      case right =>
      constructor
      exact Hinv₄
      case right =>
      constructor
      exact Hinv₅
      case right =>
      constructor
      exact Hinv33
      case right =>
      exact Hinv34

}

def MainlandOutDep : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b => b.ML_OUT_SR = Sensor.On ∧ b.mainlandTL = Color.Green

    action := fun b => {b with IL_OUT_SR := Sensor.Off
                               ml_out_10 := True
                               A := b.A + 1}

    safety := fun b => by
      simp [Machine.invariant,
      Bridge3.invariant_12,
      Bridge3.invariant_13,
      Bridge3.invariant_14,
      Bridge3.invariant_15,
      Bridge3.invariant_16,
      Bridge3.invariant_17,
      Bridge3.invariant_18,
      Bridge3.invariant_19,
      Bridge3.invariant_20,
      Bridge3.invariant_21,
      Bridge3.invariant_22,
      Bridge3.invariant_23,
      Bridge3.invariant_24,
      Bridge3.invariant_25,
      Bridge3.invariant_26,
      Bridge3.invariant_27,
      Bridge3.invariant_28,
      Bridge3.invariant_29,
      Bridge3.invariant_30,
      Bridge3.invariant_31,
      Bridge3.invariant_32,
      Bridge3.invariant_33,
      Bridge3.invariant_34]
      intros Hinv12 Hinv13 Hinv14 Hinv15 Hinv16 Hinv17 Hinv18 Hinv19 Hinv20 Hinv21 Hinv22 Hinv23 Hinv24 Hinv25 Hinv26 Hinv27 Hinv28 Hinv29 Hinv30 Hinv31 Hinv32 Hinv33_phys Hinv34_phys Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv33 Hinv34 Hgrd₁ Hgrd₂
      constructor
      exact fun a => Hinv14 a
      case right =>
      constructor
      exact Hgrd₂
      case right =>
      constructor
      exact fun a => Hinv16 a
      case right =>
      constructor
      exact fun a => Hinv17 a
      case right =>
      constructor
      exact fun a => Hinv19 a
      case right =>
      constructor
      omega
}

def MainlandInDep : OrdinaryEvent (Bridge3 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b => b.ML_IN_SR = Sensor.On

    action := fun b => {b with ML_IN_SR := Sensor.Off
                               ml_in_10 := True
                               C := b.C - 1}

    safety :=  fun b => by
      simp [Machine.invariant,
      Bridge3.invariant_12,
      Bridge3.invariant_13,
      Bridge3.invariant_14,
      Bridge3.invariant_15,
      Bridge3.invariant_16,
      Bridge3.invariant_17,
      Bridge3.invariant_18,
      Bridge3.invariant_19,
      Bridge3.invariant_20,
      Bridge3.invariant_21,
      Bridge3.invariant_22,
      Bridge3.invariant_23,
      Bridge3.invariant_24,
      Bridge3.invariant_25,
      Bridge3.invariant_26,
      Bridge3.invariant_27,
      Bridge3.invariant_28,
      Bridge3.invariant_29,
      Bridge3.invariant_30,
      Bridge3.invariant_31,
      Bridge3.invariant_32,
      Bridge3.invariant_33,
      Bridge3.invariant_34]
      intros Hinv12 Hinv13 Hinv14 Hinv15 Hinv16 Hinv17 Hinv18 Hinv19 Hinv20 Hinv21 Hinv22 Hinv23 Hinv24 Hinv25 Hinv26 Hinv27 Hinv28 Hinv29 Hinv30 Hinv31 Hinv32 Hinv33_phys Hinv34_phys Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hinv₅ Hinv33 Hinv34 Hgrd₁
      constructor
      exact fun a => Hinv12 a
      case right =>
      constructor
      exact fun a => Hinv13 a
      case right =>
      constructor
      exact fun a => Hinv15 a
      case right =>
      constructor
      exact fun a => Hinv16 a
      case right =>
      constructor
      exact fun a => Hinv17 a
      case right =>
      constructor
      exact fun a => Hinv18 a
      case right =>
      constructor
      exact fun a => Hinv20 a
      case right =>
      constructor
      exact fun a a_1 => Hinv21 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv22 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv23 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv24 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv25 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv26 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv27 a a_1
      case right =>
      constructor
      exact fun a a_1 => Hinv28 a a_1
      case right =>
      constructor
      exact fun a =>
        (fun {b a c} h => (Nat.sub_eq_iff_eq_add h).mpr) (Hinv14 Hgrd₁) (Hinv30 a (Hinv19 Hgrd₁))
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
