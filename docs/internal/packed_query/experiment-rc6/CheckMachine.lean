import Lean

/- Independent executable semantics for the experimental register program.
   This is finite cross-checking, not a universal refinement theorem. -/
open Lean

def getE {α} (x : Except String α) : IO α :=
  match x with
  | .ok v => pure v
  | .error e => throw (IO.userError e)

def readJson (path : String) : IO Json := do
  getE (Json.parse (← IO.FS.readFile path))

def field (j : Json) (name : String) : IO Json := getE (j.getObjVal? name)
def nat (j : Json) : IO Nat := getE j.getNat?
def arr (j : Json) : IO (Array Json) := getE j.getArr?

structure Ins where
  op : String
  args : Array Nat
deriving Inhabited

def parseIns (j : Json) : IO Ins := do
  let a ← arr j
  let op ← getE (a[0]!.getStr?)
  let args ← (a.extract 1 a.size).mapM nat
  pure { op, args }

structure CheckResult where
  result : Nat
  steps : Nat
  cats : Array Nat
  reads : Array (Nat × Nat)
  peak : Nat

def execute (code : Array Ins) (regCount width left right : Nat)
    (inputs : Array Nat) (memory : Array Nat) : IO CheckResult := do
  let cap := 2 ^ width
  let mut regs := Array.replicate regCount 0
  regs := regs.set! inputs[0]! left
  regs := regs.set! inputs[1]! right
  let mut pc := 0
  let mut steps := 0
  let mut cats := Array.replicate 6 0
  let mut reads := #[]
  let mut peak := max left right
  let mut result := 0
  let mut halted := false
  while !halted && steps < 20000000 do
    unless pc < code.size do throw (IO.userError "pc out of code")
    let ins := code[pc]!
    let a := ins.args
    let op := ins.op
    let oldpc := pc
    pc := pc + 1
    steps := steps + 1
    let mut category := 0
    let mut write : Option (Nat × Nat) := none
    if op == "halt" then
      category := 5
      result := regs[a[0]!]!
      halted := true
    else if op == "load" then
      category := 0
      let address := regs[a[1]!]!
      unless address < memory.size do throw (IO.userError "missing physical cell")
      let value := memory[address]!
      reads := reads.push (address, value)
      write := some (a[0]!, value)
    else if op == "const" then
      category := 1
      write := some (a[0]!, a[1]!)
    else if op == "move" then
      category := 1
      write := some (a[0]!, regs[a[1]!]!)
    else if op == "jump" then
      category := 4
      pc := a[0]!
    else if op == "jreg" then
      category := 4
      pc := regs[a[0]!]!
    else if op == "jz" || op == "jnz" then
      category := 4
      if (regs[a[0]!]! == 0) == (op == "jz") then pc := a[1]!
    else
      let x := regs[a[1]!]!
      let y := regs[a[2]!]!
      let mut z := 0
      category := 2
      if op == "add" then z := x + y
      else if op == "sub" then
        unless y ≤ x do throw (IO.userError "unguarded subtraction underflow")
        z := x - y
      else if op == "mul" then z := x * y
      else if op == "div" then z := x / y
      else if op == "mod" then z := x % y
      else if op == "shl" then z := Nat.shiftLeft x y
      else if op == "shr" then z := Nat.shiftRight x y
      else if op == "and" then z := Nat.land x y
      else if op == "or" then z := Nat.lor x y
      else
        category := 3
        if op == "lt" then z := if x < y then 1 else 0
        else if op == "le" then z := if x ≤ y then 1 else 0
        else if op == "eq" then z := if x = y then 1 else 0
        else if op == "ne" then z := if x ≠ y then 1 else 0
        else if op == "gt" then z := if x > y then 1 else 0
        else if op == "ge" then z := if x ≥ y then 1 else 0
        else throw (IO.userError s!"unknown opcode {op}")
      write := some (a[0]!, z)
    cats := cats.set! category (cats[category]! + 1)
    if let some (d,z) := write then
      unless d < regs.size && z < cap do
        throw (IO.userError s!"width failure pc={oldpc} dst={d} value={z}")
      regs := regs.set! d z
      peak := max peak z
  unless halted do throw (IO.userError "fuel exhausted")
  unless cats.foldl (· + ·) 0 == steps do throw (IO.userError "category partition")
  pure {result, steps, cats, reads, peak}

def main (args : List String) : IO Unit := do
  let program ← readJson args[0]!
  let fixture ← readJson args[1]!
  let expected ← readJson args[2]!
  let code ← (← arr (← field program "code")).mapM parseIns
  let inputs ← (← arr (← field program "inputs")).mapM nat
  let memory ← (← arr (← field fixture "cells")).mapM fun j => do
    let s ← getE j.getStr?
    match s.toNat? with
    | some n => pure n
    | none => throw (IO.userError "non-numeric cell")
  let width ← nat (← field fixture "cellWidth")
  let rc ← nat (← field program "registers")
  let l ← nat (← field fixture "left")
  let r ← nat (← field fixture "right")
  let cap := 2 ^ width
  unless rc < cap && code.size < cap && l < cap && r < cap &&
      memory.all (· < cap) && code.all (fun ins => ins.args.all (· < cap)) do
    throw (IO.userError "static/input width failure")
  let out ← execute code rc width l r inputs memory
  unless out.result == (← nat (← field expected "resultTag")) &&
      out.steps == (← nat (← field expected "steps")) &&
      out.peak == (← nat (← field expected "maxRegisterValue")) do
    throw (IO.userError "result/count/width disagreement")
  let names := #["memoryRead","registerWrite","arithmetic","comparison","branch","control"]
  let categories ← field expected "categories"
  for i in [:6] do
    unless out.cats[i]! == (← nat (← field categories names[i]!)) do
      throw (IO.userError "category disagreement")
  let er ← (← arr (← field expected "reads")).mapM fun j => do
    pure ((← nat (← field j "address")), (← nat (← field j "reply")))
  unless out.reads == er do throw (IO.userError "ordered receipt disagreement")
  IO.println s!"LEAN VM PASS tag={out.result} steps={out.steps} reads={out.reads.size} width={width} peak={out.peak}"
