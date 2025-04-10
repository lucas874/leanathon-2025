# Leanathon 2025

## Proposal

### Learning objective

The goal of this course is to learn how to work with the Lean 4 theorem prover, in a capacity to _start formalization of new or existing work_. This includes:

- Writing domain specific data types (inductive and structural types)
- Write operations and semantics for and on these types
- Proof properties about these operations and semantics
- Write domain specific languages using Leans extensible syntax
- Make use existing theory, such as the extensive mathlib library

## Dates

We propose having joint interactive lectures and workshops (it is a leanathon after all) on ...

- **Tuesday mornings** and
- **Thursday afternoons**

... for three weeks starting **22/4**. Please open issues or [contact](mailto:oembo@dtu.dk) if you have any recommendations or comments about this or if it doesn't work for you!

| Date          | Description  |
| ------------- | ------------ |
| Tuesday 22/4  | Introduction |
| Thursday 24/4 | TBD          |
| Tuesday 29/4  | TBD          |
| Thursday 1/5  | TBD          |
| Thursday 8/5  | TBD          |

## Participants

- [Oliver Bøving](https://github.com/oeb25)
- [Ayman Hussein](https://github.com/a-y-man)
- [_You? Please add yourself if you would like to join!_](https://github.com/oembo-sse/leanathon-2025/edit/main/README.md)

## Exciting snippets of what you can do

### Embed Wasm (wat) into lean syntax

```lean
/--
info: ctx { locals := {i ↦ 3}
      stack := [10], frame :=  }
-/
#guard_msgs in
#eval
  let mod := wasm {
    (module
      (func hello
        ((local i i32))
        (i32.add (i32.const 1) (i32.const 2))
        (local.set i)
        (i32.sub (local.get i) (local.get i))
        if
          i32.const 5
        else
          i32.const 10
        end
      )
    )
  }
  Ctx.ofModule mod |>.run
```

- `wasm { ... }` encapsulates Wasm code to construct a module
- `Ctx.ofModule mod |>.run` executes the `hello` func using a basic Wasm interpreter written in Lean
- `#guard_msgs in` is an expectation/golden test functionality, that makes sure the result of `#eval` (which executes the Lean code), prints the thing in the comment above!

### Guarded-Command Language (GCL) graph construction

```lean
mutual

def Command.edges (q q' : State) : Command → GraphBuilder (DSet Edge)
| gcl { ~x := ~y } => pure {⟨q, act {~x := ~y}, q'⟩}
| gcl { skip } => pure {⟨q, act {skip}, q'⟩}
| gcl { ~C₁ ; ~C₂ } => do
    let q ← fresh
    let E₁ ← C₁.edges q q
    let E₂ ← C₂.edges q q'
    pure $ (E₁ ∪ E₂)
| gcl { if ~gc fi } => gc.edges q q'
| gcl { do ~gc od } => do
    let b := gc.done
    let E ← gc.edges q q
    pure $ E ∪ {⟨q, act {if ~b}, q'⟩}

def Guarded.edges (q q' : State) : Guarded Command → GraphBuilder (DSet Edge)
| gcluard { ~b → ~C } => do
    let q ← fresh
    let E ← C.edges q q'
    pure $ {⟨q, act {if ~b}, q⟩} ∪ E
| gcluard { ~GC₁ [] ~GC₂ } => do
    let E₁ ← GC₁.edges q q'
    let E₂ ← GC₂.edges q q'
    pure $ E₁ ∪ E₂

end

structure Graph where
    edges : DSet Edge
deriving Repr

def Command.graph (c : Command) : Graph :=
    ⟨(c.edges q▹ q◂ 0).fst⟩

def Graph.dot (g : Graph) : String :=
    let edges :=
        g.edges.image (fun e ↦ s!"{reprStr e.source} -> {reprStr e.target}[label=\"{reprStr e.action}\"]")
            |>.elements |> "  ".intercalate
    s!"dgraph \{{edges}}"

/-- info: "dgraph {q[0] -> q[0][label=\"skip\"]  q[0] -> q◂[label=\"a := 12\"]}" -/
#guard_msgs in
#eval gcl { skip; a := 12 }.graph.dot
```

- `def Command.edges` and `def Guard.edges` are builds the graphs à la _Formal Methods An Appetizer_
- `| gcl { ~x := ~y } => ...` uses custom syntax to match on GCL programs, where `~x` means we bind the target of assignment into Lean variable `x`
- `let q ← fresh` uses Monadic-style fresh node declaration
- `#guard_msgs in #eval` again makes sure that out function produces the expected output by comparing to the comment above

### Guarded-Command Language (GCL) semantics

```lean
def 𝒜 : AExpr → Mem → Option ℤ
| .const n, _ => some n
| .var n, σ => if h : n ∈ σ.dom then σ.read ⟨n, h⟩ else none
| aexpr { ~a₁ + ~a₂ }, σ => return (← 𝒜 a₁ σ) + (← 𝒜 a₂ σ)
| aexpr { ~a₁ - ~a₂ }, σ => return (← 𝒜 a₁ σ) - (← 𝒜 a₂ σ)
| aexpr { ~a₁ * ~a₂ }, σ => return (← 𝒜 a₁ σ) * (← 𝒜 a₂ σ)
| aexpr { ~a₁ / ~a₂ }, σ => return (← 𝒜 a₁ σ) / (← 𝒜 a₂ σ)

def ℬ : BExpr → Mem → Option Bool
| .const t, _ => pure t
| bexpr { ¬~b }, σ => return ¬(← ℬ b σ)
| bexpr { ~a₁ = ~a₂ }, σ => return (← 𝒜 a₁ σ) = (← 𝒜 a₂ σ)
| bexpr { ~a₁ ≠ ~a₂ }, σ => return (← 𝒜 a₁ σ) ≠ (← 𝒜 a₂ σ)
| bexpr { ~a₁ < ~a₂ }, σ => return (← 𝒜 a₁ σ) < (← 𝒜 a₂ σ)
| bexpr { ~a₁ ≤ ~a₂ }, σ => return (← 𝒜 a₁ σ) ≤ (← 𝒜 a₂ σ)
| bexpr { ~a₁ > ~a₂ }, σ => return (← 𝒜 a₁ σ) > (← 𝒜 a₂ σ)
| bexpr { ~a₁ ≥ ~a₂ }, σ => return (← 𝒜 a₁ σ) ≥ (← 𝒜 a₂ σ)
| bexpr { ~a₁ ∧ ~a₂ }, σ => return (← ℬ a₁ σ) ∧ (← ℬ a₂ σ)
| bexpr { ~a₁ ∨ ~a₂ }, σ => return (← ℬ a₁ σ) ∨ (← ℬ a₂ σ)

def 𝒮 : Act → Mem → Option Mem
| act {~x := ~a}, σ => do some $ σ[x ↦ ← 𝒜 a σ]
| act {skip}, σ => some σ
| act {if ~b}, σ => do if ← ℬ b σ then some σ else none
```

- `def 𝒜` and `def ℬ` and `def 𝒮` defines semantics for arithmetic, boolean, and actions. Note the extensive use for unicode! To type `𝒜` you do `\McA`, and it automatically (in vscode at least) get replaced by `𝒜`
