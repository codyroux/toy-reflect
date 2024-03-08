This is a tiny repo meant to show how reflection works in Lean.

It defines a tactic to solve goals of the form

`True /\ ... \/ False ...`

(Admittedly not a difficult task) by transforming it into a tree and
evaluating the tree in the booleans.

Metaprogramming comes into play only to get `Prop`s into a `BoolTree`,
using the Qq module, and re-interpreting the resulting tree into a
kernel expression.

For the last step we use the `Mathlib` tactic for deriving `toExpr`
instances.
