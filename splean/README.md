# SPLean: *S*eparation Logic *P*roofs in *Lean*

This project provides a Separation Logic framework for simple heap-manipulating programs verification. Inspired by [CFML](https://softwarefoundations.cis.upenn.edu/slf-current/index.html)

# Building SPLean

To build this project tun 

```
lake exe cache get; lake build
```

# File Content

1. `Theories/HProp.lean`: facts about heap-propositions 
2. `Theories/XSimp.lean`: implementation of an `xsimp` tactic for heap entailment simplification
3. `Theories/SepLog.lean`: Separation logic formalization
4. `Theories/WP1.lean`: Weakest-Precondition formalization
5. `Experiments/Misc.lean`: Some case studies

# Essential tactics

1. `xsimp`: simplifies heap entailments. For instance, `xsimp` turns `H1 ∗ H ∗ H2 ==> H3 ∗ H ∗ H4` into `H1 ∗ H2 ==> H3 ∗ H4`
2. `xstep`: does one step of symbolic execution. This tactic can have an optional argument `triple_lemma` of type `... -> { P }[ c ]{ Q }`. In this case, it will try advance the top-most instruction according to `triple_lemma`
3. `xapp triple_lemma`: applies `triple_lemma` of type `... -> { P }[ c ]{ Q }`. If first argument is omitted, `xapp` will try to find a correspondent lemma in `@[xapp]` hint database
4. `xif`/`xval`/`xref`: tactics for `if`, `return` and `ref` statements
5. `xfor`/`xwhile`: tactics for `for` and `while` loops

# Limitations 
1. `xsimp` tactic can be slow for big heap entailments
2. We only support `for` and `while` loops. Recursion is not supported (yet)
3. We only support programs in an SSA-normal form
