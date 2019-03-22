# Flow Analysis for Non-nullability

paulberry@google.com

WORK IN PROGRESS: I am writing this based on
https://docs.google.com/document/d/11Xs0b4bzH6DwDlcJMUcbx4BpvEKGz8MVuJWEfo_mirE/edit,
however I am making several changes / design decisions.  See the section
"Alternatives considered" for details.

**Status**: Proposal.

This is intended to define a the local analysis (within function and method
bodies) that underlies type promotion, definite assignment analysis, and
reachability analysis.

## Motivation

The Dart language spec requires type promotion analysis to determine when
a local variable is known to have a more specific type than its declared type.
We believe additional enhancement is necessary to support NNBD (“non-nullability by default”)
including but not limited to the [Enhanced Type Promotion](
https://github.com/dart-lang/language/blob/master/working/enhanced-type-promotion/feature-specification.md)
proposal (see [tracking issue](https://github.com/dart-lang/language/issues/81)).

For example, we should be able to handle these situations:

```dart
int stringLength1(String? stringOrNull) {
  return stringOrNull.length; // error stringOrNull may be null
}

int stringLength2(String? stringOrNull) {
  if (stringOrNull != null) return stringOrNull.length; // ok
  return 0;
}
```

The language spec also requires a small amount of reachability analysis,
to ensure control flow does not reach the end of a switch case.
To support NNBD a more complete form of reachability analysis is necessary to detect
when control flow “falls through” to the end of a function body and an implicit `return null;`,
which would be an error in a function with a non-nullable return type.
This would include but not be limited to the existing
[Define 'statically known to not complete normally'](https://github.com/dart-lang/language/issues/139)
proposal.

For example, we should correctly detect this error situation:

```dart
int stringLength3(String? stringOrNull) {
  if (stringOrNull != null) return stringOrNull.length;
} // error implied null return value

int stringLength4(String? stringOrNull) {
  if (stringOrNull != null) {
    return stringOrNull.length;
  } else {
    return 0;
  }
} // ok!
```

Finally, to support NNBD, we believe definite assignment analysis should be added to the spec,
so that a user is not required to initialize non-nullable local variables if it can be proven
that they will be assigned a non-null value before being read.
There are currently discussions underway about exactly how definite assignment should be specified,
and there is a [prototype implementation](
https://github.com/dart-lang/sdk/blob/master/pkg/analyzer/lib/src/dart/resolver/definite_assignment.dart)
in the analyzer codebase which is not yet enabled.

With all the above, we should properly analyze these functions:

```dart
int stringLength5(String? stringOrNull) {
  String string;
  if (stringOrNull != null) {
    string = stringOrNull;
  }
  return string.length; // error string may not have been assigned
}

int stringLength6(String? stringOrNull) {
  String string;
  if (stringOrNull != null) {
    string = stringOrNull;
  } else {
    string = '';
  }
  return string.length; // ok
}
```

We believe that all three kinds of analysis can be specified (and implemented) using a common framework,
and that by doing so, we can make all three of them more sophisticated without a great deal of extra effort.
This document outlines the formulation we have in mind, and illustrates the benefits through some examples.
The design is inspired by the Wikipedia article on definite assignment analysis, and shares many of its concepts
with the prototype implementation of definite assignment analysis in the analyzer, as well as the implementation
of type promotion in the front end.  It also takes many ideas from prior work by Johnni Winther in Java,
and it is similar to analysis that is currently done by the dart2js back-end.

## Terminology and Notation

TODO: We use the generic term *node* to denote an expression, statement, top
level function, method, constructor, or field.

TODO: `[]` denotes optional syntax.

TODO: more symbols

A *type test site*, denoted `TypeTestSite(expression, type)` represents a
location in the program where a variable's type is tested, either via an `is`
expression or a cast.

A *variable model*, denoted `VariableModel(declaredType, promotedType,
testSites, assigned, writeCaptured)`, represents what is statically known to
flow analysis about the state of a variable at a given point in the source code:

- `declaredType` is the type assigned to the variable at its declaration site
  (either explicitly or by type inference).

- `promotedType` is the type flow analysis has established for the variable at
  the given point in the program's execution.  It will always be a subtype of
  `declaredType`.

- `testSites` is an ordered list of *type test site*s representing the set of
  type tests that are known to have been performed on the variable in all code
  paths leading to the given point in the source code.

- `assigned` is a boolean value indicating whether the variable has been
  definitely assigned at the given point in the source code.
  
- `writeCaptured` is a boolean value indicating whether a closure might exist at
  the given point in the source code, which could potentially write to the
  variable.

A *flow model*, denoted `FlowModel(reachable, variableModels)`, represents what
is statically known to flow analysis about the state of the program at a given
point in the source code:

- `reachable` is a boolean value indicating whether the given point in the
  source code might conceivably be reached during execution.  Note that this is
  a conservative estimate.  If `reachable` is `false`, the given point is known
  by flow analysis to be unreachable; otherwise no firm conclusion can be drawn.
  
- `variableModels` is a mapping from variables in scope at the given point to
  their associated *variable model*s.
  
  - We will use the notation `{A: B, C: D}` to denote a map associating the key
    `A` with the value `B`, and the key `C` with the value `D`.
    
The following functions associate flow models to points in the source code:

- `before(N)`, where `N` is a statement or expression, represents the *flow
  model* just prior to execution of `N`.
  
- `after(N)`, where `N` is a statement or expression, represents the *flow
  model* just after execution of `N`, assuming that `N` completes normally
  (i.e. does not throw an exception or perform a jump such as `return`, `break`,
  or `continue`).
  
- `true(E)`, where `E` is an expression, represents the *flow model* just after
  execution of `E`, assuming that `E` completes normally and evaluates to `true`.
  
- `false(E)`, where `E` is an expression, represents the *flow model* just after
  execution of `E`, assuming that `E` completes normally and evaluates to `false`.
  
- `null(E)`, where `E` is an expression, represents the *flow model* just after
  execution of `E`, assuming that `E` completes normally and evaluates to `null`.
  
- `notNull(E)`, where `E` is an expression, represents the *flow model* just
  after execution of `E`, assuming that `E` completes normally and does not
  evaluate to `null`.
  
- `break(S)`, where `S` is a `do`, `for`, `switch`, or `while` statement, represents TODO.
  
Note that `true`, `false`, `null`, and `notNull` are defined for all expressions
regardless of their static types.

We also make use of the following auxiliary functions:

- `join(M1, M2)`, where `M1` and `M2` are control flow paths, represents the union
  of the *flow model* after `M1` and after `M2`, and is presumed to satisfy a these properties:

  - Commutativity: join(M1, M2) = join(M2, M1)

  - Associativity: join(join(M1, M2), M3) = join(M1, join(M2, M3))

  For brevity, we will sometimes extend `join` to more than two arguments in the obvious way.
  For example, `join(M1, M2, M3)` represents `join(join(M1, M2), M3)`, and `join(S)`, where S
  is a set of models, denotes the result of folding all models in S together using `join`.

- `EMPTY` represents the model ∅ (the empty model) such that join(M, ∅) = M.<br/>
  ∅ can be thought of as corresponding to an empty set of program states.

- `exit(N)`, where `N` is a statement, represents the state associated with any unreachable code
  that follows an unconditional jump such as `break` or `return`.
  It would be sound to define exit(M) = ∅ for all models, but we can perform better analysis
  resulting in better feedback for the user if we use the formulation described
  in the **Extended Reachability** section below.

## Details

Flow analysis of a function or method is defined via two recursive passes over
the source code.  In the first pass, TODO.  In the second pass, flow models are
are assigned to `before(N)` and `after(N)` for every statement or expression
`N`, and to `true(E)`, `false(E)`, `null(E)`, and `notNull(E)` for every
expression `E`.  The second pass is interleaved with type inference.

For both passes, we will define the steps that are taken to *visit* a node `N`.
In most cases this will involve visiting all of the statements and expressions
constituting `N` in some well-defined order.

Implementation note: as with type inference, it is not necessary to implement
flow analysis in this way; the flow models for some expressions and statements
could be completely or partially computed during the first pass, which could
occur during parsing.

### First pass

A small amount of information needs to be gathered beforehand, namely which variables
are potentially assigned in certain scopes; hopefully it is possible to gather this
information during earlier analysis phases.

TODO: List information needed by next pass

### Flow model pass: algorithm

The flow model pass is initiated by visiting the top level function, method,
constructor, or field declaration to be analyzed.

To visit a node `N`, we pattern match according to the following rules:

#### Expressions

- **True literal**: If `N` is the literal `true`, then:

  - Let `true(N) = before(N)`.
  
  - Let `false(N) = EMPTY`.

- **False literal**: If `N` is the literal `false`, then:

  - Let `true(N) = EMPTY`.
  
  - Let `false(N) = before(N)`.

- **Shortcut and**: If `N` is a shortcut "and" expresion of the form `E1 && E2`,
  then:
  
  - Let `before(E1) = before(N)`.
  
  - Visit `E1` to determine `true(E1)` and `false(E1)`.
  
  - Let `before(E2) = true(E1)`.
  
  - Visit `E2` to determine `true(E2)` and `false(E2)`.
  
  - Let `true(N) = true(E2)`.
  
  - Let `false(N) = join(false(E1), false(E2))`.

- **Shortcut or**: If `N` is a shortcut "or" expression of the form `E1 || E2`,
  then:
  
  - Let `before(E1) = before(N)`.
  
  - Visit `E1` to determine `true(E1)` and `false(E1)`.
  
  - Let `before(E2) = false(E1)`.
  
  - Visit `E2` to determine `true(E2)` and `false(E2)`.
  
  - Let `false(N) = false(E2)`.
  
  - Let `true(N) = join(true(E1), true(E2))`.

- **If-null**: If `N` is an if-null expression of the form `E1 ?? E2`, then:

  - Let `before(E1) = before(N)`.
  
  - Visit `E1` to determine `null(E1)` and `notNull(E1)`.
  
  - Let `before(E2) = null(E1)`.
  
  - Visit `E2` to determine `null(E2)` and `notNull(E2)`.
  
  - Let `null(N) = null(E2)`.
  
  - Let `notNull(N) = join(notNull(E1), notNull(E2))`.

- **Binary operator**: All binary operators other than `&&`, `||`, and `??` are
  handled as calls to the appropriate `operator` method.

- **Conditional expression**: If `N` is a conditional expression of the form `E1
  ? E2 : E3`, then:
  
  - Let `before(E1) = before(N)`.
  
  - Visit `E1` to determine `true(E1)`.
  
  - Let `before(E2) = true(E1)`.
  
  - Visit `E2` to determine `after(E2)`, `true(E2)`, `false(E2)`, `null(E2)`,
    and `notNull(E2)`.
  
  - Let `before(E3) = false(E1)`.
  
  - Visit `E3` to determine `after(E3)`, `true(E3)`, `false(E3)`, `null(E3)`,
    and `notNull(E3)`.
  
  - Let `after(N) = join(after(E2), after(E3))`.
  
  - Let `true(N) = join(true(E2), true(E3))`.
  
  - Let `false(N) = join(false(E2), false(E3))`.
  
  - Let `null(N) = join(null(E2), null(E3))`.
  
  - Let `notNull(N) = join(notNull(E2), notNull(E3))`.
  
TODO: behavior of true, false, notNull, and null if not specified above.

If `N` is an expression, and the above rules specify the values to be assigned
to `true(N)` and `false(N)`, but do not specify values for `null(N)`,
`notNull(N)`, or `after(N)`, then they are assigned as follows:

- `null(N) = EMPTY`.

- `notNull(N) = join(true(N), false(N))`.

- `after(N) = notNull(N)`.

If `N` is an expression, and the above rules specify the value to be assigned to
`after(N)`, but do not specify values for `true(N)`, `false(N)`, `null(N)`, or
`notNull(N)`, then they are all assigned the same value as `after(N)`.

#### Statements

- TODO: assignment, return, 

- **Break statement**: If `N` is a statement of the form `break [L];`, then:

  - Let `S` be the statement targeted by the `break`.  If `L` is not present,
    this is the innermost `do`, `for`, `switch`, or `while` statement.
    Otherwise it is the `do`, `for`, `switch`, or `while` statement with a label
    matching `L`.
  
  - Update `break(S) = join(break(S), before(N))`.
  
  - Let `after(N) = exit(before(N))`.
  
- **Continue statement**: If `N` is a statement of the form `continue [L];` then:

  - Let `S` be the statement targeted by the `continue`.  If `L` is not present,
    this is the innermost `do`, `for`, or `while` statement.  Otherwise it is
    the `do`, `for`, or `while` statement with a label matching `L`, or the
    `switch` statement containing a switch case with a label matching `L`.
    
  - Update `continue(S) = join(continue(S), before(N))`.
  
  - Let `after(N) = exit(before(N))`.

- **Do statement**: If `N` is a "do" statement of the form `do S while (E);`,
  then:
  
  - TODO: work on proofs

#### Functions

- **Top level function or method**: If `N` is a top level function or method of
  the form `[R] name([T1] P1, [T2] P2, ... [Tn] Pn) B`, then:
  
  - If `R` is present, let `R' = R`.  Otherwise let `R'` be the inferred return
    type of the top level function or method.
    
  - For each parameter `Pi`, if `Ti` is present let `Ti' = Ti`.  Otherwise let
    `Ti'` be the inferred parameter type.
    
  - If `B` is a block, let `B' = B`.  If `B` takes the form `=> E;`, then let
    `B' = { return E; }`.
  
  - Let `before(B') = FlowModel(true, {P1: VariableModel(T1', T1', [], false,
    false), P2: VariableModel(T2', T2', [], false, false), ... Pn:
    VariableModel(Tn', Tn', [], false, false)})`.
  
  - Visit `B'` to determine `after(B')`.
  
  - If `after(B').reachable` is `true`, and `R'` is not nullable, then there is
    a static error: control flow reached the end of the top level function or
    method without returning a value.
    
- **Factory constructor**: Factory constructors are treated as the equivalent
  static method, having an implicit return type `C` (where `C` is the type of
  the enclosing class).  TODO: should the implicit return type of the factory
  constructor be `C?` instead?
    
- **Generative constructor**: If `N` is a generative constructor of the form
  `name([T1] P1, [T2] P2, ... [Tn] Pn) : I1, I2, ... In B`, then:
  
  - TODO: specify the rule here.  Account for the wacky scoping rules with
    `this.` as well as the fact that a `this.` parameter may effectively have
    two types.

- TODO: redirecting factory and generative constructors.

### Extended Reachability

  As mentioned earlier, it would be sound to define exit(M) = ∅ for all models, but
  doing so leads to less than optimal user feedback. Consider, for example, the following code:

  ```dart
    void f(Object o) {
      throw ...; // Temporary hack (S1)
      if (o is! int) return; // (S2)
      print(o.isEven); // (S3)
      print(o.hashCodee); // (S4)
    }
  ```

  Due to the unconditional throw at (S1), `after(S1)` would be considered unreachable,
  so both branches of the if statement at (S2) would be considered unreachable.
  Consequently, when the states associated with the two branches are joined,
  there will be no way to tell that the promotion of `o` to `int` should be kept,
  so the type promotion model will be `o` → `Object`.

  This creates a conundrum: do we report errors in unreachable code?
  If we do, then we would flag (S3) as an error, likely causing user frustration.
  If we don’t, then we would fail to notice the misspelling at (S4),
  again likely causing frustration.

  We solve this by extending reachability analysis as follows.
  On entry to a branching construct such as an `if` statement or a loop,
  we provisionally reset reachability analysis to `true`
  (i.e., we provisionally assume that the code is reachable).
  On exit, we correct the provisional assumption by anding in the actual reachability
  of the branching construct.
  So for instance, the reachability formulas for an `if` statement become:

TODO fold this into the algorithm section

  - `before(C)` ← 𝐓
  - `before(S1)` ← `true(C)`
  - `before(S2)` ← `falseC)`
  - `after(IF)` ← `join(after(S1), after(S2)` ∧ `before(IF)`

  And the reachability formulas for `E1 && E2` become:

  - `before(E1)` ← 𝐓
  - `before(E2)` ← `true(E1)`
  - `true(&&)` ← `true(E2)` ∧ `before(&&)`
  - `false(&&)` ← `join(false(E1), false(E2))` ∧ `before(&&)`
  - `after(&&)` ← `join(true(&&), false(&&))`

  This modification is only performed for reachability analysis; the other analyses are unchanged.
  However since the join operations for the other analyses make use of reachability analysis
  to decide which branches to discard, this has the effect of allowing the other analyses
  to produce intuitive results when analyzing unreachable code.

  This analysis is sound because its only effect is to change the analysis of code
  that is truly unreachable.  Any model whatsoever is sound for unreachable code,
  because the true set of program states for unreachable code is the empty set;
  therefore any model is a valid conservative approximation of the true set of program states.

## Alternatives considered

TODO: rewrite so that we actually describe the choices rather than just
referring to options in
https://docs.google.com/document/d/11Xs0b4bzH6DwDlcJMUcbx4BpvEKGz8MVuJWEfo_mirE/edit

- Do we use the "single pass analysis" option or the "fixed point analysis"
  option?  Single pass analysis.  Rationale: fixed point analysis is a big
  additional complication and it conflicts with the front end team's desire to
  analyze all the code in a single pass.  We can always switch to the fixed
  point approach in the future if there's sufficient user demand.

- Do we include the extension "allow bottom to influence reachability"?  Yes.
  Rationale: it's an easy extension and it has tangible benefits (e.g. it allows
  `if (x == null) reportError()` to promote `x` to non-nullable).

- Do we include the extension "provisionally reachable code"?  Yes.  Rationale:
  this is required to ensure that the new algorithm produces results that are
  strictly better than the old algorithm.

- Do we include the extension "complete switch" as described in [issue 35716](
  https://github.com/dart-lang/sdk/issues/35716)?  Yes.  Rationale: this is a
  simple improvement with obvious benefits for non-nullability.

- Do we keep the existing requirements for switch cases to end in
  `break`, `continue`, `rethrow`, or `return` statements (see the section
  "Switch" in the spec), or do we replace these requirements with a requirement
  based on the new reachability analysis?  Replace them.  Rationale: this should
  reduce user surprise by avoiding two different notions of reachability in the
  spec.  No existing code should be broken by this change, and in the process
  we should be able to address [improved switch flow analysis](
  https://github.com/dart-lang/sdk/issues/35390).

- Do we include the extension "more accurate handling of throws"?  No.
  Rationale: it's not clear that there's a significant benefit, and it makes it
  harder to prove the system is sound.
  
- Do we include the extension "promote via runtimeType equality check"?  No.
  Rationale: AFAIK, there hasn't been a great deal of demand for this.
  
- Do we include the extension "promote via downcast"?  Yes.  Rationale: although
  I'm not aware of any user demand for it, this feature is fits well with the
  overall design principles of the rest of the proposal, so including it should
  reduce user surprise.  Note that since implicit downcasts will be switched off
  when the user opts into NNBD, "promote via downcast" really means "promote via
  explicit downcast".
  
- Do we include the extension "use least upper bound in join"?  No.  Rationale:
  this could lead to promoted types that were not explicitly named by the user,
  which is problematic for the reasons explained in Johnni's paper.
  
- Do we include the extension "support non-null branches"?  Yes.  Rationale:
  this is a critical feature we need for non-nullability.
  
- Do we include the extension "support null branches"?  Yes.  Rationale: it's a
  trivial extension with a well understood use case.
  
- Do we include the extension "ensure-guarding"?  Yes.  Rationale: there's a
  well understood use case for this.  Note that we only promote to types that
  are "of interest", so that we never promote a variable to a more specific type
  than the user has mentioned.
  
- Do we include the extension "partial union type support"?  No.  Rationale:
  union types are a can of worms that the language team is deliberately not
  opening yet.
  
- Do we include the extension "final fields and variables"?  No.  Rationale:
  this is fairly orthogonal to the rest of the proposal, so if we're interested
  in doing it we should do it separately.
  
- Do we include the extension "checked final field promotion"?  No.  Rationale:
  in addition to being fairly orthogonal to the rest of the proposal, it is
  somewhat controversial due to how it interacts with soundness.  If we're going
  to do this it should be in a separate proposal.
  
- Do we include the extension "checked asserts"?  No.  Rationale: this has
  similar soundness issues to "checked final field promotion".
  
- Do we include the extension "null and nonNull models"?  Yes.  Rationale: this
  reduces user surprise by making the `??` operator participate in type
  promotion in a similar way to how `&&` and `||` do.
  
- Do we include the extension "type checking of assignment values"?  Yes.
  Rationale: this is a trivial extension to the proposal and real-world code
  could benefit from it.

## Integration with type inference

TODO: talk about where in the algorithm upwards and downwards inference happens,
and where context is carried.

## Proof of soundness

Goal is to show that each concrete program state `S` reached during program
execution is consistent with the static flow model from the corresponding
location in the source code.

## Comparison to previous type promotion algorithm

TODO

Note that I may need to assume covariance of inference for this proof.
(TODO(paulberry): explain this)
