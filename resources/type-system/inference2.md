# Expressions

## Null

## Numbers

TODO(paulberry): reconcile order with spec

### Double literal

### Integer literal

## Booleans

## Strings

TODO(paulberry): reconcile with spec

### Adjacent strings

### Simple string literal

### String interpolation

## Symbol literal

## Collection literals

TODO(paulberry): reconcile with spec

### List literal

### Set or map literal

## Throw

## Function expressions

## This

## Instance creation

## Function invocation

TODO(paulberry): what goes here?

## Function closurization

TODO(paulberry): what goes here?

## Generic function instantiation

TODO(paulberry): what goes here? Anything?

## Lookup

TODO(paulberry): what goes here? Anything?

## Top level getter invocation

TODO(paulberry): what goes here? Anything?

## Member invocations

TODO(paulberry): what goes here? Anything?

### Index expression

## Method invocation

### Cascade expression

TODO(paulberry): this is really weird for this to be here

## Property extraction

TODO(paulberry): reconcile with spec

### Property access

## Assignment

## Conditional

## If-null expressions

TODO(paulberry): split from binary expressions

## Logical boolean expressions

TODO(paulberry): split from binary expressions

## Equality

TODO(paulberry): split from binary expressions

## User-definable binary operations

Note: spec splits these into "relational expressions", "bitwise expressions",
"shift", "additive expressions", and "multiplicative expressions".

TODO(paulberry): make sure all analyzer behaviors are covered either here or in
"equality", "logical boolean expressions", or "if-null expressions".

## Unary expressions

See "prefix expression" in the analyzer

## Await expressions

## Postfix expressions

TODO(paulberry): does `!` go grammatically with other postfix expressions?

## Assignable expressions

TODO(paulberry): what goes here? anything? Maybe l-values?

## Lexical lookup

TODO(paulberry): what goes here? anything?

## Identifier reference

TODO(paulberry): what goes here? anything?

## Type test

## Type cast

==== ABOVE FOLLOWS SPEC

## Augmented expression

TODO(paulberry): postpone working on this?

## Augmented invocation

TODO(paulberry): postpone working on this?

## Constructor reference

TODO(paulberry): is this real?

## Function expression invocation

TODO(paulberry): reconcile this with the spec

## Function reference

TODO(paulberry): reconcile this with the spec

## Parenthesized expression

TODO(paulberry): this is probably worth talking about because of its effect on
null shorting. Where should we talk about it?

## Pattern assignment

## Prefixed identifier

TODO(paulberry): split out cases to match spec

## Record literal

## Rethrow expression

TODO(paulberry): this is spec'ed as a statement.

## Simple identifier

TODO(paulberry): split out cases to match spec?

## Super expression

TODO(paulberry): rework to match spec

## Switch expression

## Type literal

# Other things

TODO(paulberry): patterns

TODO(paulberry): statements

TODO(paulberry): elements
