# MyLisp — Interpreter & Standard Library

> **Academic Project — Programming Languages Course**  
> An interpreter and modular standard library for **MyLisp**, a purely functional, statically-scoped Lisp dialect implemented in **Standard ML (`MyLispInterpreter.sml`)**.

---

## Overview & Theoretical Foundation

**MyLisp** is designed as a direct, executable realization of Programming Languages theory in Standard ML. Taking primary inspiration from **Scheme** and **Lispkit**, it pairs minimalist functional semantics with an exact numeric tower, hygienic lexical environments, and a compositional module system.

### Key Language Characteristics

* **Purely Functional & Single Top-Level Expression:** Every MyLisp program (and every imported module) consists of a **single top-level expression** evaluated to a value. There is no mutation (`set!`), no imperative sequencing (`begin`), and no global mutable state—all bindings are introduced lexically through `let`, `let*`, `letrec`, `lambda`, or `import`.
* **Static (Lexical) Scoping & Closures:** Functions evaluate to first-class closures (`closure of myLisp * myLisp * environment`) that capture their lexical environment at declaration time, guaranteeing referential transparency and predictable variable resolution.
* **Functions & Currying:** Since closures in MyLisp take only one argument (`closure of myLisp * myLisp * environment`), the multi-variable lambda syntax of Lisp `(lambda (x y ...) body)` is desugared from the (`interpretSexp`) function into nested single-argument closures (`lambda(x, lambda(y, ...))`), this method is sound by the **currying isomorphism** and supports partial application out of the box (the (`uncurry`) function is implemented in `lists.mylisp`, a module of the standard libray `stdlib.mylisp`).
* **Lazy Environments for Mutual Recursion (`letrec`):** While function application is eager (call-by-value), recursive bindings introduced by `letrec` are modeled via **lazy environment extensions** (`lazyextension of environment * (string * myLisp) list`). Recursive lambda expressions are evaluated on demand upon lookup inside the self-referential environment, enabling clean mutual recursion without mutation or backpatching.
* **First-Class Hygienic Modules (`import` / `export`):** Modules are ordinary single-expression files whose top-level `(export ...)` or `(export *)` expression evaluates to a first-class environment value (`envVal of environment`). Importing files (`(import ("path1.mylisp" ...) body)`) resolves paths relative to the importing file and cleanly merges the exported bindings into the local lexical environment without polluting any global namespace.
* **Pre-Existing Initial Environment (`initialEnv`):** Built-in primitives (`+`, `-`, `*`, `/`, `pow`, `mod`, `cons`, `car`, `cdr`, type predicates, and converters) are pre-populated as curried closures inside `initialEnv`, allowing primitives to be passed as first-class higher-order arguments (e.g., `(map car lists)` or `(foldl + 0 nums)`), while syntactic guards prevent accidental primitive shadowing.

---

## Interpreter Architecture in Standard ML

The implementation in `MyLispInterpreter.sml` mirrors the formal separation between **syntax** and **semantics** taught in Programming Languages theory:

1. **Lexical Analysis (`tokenize`) & S-Expression Parsing (`parseSexp`):**
   * Converts raw source text into an intermediate symbolic tree (`datatype s_exp = Atom of string | List of s_exp list`), handling comments (`;`), string escapes, quote shorthand (`'expr`), and case-insensitive symbols.
2. **Inductive Abstract Syntax (`interpretSexp` $\rightarrow$ `exp`):**
   * The core language is defined as an **inductive algebra** via Standard ML's recursive `datatype` construct (`datatype myLisp = emptyList | const of constant | var of string | ...`).
   * `interpretSexp` acts as the syntactic elaboration pass, translating concrete S-expressions into well-formed AST terms, desugaring derived forms (such as `cond`, `let*`, `list`, multi-argument `lambda`, and multi-argument function application), and enforcing static well-formedness rules (`SyntaxError`).
3. **Operational Semantics (`eval`):**
   * The `eval` function directly encodes the **structural operational semantics** of the language:
     $$\langle d, \text{baseDir}, E, e \rangle \Downarrow v$$
   * By pattern-matching inductively over the `myLisp` algebra, each clause of `eval` corresponds directly to a formal inference rule mapping an environment $E$ and an expression $e$ to a semantic value (`datatype value = constVal | symbolVal | listVal | closure | envVal`), while tracking recursion depth (`MAX_DEPTH`), tracking `baseDir` dynamically using `OS.Path` and distinguishing static `SyntaxError`s from dynamic `RuntimeError`s.

---

## Project Structure

```text
.
├── MyLispInterpreter.sml       # Lexer, S-expression parser, inductive AST, and operational semantics
├── library/
│   ├── combinators.mylisp      # Functional combinators (root module, zero dependencies)
│   ├── list.mylisp             # Higher-order list operations (imports combinators)
│   ├── math.mylisp             # Arithmetic, rounding, and number theory (imports list)
│   ├── strings.mylisp          # String manipulation, slicing, and searching (imports list)
│   └── stdlib.mylisp           # Umbrella module re-exporting the entire standard library
├── test.mylisp                 # Entry-point program for testing and execution
└── README.md                   # Project documentation
```

### Module Dependency Hierarchy

```text
      combinators.mylisp
              │
              ▼
         list.mylisp
           │     │
           ▼     ▼
   math.mylisp  strings.mylisp
           │     │
           └──┬──┘
              ▼
        stdlib.mylisp
```

Because `MyLispInterpreter.sml` tracks `baseDir` dynamically using `OS.Path`, relative imports inside `library/` resolve cleanly regardless of the caller's working directory. Furthermore, each module uses an explicit `(export ...)` clause so that only its own public definitions are exposed, preventing symbol collisions when multiple modules are imported together.

---

## Getting Started

### Prerequisites

* A Standard ML compiler or interpreter supporting the SML'97 Basis Library (e.g., **Poly/ML**, **MLton**, or **SML/NJ**).

### Running a Program

1. Write a single top-level MyLisp expression in `test.mylisp` (or any `.mylisp` file).
2. Load `MyLispInterpreter.sml` in your SML environment and evaluate a file or expression string:

```sml
(* Evaluate a .mylisp file *)
executeFile "test.mylisp";

(* Evaluate a MyLisp expression string directly *)
executeStr "(+ 1/2 3/4)";
```

---

## Language Reference

### 1. Data Types & Exact Numeric Tower

MyLisp implements a self-simplifying numeric tower alongside booleans, strings, symbols, and proper lists:

| Type | Examples | Semantic Behavior |
| :--- | :--- | :--- |
| **Integer** | `0`, `42`, `-15` | Signed SML `int` |
| **Ratio** | `1/2`, `-3/4`, `6/3` $\rightarrow$ `2` | Exact rational pairs reduced via `gcd`; automatically simplifies to `integer` when denominator is `1` |
| **Real** | `3.14`, `-0.5`, `1e-3` | IEEE-754 floating point; mixing `real` with `int` or `ratio` promotes to `real` |
| **Boolean** | `true`, `false` | Logical truth values |
| **String** | `"hello\nworld"` | Immutable strings supporting `\"`, `\\`, `\n`, `\t` escapes |
| **Symbol** | `'foo`, `(quote bar)` | Unevaluated atomic identifiers (case-insensitive) |
| **List** | `'()`, `(list 1 2 3)` | Homogeneous or heterogeneous linked lists |

### 2. Special Forms

* **Conditionals:**
  * `(if cond then-expr else-expr)`
  * `(cond (c1 e1) (c2 e2) ... (else en))`
* **Lexical Bindings:**
  * `(let ((x1 v1) (x2 v2)) body)` — Simultaneous (parallel) local bindings; duplicate names are rejected.
  * `(let* ((x1 v1) (x2 v2)) body)` — Sequential local bindings.
  * `(letrec ((f1 (lambda ...)) (f2 (lambda ...))) body)` — Mutually recursive function bindings backed by lazy environment evaluation.
* **Functions & Currying:**
  * `(lambda (x y ...) body)` — as already said (`interpretSexp`) automatically desugars into nested single-argument closures (`lambda(x, lambda(y, ...))`) returning a curried function.
* **Quoting & Metaprogramming:**
  * `'expr` or `(quote expr)` — Quotes an S-expression as data.
  * `(eval expr)` — Reifies a quoted value back into syntax and evaluates it in the current lexical environment.
* **Modules & Errors:**
  * `(import ("file1.mylisp" "file2.mylisp") body)` — Evaluates imported modules and merges their exported environments into `body`.
  * `(export sym1 sym2 ...)` / `(export *)` — Produces a first-class `envVal` containing the specified (or all user-defined) bindings.
  * `(error "message")` — Aborts evaluation with a `RuntimeError`.

### 3. Built-in Primitives (`initialEnv`)

* **Arithmetic & Comparison:** `+`, `-`, `*`, `/`, `pow`, `mod`, `=`, `<`, `<=`, `>`, `>=`
  * Variadic `+`, `-`, `*`, `/`, and chained comparisons (`(< 1 2 3)`).
  * `(+)` $\rightarrow$ `0`, `(*)` $\rightarrow$ `1`, unary `(- x)` negates, unary `(/ x)` inverts (`(/ 4)` $\rightarrow$ `1/4`).
  * `(pow base exp)` computes exact integer/rational powers for integer exponents and promotes to `real` for fractional exponents.
* **Logic, Lists & Strings:** `and`, `or`, `not`, `cons`, `car`, `cdr`, `list`, `concat`, `explode`
* **Type Predicates:** `null?`, `atom?`, `int?`, `ratio?`, `real?`, `number?`, `bool?`, `symbol?`, `list?`, `string?`
* **Type Conversions & Rounding:**
  * `int->string`, `string->int`, `real->string`, `string->real`, `ratio->string`, `string->ratio`, `bool->string`, `string->bool`
  * `ratio->real`, `real->ratio` (splits integer and fractional components to preserve 9 decimal places of precision without overflow)
  * `floor`, `ceiling`, `round` (exact on `int`, `ratio`, and `real`)

---

## Standard Library (`library/stdlib.mylisp`)

Import the full standard library into any program with:

```lisp
(import ("library/stdlib.mylisp")
    ...)
```

Every library function validates its arguments at runtime using positional type guards (`check-list`, `check-num`, `check-int`, `check-natural`, `check-string`).

### `library/combinators.mylisp`
* **Identity & Constant:** `id`, `const`
* **Argument & Application Control:** `flip`, `curry`, `apply-to`
* **Composition:** `compose` ($f \circ g$), `pipe` ($g \circ f$)
* **Predicate Combinators:** `negate`, `both`, `either`

### `library/list.mylisp`
* **Folds & Reductions:** `foldl`, `foldr`, `reduce`, `reduce-r`
* **Transformations:** `map`, `flat-map`, `filter`, `reject`, `reverse`, `append`, `append-all`
* **Inspection & Aggregation:** `length`, `get`, `uncurry`, `sum-all`, `prod-all`, `concat-all`

### `library/math.mylisp`
* **Basic Arithmetic & Clamping:** `inc`, `dec`, `abs`, `sign`, `min`, `max`, `average`, `clamp`
* **Predicates:** `zero?`, `positive?`, `negative?`, `even`, `odd`, `divides?`
* **List Aggregations:** `min-list`, `max-list`, `average-list`
* **Number Theory & Sequences:** `gcd`, `lcm`, `fact`, `fib` (tail-recursive $O(n)$)

### `library/strings.mylisp`
* **Inspection & Conversion:** `implode`, `string-length`, `string-empty?`, `string-reverse`, `palindrome?`
* **Indexing & Slicing:** `string-ref`, `substring`
* **Search & Matching:** `starts-with?`, `ends-with?`, `contains?`, `index-of`
* **Manipulation & Formatting:** `string-repeat`, `string-join`, `string-split`, `string-replace`, `string-trim-left`, `string-trim-right`, `string-trim`

---

## Example Program

```lisp
(import ("library/stdlib.mylisp")
    (let* (
            (scores '(85 92 78 95 88))
            (passing (filter (lambda (s) (>= s 80)) scores))
            (avg (round (average-list passing)))
            (summary (string-join " | "
                         (list (concat "Passing: " (int->string (length passing)))
                               (concat "Average: " (int->string avg)))))
          )
        summary))
;; => constant : "Passing: 4 | Average: 90"
```
