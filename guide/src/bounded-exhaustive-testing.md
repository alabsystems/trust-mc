<!-- Author: Andrew Yates <andrewyates.name@gmail.com> -->
<!-- dscan:allow(volatile_numbers) -->
# Bounded Exhaustive Testing

trust-mc includes a bounded exhaustive testing harness that enumerates small Rust
programs, runs trust-mc and concrete execution, and compares results. This provides
high confidence in the MIR-to-SMT translation for a well-defined Rust subset.

The harness lives in `scripts/bounded_exhaustive.py`. It defines a small
grammar and configurable bounds to keep the search finite.

## Grammar

### Types

```
Ty ::= i32 | i64 | bool
```

### Expressions

```
Expr ::= Literal
       | Variable
       | UnaryOp Expr
       | Expr BinaryOp Expr

Literal ::= IntLit | BoolLit
IntLit  ::= -1 | 0 | 1 | 2
BoolLit ::= true | false
```

### Operators

```
UnaryOp  ::= - | !
ArithOp  ::= + | - | * | / | %
CmpOp    ::= == | != | < | <= | > | >=
BoolOp   ::= && | ||
BinaryOp ::= ArithOp | CmpOp | BoolOp
```

### Statements

```
Stmt ::= AssignStmt | IfStmt | WhileStmt

AssignStmt ::= Variable = Expr ;
IfStmt     ::= if Expr<bool> { Stmt } else { Stmt }
WhileStmt  ::= while Expr<bool> { Stmt }
```

Note: `Expr<bool>` denotes an expression whose type is `bool`.

### Programs

```
Program ::= fn main() { VarDecl* Stmt* assert!(Expr<bool>); }
VarDecl ::= let mut Variable: Ty = Default;
```

## Bounds (CLI-configurable)

Default bounds are intentionally small to prevent exponential blowup.

| Option | Default | Description |
|--------|---------|-------------|
| `--max-programs` | 10,000 | Maximum programs to test |
| `--max-programs-per-type` | 0 | Limit per type assignment (0 = global cap) |
| `--max-vars` | 3 | Variables per program (1-3) |
| `--max-expr-size` | 3 | Maximum AST depth for expressions |
| `--max-stmts` | 3 | Statements per program |
| `--max-depth` | 1 | Control-flow nesting depth |
| `--max-loop-iters` | 2 | Loop iteration bound |
| `--max-statements` | 1000 | Max statements to generate per type (prevents OOM) |

### Additional Options

| Option | Description |
|--------|-------------|
| `--vary-types` | Enumerate all type assignments (not just default) |
| `--fail-fast` | Stop on first mismatch |
| `--no-trust-mc` | Skip trust-mc verification (concrete only) |
| `--no-concrete` | Skip concrete execution (trust-mc only) |
| `--output-dir` | Output directory (default: `out/bounded_exhaustive`) |
| `--trust-mc` | Path to trust-mc script (default: `scripts/trust-mc`) |
| `--rustc` | Path to rustc (default: `rustc`) |

## Canonicalization Rules

To reduce duplicates, the generator canonicalizes commutative operators:
`+`, `*`, `==`, `!=`, `&&`, `||`.

Division and modulo only use safe divisors (`1`, `2`, `-1`) to avoid undefined
behavior.

## Example

```bash
# Run 100 test programs with small expressions
python3 scripts/bounded_exhaustive.py --max-programs 100 --max-expr-size 2

# Results saved to out/bounded_exhaustive/
# - summary.json: test statistics
# - mismatches/: programs where trust-mc and concrete execution disagree
```

### Quick Smoke Test

```bash
# Fast sanity check (generates programs without running verifiers)
python3 scripts/bounded_exhaustive.py --max-programs 10 --no-trust-mc --no-concrete
```
