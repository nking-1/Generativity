## Operator Notation

DAO provides clean operator notation for logical operations. The notation is scoped to avoid conflicts with other libraries.

### Quick Start
```coq
Require Import DAO.Logic.Operators.
Open Scope dao_scope.

(* Now you can use operators *)
Theorem example : forall P Q, (P AND Q) ==> (Q AND P).
```

### Available Operators

| Operator | Meaning | ASCII |
|----------|---------|-------|
| `AND` | Conjunction | ✓ |
| `OR` | Disjunction | ✓ |
| `==>` | Implication | ✓ |
| `NOT` | Negation | ✓ |
| `IFF` | Equivalence | ✓ |
| `XOR` | Exclusive or | ✓ |
| `NAND` | Not and | ✓ |
| `NOR` | Not or | ✓ |
| `Bot` | Impossibility | ✓ |
| `Top` | Tautology | ✓ |
| `Possible` | Existence | ✓ |
| `Necessary` | Universal | ✓ |
| `Impossible` | No witnesses | ✓ |

### Scope Management

The DAO scope is automatically bound to `Alphacarrier` predicates, so it usually opens automatically.

If needed, you can:
- **Explicitly open**: `Open Scope dao_scope.`
- **Explicitly close**: `Close Scope dao_scope.`
- **Inline usage**: `(P AND Q)%DAO`

### Compatibility

The scoped notation ensures DAO operators don't conflict with other libraries. If another library also defines `AND`, both can coexist by using their respective scopes.