import Lake
open Lake DSL

package dao where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

lean_lib DAO where
  -- Main DAO Theory library