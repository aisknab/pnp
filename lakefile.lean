import Lake
open Lake DSL

package pnp_lean_bridge where
  -- Deliberately mathlib-free for the first bridge pass.
  -- The goal is a small checker-trust theorem bridge that builds quickly in CI.

@[default_target]
lean_lib PNP where
  srcDir := "lean"
  roots := #[`PNP]
