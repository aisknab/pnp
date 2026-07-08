import Lake
open Lake DSL

package pnp_lean_bridge where
  -- Deliberately mathlib-free for the first bridge pass.
  -- The goal is a small checker-trust theorem bridge that builds quickly in CI.

lean_lib PNP where
  srcDir := "lean"
