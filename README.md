# SH-GLT Lean Formalization

Lean 4 + Mathlib formalization accompanying the paper  
**“SH-GLT: Sparse-History Guided Candidate Search for Full-Bandit Submodular Maximization.”**

## Verification

The formalization was checked successfully with Lean 4 and Mathlib using:

```bash
lake build
lake env lean Main.lean
