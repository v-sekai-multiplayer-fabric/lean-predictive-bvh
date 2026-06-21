# HumanoidRom

Humanoid range-of-motion / IK-constraint hexagon: ROM math, Kusudama, muscle/prismatic constraints (core); B3D/AddBiomechanics parsers + GPU shader + python tools (adapters).

## Hexagon layout

- `core/` — dependency-free domain logic + proofs
- `ports/` — narrow driving (source) / driven (sink) contracts
- `adapters/` — concrete I/O at the edges

## Sibling wiring

- Shared — common primitive types
- swing-twist-kusudama / kusudama-constraint-godot — sibling IK repos over the constraint wire
