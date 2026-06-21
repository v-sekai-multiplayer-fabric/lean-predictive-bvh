# InterestManagement

Authority-interest + solve-order hexagon: who-sees-whom and solve sequencing.

## Hexagon layout

- `core/` — dependency-free domain logic + proofs
- `ports/` — narrow driving (source) / driven (sink) contracts
- `adapters/` — concrete I/O at the edges

## Sibling wiring

- FabricProtocol — interest queries source
- Rebac — authority decisions
