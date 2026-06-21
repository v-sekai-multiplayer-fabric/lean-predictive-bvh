# FabricProtocol

The fabric networking/SLA hexagon: saturation, waypoint bounds, abyssal SLA (core).

## Hexagon layout

- `core/` — dependency-free domain logic + proofs
- `ports/` — narrow driving (source) / driven (sink) contracts
- `adapters/` — concrete I/O at the edges

## Sibling wiring

- Shared
- connection-fsm / http3-queue — the transport siblings on the /fabric wire
