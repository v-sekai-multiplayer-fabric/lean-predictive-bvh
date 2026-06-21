-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee

import Lake
open System Lake DSL

package «optimal-partition» where

-- Dependency for flat ECS-style E-node and E-class storage patterns
require «truth_research_zk» from git
  "https://github.com/V-Sekai-fire/truth_research_zk.git" @ "add-i64-r128-emitters-fix-mapscalar"

require LeanSlang from git
  "https://github.com/V-Sekai-fire/lean-slang.git" @ "v0.0.5"

-- ── Hexagon clusters (core/ports/adapters per the hexagonal convention) ───────
-- Each cluster is a lean_lib rooted at its aggregator file (e.g. PredictiveBvh.lean),
-- which imports that cluster's module closure. The old monolithic `PredictiveBVH`
-- library was split into these along the dependency seams.

-- Shared primitive types (the common vocabulary every core builds on).
lean_lib Shared where
  roots := #[`Shared]

-- The predictive spatial-oracle hexagon (ghost expansion + SAH + broadphase).
lean_lib PredictiveBvh where
  roots := #[`PredictiveBvh]

-- Humanoid range-of-motion / IK-constraint hexagon.
lean_lib HumanoidRom where
  roots := #[`HumanoidRom]

-- Fabric networking / SLA hexagon.
lean_lib FabricProtocol where
  roots := #[`FabricProtocol]

-- Authority-interest / solve-order hexagon.
lean_lib InterestManagement where
  roots := #[`InterestManagement]

-- Relationship-based access-control hexagon (NoGod / ReBAC).
lean_lib Rebac where
  roots := #[`Rebac]

-- AmoLean C code generator: writes thirdparty/predictive_bvh/predictive_bvh.h.
-- Lives in the predictive-bvh adapters layer (a driven C-header sink).
@[default_target]
lean_exe «bvh-codegen» where
  root := `PredictiveBvh.adapters.CodeGen
  supportInterpreter := true
