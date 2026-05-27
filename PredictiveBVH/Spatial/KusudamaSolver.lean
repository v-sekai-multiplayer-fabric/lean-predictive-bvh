-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- Single-source kusudama constraint solver.
-- Defined once as LeanSlang AST, emitted to Slang source.
-- The emitted code is used by both the Godot shader (GPU gizmo)
-- and the C++ solver (CPU constraint).
--
-- Pattern: Lean AST → emit → pin committed source with native_decide.

import LeanSlang.Types
import LeanSlang.AST
import LeanSlang.Emit

namespace PredictiveBVH.KusudamaSolver

open LeanSlang

-- ── is_in_cone ──────────────────────────────────────────────────────────────
-- Returns: -1 inside, 0 on boundary, 1 outside.

private def isInConeBody : List SlangStmt :=
  [ .declInit (.scalar .float) "arc_dist"
      (.call "acos" [.call "dot" [.var "dir", .member (.var "cone") "xyz"]])
  , .declInit (.scalar .float) "half_bw"
      (.bin "/" (.var "boundary_width") (.litFloat 2.0))
  , .ifThen
      (.bin ">" (.var "arc_dist")
        (.bin "+" (.member (.var "cone") "w") (.var "half_bw")))
      [.retExpr (.litUint 1)]
      []
  , .ifThen
      (.bin "<" (.var "arc_dist")
        (.bin "-" (.member (.var "cone") "w") (.var "half_bw")))
      [.retExpr (.call "int" [.un "-" (.litUint 1)])]
      []
  , .retExpr (.litUint 0)
  ]

private def isInConeFn : SlangFunctionDecl :=
  { retType := .scalar .int
    name    := "kusudama_is_in_cone"
    params  := [ { name := "dir",            type := .vec .float 3 }
               , { name := "cone",           type := .vec .float 4 }
               , { name := "boundary_width", type := .scalar .float }
               ]
    body    := isInConeBody }

-- ── is_in_inter_cone_path ───────────────────────────────────────────────────
-- Cross-product half-space test for the tangent-path region between two cones.

private def isInInterConePathBody : List SlangStmt :=
  [ .declInit (.vec .float 3) "c1xc2"
      (.call "cross" [.member (.var "cone_1") "xyz", .member (.var "cone_2") "xyz"])
  , .declInit (.scalar .float) "side"
      (.call "dot" [.var "dir", .var "c1xc2"])
  , .ifThen (.bin "<" (.var "side") (.litFloat 0.0))
      [ .declInit (.vec .float 3) "c1xt1"
          (.call "cross" [.member (.var "cone_1") "xyz", .member (.var "tangent_1") "xyz"])
      , .declInit (.vec .float 3) "t1xc2"
          (.call "cross" [.member (.var "tangent_1") "xyz", .member (.var "cone_2") "xyz"])
      , .retExpr
          (.bin "&&"
            (.bin ">" (.call "dot" [.var "dir", .var "c1xt1"]) (.litFloat 0.0))
            (.bin ">" (.call "dot" [.var "dir", .var "t1xc2"]) (.litFloat 0.0)))
      ]
      [ .declInit (.vec .float 3) "t2xc1"
          (.call "cross" [.member (.var "tangent_2") "xyz", .member (.var "cone_1") "xyz"])
      , .declInit (.vec .float 3) "c2xt2"
          (.call "cross" [.member (.var "cone_2") "xyz", .member (.var "tangent_2") "xyz"])
      , .retExpr
          (.bin "&&"
            (.bin ">" (.call "dot" [.var "dir", .var "c2xt2"]) (.litFloat 0.0))
            (.bin ">" (.call "dot" [.var "dir", .var "t2xc1"]) (.litFloat 0.0)))
      ]
  ]

private def isInInterConePathFn : SlangFunctionDecl :=
  { retType := .scalar .bool
    name    := "kusudama_is_in_inter_cone_path"
    params  := [ { name := "dir",       type := .vec .float 3 }
               , { name := "tangent_1", type := .vec .float 4 }
               , { name := "cone_1",    type := .vec .float 4 }
               , { name := "tangent_2", type := .vec .float 4 }
               , { name := "cone_2",    type := .vec .float 4 }
               ]
    body    := isInInterConePathBody }

-- ── Shader module ───────────────────────────────────────────────────────────

def kusudamaSolverModule : SlangShaderModule :=
  { functions := [isInConeFn, isInInterConePathFn] }

/-- Slang source derived from the AST. Single source of truth. -/
def kusudamaSolverSource : String := LeanSlang.emit kusudamaSolverModule

-- ── Pin: committed source must match emitted ────────────────────────────────

/-- Committed copy of the emitted Slang source. If the AST changes,
    this literal must be updated — the proof enforces byte-identity. -/
def committedSource : String :=
"int kusudama_is_in_cone(float3 dir, float4 cone, float boundary_width) {
  float arc_dist = acos(dot(dir, cone.xyz));
  float half_bw = (boundary_width / 2.000000);
  if ((arc_dist > (cone.w + half_bw))) {
    return 1u;
  }
  if ((arc_dist < (cone.w - half_bw))) {
    return int((-1u));
  }
  return 0u;
}

bool kusudama_is_in_inter_cone_path(float3 dir, float4 tangent_1, float4 cone_1, float4 tangent_2, float4 cone_2) {
  float3 c1xc2 = cross(cone_1.xyz, cone_2.xyz);
  float side = dot(dir, c1xc2);
  if ((side < 0.000000)) {
    float3 c1xt1 = cross(cone_1.xyz, tangent_1.xyz);
    float3 t1xc2 = cross(tangent_1.xyz, cone_2.xyz);
    return ((dot(dir, c1xt1) > 0.000000) && (dot(dir, t1xc2) > 0.000000));
  } else {
    float3 t2xc1 = cross(tangent_2.xyz, cone_1.xyz);
    float3 c2xt2 = cross(cone_2.xyz, tangent_2.xyz);
    return ((dot(dir, c2xt2) > 0.000000) && (dot(dir, t2xc1) > 0.000000));
  }
}"

/-- Byte-pin: committed = emitted. If the AST changes, this breaks. -/
theorem committed_matches : committedSource = kusudamaSolverSource := by native_decide

end PredictiveBVH.KusudamaSolver
