-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- Unified kusudama constraint solver.
-- Defined once as LeanSlang AST, emitted to Slang source.
-- The SAME function runs in both the Godot shader (GPU) and C++ solver (CPU).
--
-- kusudama_solve(dir, cone_count, cone_sequence) → float3:
--   Returns dir if inside allowed region (cone or tangent path).
--   Returns projected direction if outside (gnomonic 2D nearest-point).
--
-- Shader: if dot(solve(dir), dir) > 0.9999 → colored, else transparent.
-- C++:    new_bone_dir = solve(dir).

import LeanSlang.Types
import LeanSlang.AST
import LeanSlang.Emit

namespace PredictiveBVH.KusudamaSolver

open LeanSlang

private def maxCones := 30

-- ── Helper: get_cone_center extracts the i-th cone from cone_sequence ───────
-- Layout: cone0, tan0_1, tan0_2, cone1, tan1_1, tan1_2, ..., coneN-1
-- Cone i is at index i*3 (for i>0) or 0 (for i=0).
-- Actually simpler: cone_sequence[0] = cone0, [1]=tan0_1, [2]=tan0_2, [3]=cone1, ...
-- So cone i is at index i*3 for i≥1, and 0 for i=0.  Or: 0, 3, 6, 9, ...
-- Wait, the layout is: cone0, (tan01_1, tan01_2, cone1), (tan12_1, tan12_2, cone2), ...
-- So cone 0 = [0], cone 1 = [3], cone 2 = [6], ..., cone i = [i*3] for all i.

-- ── kusudama_solve: the unified solver ──────────────────────────────────────

private def solveBody : List SlangStmt :=
  -- 1. Cone containment
  [ .forCount "ci" (.litUint 0) (.var "cone_count")
      [ .declInit (.scalar .uint) "idx" (.bin "*" (.var "ci") (.litUint 3))
      , .declInit (.vec .float 4) "cone" (.index (.var "cone_sequence") (.var "idx"))
      , .ifNoElse
          (.bin "<=" (.call "acos" [.call "dot" [.var "dir", .member (.var "cone") "xyz"]])
                     (.member (.var "cone") "w"))
          [.retExpr (.var "dir")]
      ]
  -- 2. Tangent path containment (open chain)
  , .forCount "ti" (.litUint 0) (.bin "-" (.var "cone_count") (.litUint 1))
      [ .declInit (.scalar .uint) "base" (.bin "*" (.var "ti") (.litUint 3))
      , .declInit (.vec .float 4) "cone_1" (.index (.var "cone_sequence") (.var "base"))
      , .declInit (.vec .float 4) "tangent_1" (.index (.var "cone_sequence") (.bin "+" (.var "base") (.litUint 1)))
      , .declInit (.vec .float 4) "tangent_2" (.index (.var "cone_sequence") (.bin "+" (.var "base") (.litUint 2)))
      , .declInit (.vec .float 4) "cone_2" (.index (.var "cone_sequence") (.bin "+" (.var "base") (.litUint 3)))
      , .declInit (.vec .float 3) "c1xc2"
          (.call "cross" [.member (.var "cone_1") "xyz", .member (.var "cone_2") "xyz"])
      , .declInit (.scalar .float) "side" (.call "dot" [.var "dir", .var "c1xc2"])
      , .ifThen (.bin "<" (.var "side") (.litFloat 0.0))
          [ .declInit (.vec .float 3) "c1xt1"
              (.call "cross" [.member (.var "cone_1") "xyz", .member (.var "tangent_1") "xyz"])
          , .declInit (.vec .float 3) "t1xc2"
              (.call "cross" [.member (.var "tangent_1") "xyz", .member (.var "cone_2") "xyz"])
          , .ifNoElse
              (.bin "&&"
                (.bin ">" (.call "dot" [.var "dir", .var "c1xt1"]) (.litFloat 0.0))
                (.bin ">" (.call "dot" [.var "dir", .var "t1xc2"]) (.litFloat 0.0)))
              [ .ifNoElse
                  (.bin "&&"
                    (.bin "<=" (.call "dot" [.var "dir", .member (.var "tangent_1") "xyz"])
                              (.call "cos" [.member (.var "tangent_1") "w"]))
                    (.bin "<=" (.call "dot" [.var "dir", .member (.var "tangent_2") "xyz"])
                              (.call "cos" [.member (.var "tangent_2") "w"])))
                  [.retExpr (.var "dir")]
              ]
          ]
          [ .declInit (.vec .float 3) "t2xc1"
              (.call "cross" [.member (.var "tangent_2") "xyz", .member (.var "cone_1") "xyz"])
          , .declInit (.vec .float 3) "c2xt2"
              (.call "cross" [.member (.var "cone_2") "xyz", .member (.var "tangent_2") "xyz"])
          , .ifNoElse
              (.bin "&&"
                (.bin ">" (.call "dot" [.var "dir", .var "c2xt2"]) (.litFloat 0.0))
                (.bin ">" (.call "dot" [.var "dir", .var "t2xc1"]) (.litFloat 0.0)))
              [ .ifNoElse
                  (.bin "&&"
                    (.bin "<=" (.call "dot" [.var "dir", .member (.var "tangent_1") "xyz"])
                              (.call "cos" [.member (.var "tangent_1") "w"]))
                    (.bin "<=" (.call "dot" [.var "dir", .member (.var "tangent_2") "xyz"])
                              (.call "cos" [.member (.var "tangent_2") "w"])))
                  [.retExpr (.var "dir")]
              ]
          ]
      ]
  -- 3. Gnomonic projection
  , .declInit (.vec .float 3) "center" (.call "float3" [.litFloat 0.0, .litFloat 0.0, .litFloat 0.0])
  , .forCount "gi" (.litUint 0) (.var "cone_count")
      [ .assign (.var "center")
          (.bin "+" (.var "center")
            (.member (.index (.var "cone_sequence") (.bin "*" (.var "gi") (.litUint 3))) "xyz"))
      ]
  , .assign (.var "center") (.call "normalize" [.var "center"])
  -- Build tangent-plane basis
  , .declInit (.vec .float 3) "u_axis"
      (.ternary
        (.bin "||"
          (.bin "!=" (.member (.var "center") "x") (.litFloat 0.0))
          (.bin "!=" (.member (.var "center") "y") (.litFloat 0.0)))
        (.call "normalize" [.call "float3"
          [.un "-" (.member (.var "center") "y"),
           .member (.var "center") "x",
           .litFloat 0.0]])
        (.call "normalize" [.call "float3"
          [.member (.var "center") "z",
           .litFloat 0.0,
           .un "-" (.member (.var "center") "x")]]))
  , .declInit (.vec .float 3) "v_axis" (.call "normalize" [.call "cross" [.var "center", .var "u_axis"]])
  -- Project input to 2D
  , .declInit (.scalar .float) "p_dot_c" (.call "max" [.call "dot" [.var "dir", .var "center"], .litFloat 0.000001])
  , .declInit (.vec .float 2) "p2d"
      (.call "float2"
        [.bin "/" (.call "dot" [.var "dir", .var "u_axis"]) (.var "p_dot_c"),
         .bin "/" (.call "dot" [.var "dir", .var "v_axis"]) (.var "p_dot_c")])
  -- Find nearest edge in 2D (open chain)
  , .declInit (.scalar .float) "best_dist" (.litFloat 1000000.0)
  , .declInit (.vec .float 2) "best2d" (.var "p2d")
  , .forCount "ei" (.litUint 0) (.bin "-" (.var "cone_count") (.litUint 1))
      [ .declInit (.scalar .uint) "ai" (.bin "*" (.var "ei") (.litUint 3))
      , .declInit (.scalar .uint) "bi" (.bin "*" (.bin "+" (.var "ei") (.litUint 1)) (.litUint 3))
      , .declInit (.vec .float 3) "va" (.member (.index (.var "cone_sequence") (.var "ai")) "xyz")
      , .declInit (.vec .float 3) "vb" (.member (.index (.var "cone_sequence") (.var "bi")) "xyz")
      , .declInit (.scalar .float) "da" (.call "max" [.call "dot" [.var "va", .var "center"], .litFloat 0.000001])
      , .declInit (.scalar .float) "db" (.call "max" [.call "dot" [.var "vb", .var "center"], .litFloat 0.000001])
      , .declInit (.vec .float 2) "a2d"
          (.call "float2"
            [.bin "/" (.call "dot" [.var "va", .var "u_axis"]) (.var "da"),
             .bin "/" (.call "dot" [.var "va", .var "v_axis"]) (.var "da")])
      , .declInit (.vec .float 2) "b2d"
          (.call "float2"
            [.bin "/" (.call "dot" [.var "vb", .var "u_axis"]) (.var "db"),
             .bin "/" (.call "dot" [.var "vb", .var "v_axis"]) (.var "db")])
      , .declInit (.vec .float 2) "edge" (.bin "-" (.var "b2d") (.var "a2d"))
      , .declInit (.scalar .float) "edge_len_sq" (.call "dot" [.var "edge", .var "edge"])
      , .declInit (.scalar .float) "t"
          (.call "clamp"
            [.bin "/" (.call "dot" [.bin "-" (.var "p2d") (.var "a2d"), .var "edge"]) (.call "max" [.var "edge_len_sq", .litFloat 0.000001]),
             .litFloat 0.0, .litFloat 1.0])
      , .declInit (.vec .float 2) "cand" (.bin "+" (.var "a2d") (.bin "*" (.var "edge") (.var "t")))
      , .declInit (.scalar .float) "d" (.call "distance" [.var "p2d", .var "cand"])
      , .ifNoElse (.bin "<" (.var "d") (.var "best_dist"))
          [ .assign (.var "best_dist") (.var "d")
          , .assign (.var "best2d") (.var "cand")
          ]
      ]
  , .retExpr (.call "normalize"
      [.bin "+" (.var "center")
        (.bin "+" (.bin "*" (.var "u_axis") (.member (.var "best2d") "x"))
                  (.bin "*" (.var "v_axis") (.member (.var "best2d") "y")))])
  ]

private def solveFn : SlangFunctionDecl :=
  { retType := .vec .float 3
    name    := "kusudama_solve"
    params  := [ { name := "dir",           type := .vec .float 3 }
               , { name := "cone_count",    type := .scalar .uint }
               , { name := "cone_sequence", type := .named s!"float4[{maxCones * 3 + 1}]" }
               ]
    body    := solveBody }

-- NOTE: The C++ caller applies a twist-free change-of-basis correction
-- using Godot's Quaternion API (not expressible in Slang):
--   rest_to_input     = Quaternion(forward, input_dir)
--   rest_to_constrained = Quaternion(forward, kusudama_solve(input_dir, ...))
--   correction = rest_to_constrained * inverse(rest_to_input)
--   result = correction.xform(input_vector)
-- This preserves twist by routing both rotations through the rest pose.

def kusudamaSolverModule : SlangShaderModule :=
  { functions := [solveFn] }

-- The IK solver applies the constraint rotation to the ENTIRE downstream
-- chain, not just the immediate bone. See iterate_ik_3d.h:
--   Quaternion correction = Quaternion(input_dir, constrained_dir);
--   for each downstream joint: chain[j] = chain[head] + correction.xform(chain[j] - chain[head]);

def kusudamaSolverSource : String := LeanSlang.emit kusudamaSolverModule

-- Write the emitted Slang to a file for slangc compilation.
-- slangc kusudama_solve.slang -target glsl → GLSL for Godot shader
-- slangc kusudama_solve.slang -target spirv → SPIR-V for Vulkan
-- The C++ solver uses the same logic via slangc -target cpp or direct inclusion.

def emitSlangFile : IO Unit := do
  IO.FS.writeFile "kusudama_solve.slang" kusudamaSolverSource
  IO.println s!"wrote kusudama_solve.slang ({kusudamaSolverSource.length} bytes)"

end PredictiveBVH.KusudamaSolver
