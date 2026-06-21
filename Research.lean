-- Non-gated tier (NOT on the CI production gate). Aspirational / model-level
-- proofs and modules currently broken against the pinned toolchain. Built for
-- signal with continue-on-error. Build explicitly with `lake build Research`.
--   SolveOrder        — uses Array.mem_toList.mp (removed in this toolchain)
--   ROMTool           — typeclass synthesis failure (ROMTool.lean:100)
--   Partition/Saturate/Fabric/AuthorityInterest/ReBAC — research-tier proofs
import PredictiveBvh.core.Partition
import FabricProtocol.core.Fabric
import FabricProtocol.core.Saturate
import InterestManagement.core.AuthorityInterest
import InterestManagement.core.SolveOrder
import Rebac.core.ReBAC
import HumanoidRom.adapters.ROMTool
