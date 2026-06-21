-- HumanoidRom hexagon cluster aggregator — production tier.
-- Range-of-motion / IK constraints (core); B3D/AddBiomechanics + shader (adapters).
-- adapters/ROMTool is in Research.lean (pre-existing typeclass-synthesis failure).
import HumanoidRom.adapters.AddBiomechanicsROM
import HumanoidRom.adapters.B3DParser
import HumanoidRom.adapters.KusudamaShader
import HumanoidRom.core.EWBIKDecomposition
import HumanoidRom.core.HumanoidConstraints
import HumanoidRom.core.KusudamaSolver
import HumanoidRom.core.MeshROM
import HumanoidRom.core.MuscleConstraint
import HumanoidRom.core.PrismaticJoint
import HumanoidRom.core.ROMPipeline
import HumanoidRom.core.ROMPredictor
import HumanoidRom.core.ROMSampling
import HumanoidRom.core.SphericalPolygon
import HumanoidRom.core.StarHeadings
