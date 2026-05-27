-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- Minimal protobuf wire-format parser for AddBiomechanics .b3d files.
--
-- The b3d format is:
--   [8 bytes: int64 LE header_size]
--   [header_size bytes: protobuf SubjectOnDiskHeader]
--   [frames...]
--
-- We only need: num_dofs, num_trials, and per-frame pos[] (joint angles).
-- The pos[] field is repeated double (field 1 in SubjectOnDiskProcessingPassFrame).

namespace PredictiveBVH.B3DParser

-- ── Protobuf wire format primitives ─────────────────────────────────────────

/-- Read a little-endian Int64 from 8 bytes. -/
def readInt64LE (bs : ByteArray) (off : Nat) : Int :=
  if off + 8 > bs.size then 0
  else
    let b0 := (bs.get! off).toNat
    let b1 := (bs.get! (off+1)).toNat
    let b2 := (bs.get! (off+2)).toNat
    let b3 := (bs.get! (off+3)).toNat
    let b4 := (bs.get! (off+4)).toNat
    let b5 := (bs.get! (off+5)).toNat
    let b6 := (bs.get! (off+6)).toNat
    let b7 := (bs.get! (off+7)).toNat
    (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216 +
     b4 * 4294967296 + b5 * 1099511627776 +
     b6 * 281474976710656 + b7 * 72057594037927936 : Nat)

/-- Read a little-endian Float64 (IEEE 754) from 8 bytes as raw bits. -/
def readFloat64LEBits (bs : ByteArray) (off : Nat) : UInt64 :=
  if off + 8 > bs.size then 0
  else
    let b0 := (bs.get! off).toUInt64
    let b1 := (bs.get! (off+1)).toUInt64
    let b2 := (bs.get! (off+2)).toUInt64
    let b3 := (bs.get! (off+3)).toUInt64
    let b4 := (bs.get! (off+4)).toUInt64
    let b5 := (bs.get! (off+5)).toUInt64
    let b6 := (bs.get! (off+6)).toUInt64
    let b7 := (bs.get! (off+7)).toUInt64
    b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
    (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

/-- Convert IEEE 754 double bits to a fixed-point integer (millidegrees).
    sign × (1 + mantissa/2^52) × 2^(exponent - 1023) × 1000
    Approximation: extract sign + rough magnitude for ROM purposes. -/
def float64BitsToMillideg (bits : UInt64) : Int :=
  let sign := if bits >>> 63 == 1 then -1 else 1
  let exponent := ((bits >>> 52) &&& 0x7FF).toNat
  let mantissa := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if exponent == 0 then 0  -- subnormal ≈ 0
  else if exponent == 0x7FF then 0  -- inf/nan
  else
    -- value ≈ sign × 2^(exp-1023) × (1 + mantissa/2^52)
    -- Convert radians to millidegrees: × 180000 / π ≈ × 57296
    let exp_signed : Int := (exponent : Int) - 1023
    let frac_1000 : Int := 1000 + (mantissa * 1000 / 4503599627370496)  -- mantissa/2^52 × 1000
    let base : Int := if exp_signed >= 0
      then frac_1000 * (2 ^ exp_signed.toNat)
      else frac_1000 / (2 ^ (-exp_signed).toNat)
    -- base is value × 1000. Radians to millidegrees: × 180000/π ≈ × 57296.
    -- millideg = (base / 1000) × 57296 = base × 57296 / 1000
    sign * base * 57296 / 1000

/-- Read a protobuf varint from bytes. Returns (value, bytes_consumed). -/
def readVarint (bs : ByteArray) (off : Nat) : Nat × Nat :=
  let rec go (pos shift acc : Nat) : (fuel : Nat) → Nat × Nat
    | 0 => (acc, pos - off)
    | fuel + 1 =>
      if pos >= bs.size then (acc, pos - off)
      else
        let b := (bs.get! pos).toNat
        let acc' := acc ||| ((b &&& 0x7F) <<< shift)
        if b &&& 0x80 == 0 then (acc', pos + 1 - off)
        else go (pos + 1) (shift + 7) acc' fuel
  go off 0 0 10

/-- Parse a protobuf Int32 field (field_number, wire_type=0). -/
structure ProtoField where
  fieldNum : Nat
  wireType : Nat  -- 0=varint, 1=64bit, 2=length-delimited, 5=32bit
  deriving Repr

def readFieldTag (bs : ByteArray) (off : Nat) : ProtoField × Nat :=
  let (tag, consumed) := readVarint bs off
  ({ fieldNum := tag >>> 3, wireType := tag &&& 7 }, consumed)

-- ── B3D header parsing ──────────────────────────────────────────────────────

structure B3DHeader where
  numDofs   : Nat
  numTrials : Nat
  rawSensorFrameSize : Nat
  processingPassFrameSize : Nat
  heightM   : Int  -- millimetres
  massKg    : Int  -- grams
  deriving Repr

/-- Parse SubjectOnDiskHeader from protobuf bytes. Extract key fields. -/
def parseHeader (bs : ByteArray) (headerStart headerEnd : Nat) : B3DHeader :=
  let rec go (pos : Nat) (h : B3DHeader) : (fuel : Nat) → B3DHeader
    | 0 => h
    | fuel + 1 =>
      if pos >= headerEnd then h
      else
        let (field, tagSize) := readFieldTag bs pos
        let pos' := pos + tagSize
        match field.wireType with
        | 0 =>
          let (val, valSize) := readVarint bs pos'
          let h' := match field.fieldNum with
            | 1 => { h with numDofs := val }
            | 2 => { h with numTrials := val }
            | 3 => { h with rawSensorFrameSize := val }
            | 4 => { h with processingPassFrameSize := val }
            | _ => h
          go (pos' + valSize) h' fuel
        | 1 =>
          let h' := match field.fieldNum with
            | 14 => { h with heightM := readInt64LE bs pos' }
            | 15 => { h with massKg := readInt64LE bs pos' }
            | _ => h
          go (pos' + 8) h' fuel
        | 2 =>
          let (len, lenSize) := readVarint bs pos'
          go (pos' + lenSize + len) h fuel
        | 5 =>
          go (pos' + 4) h fuel
        | _ => h
  go headerStart { numDofs := 0, numTrials := 0, rawSensorFrameSize := 0,
                   processingPassFrameSize := 0, heightM := 0, massKg := 0 } 10000

-- ── Frame parsing: extract pos[] joint angles ───────────────────────────────

/-- Extract the pos[] repeated double from a processing pass frame.
    Field 1, wire type 1 (packed repeated double). -/
def extractPosFromFrame (bs : ByteArray) (frameStart frameEnd numDofs : Nat) : Array Int :=
  -- pos is field 1, which for packed repeated double is wire type 2 (length-delimited)
  -- containing numDofs × 8 bytes of IEEE 754 doubles.
  let rec findPosField (pos : Nat) : (fuel : Nat) → Option (Nat × Nat)
    | 0 => none
    | fuel + 1 =>
      if pos >= frameEnd then none
      else
        let (field, tagSize) := readFieldTag bs pos
        let pos' := pos + tagSize
        match field.wireType with
        | 0 => let (_, vs) := readVarint bs pos'; findPosField (pos' + vs) fuel
        | 1 => if field.fieldNum == 1 then some (pos', 8) else findPosField (pos' + 8) fuel
        | 2 =>
          let (len, ls) := readVarint bs pos'
          if field.fieldNum == 1 then some (pos' + ls, len)
          else findPosField (pos' + ls + len) fuel
        | 5 => findPosField (pos' + 4) fuel
        | _ => none
  match findPosField frameStart 1000 with
  | none => #[]
  | some (dataStart, dataLen) =>
    let nDoubles := dataLen / 8
    (Array.range nDoubles).map fun i =>
      let bits := readFloat64LEBits bs (dataStart + i * 8)
      float64BitsToMillideg bits

-- ── Top-level: parse a .b3d file ────────────────────────────────────────────

/-- Parse a .b3d file. Returns the header and a function to extract frame data. -/
def parseB3D (bs : ByteArray) : Option B3DHeader :=
  if bs.size < 8 then none
  else
    let headerSize := (readInt64LE bs 0).toNat
    if 8 + headerSize > bs.size then none
    else some (parseHeader bs 8 (8 + headerSize))

-- ── Verification ────────────────────────────────────────────────────────────

/-- Varint encoding of 150 = [0x96, 0x01]. -/
theorem varint_150 :
    readVarint ⟨#[0x96, 0x01]⟩ 0 = (150, 2) := by native_decide

/-- Field tag: field 1, wire type 0 = byte 0x08. -/
theorem field_tag_1_0 :
    let r := readFieldTag ⟨#[0x08]⟩ 0
    r.1.fieldNum = 1 ∧ r.1.wireType = 0 := by native_decide

/-- π/2 ≈ 1.5708 rad → 89954 millidegrees (≈90°). -/
theorem pi_half_to_mdeg :
    float64BitsToMillideg 0x3FF921FB54442D18 > 89000 ∧
    float64BitsToMillideg 0x3FF921FB54442D18 < 91000 := by native_decide

/-- 1.0 rad → 57296 millidegrees (≈57.3°). -/
theorem one_rad_to_mdeg :
    float64BitsToMillideg 0x3FF0000000000000 = 57296 := by native_decide

end PredictiveBVH.B3DParser
