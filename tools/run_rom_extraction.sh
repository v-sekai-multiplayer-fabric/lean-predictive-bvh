#!/bin/bash
# SPDX-License-Identifier: MIT
# Run inside WSL Ubuntu to download AddBiomechanics and extract ROM.
set -e

DATA_DIR="/mnt/e/addbiomechanics_data"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
OUTPUT="$SCRIPT_DIR/../PredictiveBVH/Spatial/AddBiomechanicsROM.lean"

echo "=== Step 1: Download AddBiomechanics (Rajagopal with arms) ==="
mkdir -p "$DATA_DIR"
if [ ! -d "$DATA_DIR/protected" ]; then
    echo "Downloading from Google Drive..."
    gdown --folder "https://drive.google.com/drive/folders/1JE4kUDXWRDq6yjkTxH6-VAkLRGodKtr6" -O "$DATA_DIR"
else
    echo "Data already exists in $DATA_DIR"
fi

echo ""
echo "=== Step 2: Extract per-joint ROM ==="
python3 "$SCRIPT_DIR/extract_addbiomechanics_rom.py" \
    --data-dir "$DATA_DIR" \
    --output "$OUTPUT"

echo ""
echo "=== Done ==="
echo "Output: $OUTPUT"
echo "Run 'lake build' to verify Lean proofs with new data."
