# AENEAS_DIR: path to an AeneasVerif/aeneas checkout with charon and aeneas built.
# CHARON / AENEAS: paths to the binaries, overriding AENEAS_DIR (e.g. for an
# unpacked aeneas release tarball, where both sit at the top level).
aeneas_dir := env("AENEAS_DIR", "")
charon := env("CHARON", aeneas_dir / "charon/bin/charon")
aeneas := env("AENEAS", aeneas_dir / "bin/aeneas")

[private]
default:
    @just --list

# Regenerate proofs/PackedPtr/Code/PackedPtr.lean from src/bits.rs
gen-proofs:
    @test -x "{{charon}}" -a -x "{{aeneas}}" || { echo "error: set AENEAS_DIR to an aeneas checkout" >&2; exit 1; }
    "{{charon}}" cargo --preset=aeneas --start-from=crate::bits --dest-file=packed_ptr.llbc
    "{{aeneas}}" -backend lean packed_ptr.llbc -dest proofs -subdir /PackedPtr/Code -namespace PackedPtr

# Build the docs
doc *args:
    cargo doc --no-deps {{args}}

# Build the docs, including private items
doc-priv *args:
    cargo doc --no-deps --document-private-items {{args}}

# Check the proofs
check-proofs *args:
    cd proofs && lake build {{args}}
