import Lake
open Lake DSL

require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "0c19cd5bff9298565362c6ca9c4f48a29033a0e9" / "backends/lean"

package «packed-ptr» {}

@[default_target]
lean_lib «PackedPtr»
