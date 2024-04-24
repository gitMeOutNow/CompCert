# ARM ISA Reordering


## Files
Memory system representation, proof of semantic equality, and reordering is in aarch64/Asm_MemSim.v. Some utility lemmas added to lib/Maps.v and Memory.v

aarch64 specification is in aarch64/Asm.v
## Quick Start w/ OPAM

opam switch create 4.13.1

eval 'opam env'

opam install coq=8.13.2

opam install menhir

./configure aarch64-macos

make all

This will take roughly 20 minutes to build all of CompCert. Verifying each pair of instructions takes significant computational power, so the reordering proof is currently configured to focus on one particular pair. We manually repeat each instruction destruction to give a sense of incremental progress when using an interactive Coq Ide.