# ARM ISA Reordering


## Files
Memory system representation, proof of semantic equality, and reordering is in aarch64/Asm_MemSim.v. Some utility functions added to lib/Maps.v

ARM specification is in aarch64/Asm.v
## Quick Start w/ OPAM

opam switch create 4.13.1
eval 'opam env'
opam install coq=8.13.2
opam install menhir
./configure aarch64-macos
make all

This will take roughly 20 minutes to build all of CompCert + my stuff. 
Currently, the expected behavior is to fail on line 1942 of MemSim.v, as that proof is currently incomplete.

Once that is completed, then the command will either complete successfully or fail setting up the linker for compcert - either is acceptable as either case means that all Coq code was interpreted correctly.



# Compcert
The formally-verified C compiler.


## Overview
The CompCert C verified compiler is a compiler for a large subset of the
C programming language that generates code for the PowerPC, ARM, x86 and
RISC-V processors.

The distinguishing feature of CompCert is that it has been formally
verified using the Coq proof assistant: the generated assembly code is
formally guaranteed to behave as prescribed by the semantics of the
source C code.

For more information on CompCert (supported platforms, supported C
features, installation instructions, using the compiler, etc), please
refer to the [Web site](https://compcert.org/) and especially
the [user's manual](https://compcert.org/man/).

## License
CompCert is not free software.  This non-commercial release can only
be used for evaluation, research, educational and personal purposes.
A commercial version of CompCert, without this restriction and with
professional support and extra features, can be purchased from
[AbsInt](https://www.absint.com).  See the file `LICENSE` for more
information.

## Copyright
The CompCert verified compiler is Copyright Institut National de
Recherche en Informatique et en Automatique (INRIA) and 
AbsInt Angewandte Informatik GmbH.


## Contact
General discussions on CompCert take place on the
[compcert-users@inria.fr](https://sympa.inria.fr/sympa/info/compcert-users)
mailing list.

For inquiries on the commercial version of CompCert, please contact
info@absint.com
