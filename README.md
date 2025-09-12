Revamping Verilog Semantics for Foundational Verification
=========================================================

Getting Started
---------------

This artifact contains the Rocq (Coq) development accompanying the paper *Revamping Verilog Semantics for Foundational Verification*.

### Directory Content

- `src`: Core framework and case study
  + `Lib`: General-purpose libraries used in the framework
  + `Lang`: Formal syntax and semantics of Verilog (*corresponds to Section 3 of the paper*)
    * `Equiv`: Equivalence between the standard and our semantics (*Section 4*)
  + `Ex`: Total correctness of a RISC-V pipelined processor (*Section 5*)
- `dep`: External dependencies (this artifact already includes all the files; i.e., no need to run `git pull`)
  + `coqutil`: Various data structures and utility lemmas, from https://github.com/mit-plv/coqutil
  + `FreeSim`: The FreeSim library mentioned in the paper
	* We made minor modifications to make it compatible with Coq 8.18.
	* The original version is available at: https://github.com/CCR-project/FreeSim
  + `riscv-coq`: Specification of RISC-V, from https://github.com/mit-plv/riscv-coq

### Requirements

- Make
- OCaml Package Manager (`opam`)

### Build Instructions

From the top-level directory, run the following commands; we do not expect any of these commands to affect your global `opam` environment.

1. `opam switch create --no-install .`
2. `opam repo add coq-released https://coq.inria.fr/opam/released`
3. `opam pin add -n coq-freesim ./dep/FreeSim`
4. `eval $(opam env)`
5. `make builddep`: respond with yes (Y) to the following prompts.
   - "Package coq-verilog-builddep does not exist, create as a NEW package? [Y/n]"
   - "Do you want to continue? [Y/n]"
6. `make -j$(nproc)`

Run on an Apple M2 Pro with 16GB RAM, the full proof check takes about 4 minutes; we do not expect it to take more than 10 minutes.


Proof Artifact Structure
------------------------

We provide the main correspondences between our paper and the artifact source code.

### Section 3. Formal Semantics of Verilog as a Transition Function

- 3.2 Syntax: `src/Lang/Syntax.v`
  + Fig. 2. Formal syntax of Verilog (excerpts)
    * Expressions: `VExpr` in `Syntax.v`:L128
    * L-values: `VLValue` in `Syntax.v`:L189
    * Event expressions: `VEventExpr` in `Syntax.v`:L230
    * Statements: `VStatement` in `Syntax.v`:L541
    * Blocks: `VModuleOrGenerateItem` in `Syntax.v`:L784
    * Generate blocks: `VModuleItems` in `Syntax.v`:L842
    * Modules: `VModuleDecl` in `Syntax.v`:L862

- 3.3 Semantic Domain: `src/Lib/HMap.v`
  + Hierarchical maps: `hmap` in `HMap.v`:L64

- 3.4 Semantic Transfer Function: `src/Lang/Semantics.v`
  + Fig. 3. Semantics for expressions, L-values, and statements (excerpts)
    * Expressions: `evalExpr` in `Semantics.v`:L292
    * L-values: `lvposfind` in `Semantics.v`:L348
    * Statements: `trsVStatementItem` in `Semantics.v`:L468
  + Fig. 4. Semantics for blocks and generate-blocks (excerpts)
    * Blocks: `trsVModuleOrGenerateItem` in `Semantics.v`:L655
    * Generate blocks: `trsVModuleItems` in `Semantics.v`:L712
  + Fig. 5. Semantics for modules
    * Modules: `trsVModuleDecl` in `Semantics.v`:L735

- 3.5 State-Transition Function: `src/Lang/Semantics.v`
  + Least fixed point of a semantic transfer function: `trsM_iff_rep` in `Semantics.v`:L745
    * As stated in the paper: "to define and use the function, the user must provide a proof that the fixpoint computation terminates."
  + State-update function: `trsM_IFF` in `Semantics.v`:L769
  + State-transition function: `trsT` in `Semantics.v`:L782

### Section 4. Equivalence Between the Standard and Our Semantics

- 4.2 Equivalence Proof: `src/Lang/Equiv/*.v`
  + Lemma 4.1 (Confluence): `eval_ugraph_confl_state_eq` in `UpdGraph.v`:L1531
    * Note that while the paper presents the equivalence between the standard semantics and ours directly, and thus the confluence lemma is stated with respect to the standard semantics, in the actual proof we use so-called update graphs (`ugraph` in our code) as an intermediate bridge between the two. Accordingly, the confluence lemma is stated for the update graphs.
  + Lemma 4.2: `Theorem stf_implies_std` in `StfStd.v`:L502
  + Lemma 4.3: `Theorem std_implies_stf` in `StfStd.v`:L522
  + Theorem 4.4 (Equivalence): `Theorem stf_std_equiv` in `StfStd.v`:L540
  + Note that `stateOf` and `trsF` are defined as functions in the paper, whereas in the artifact they are defined as `StateOf` and `TrsF`, respectively, as relations. This is simply because our state-transition function is defined as a fixpoint, and in the actual code, the fixpoint is represented as an inductive relational predicate.

### Section 5. Modular Verification of a Pipelined RISC-V Processor

- 5.2 Verilog Module Behavior in ITree: `src/Lang/ModuleITree.v`
  + Theorem 5.1 (Determinism): `src/Lang/ModuleITree.v`:L142
- 5.3 Formal Specification of RISC-V: `src/Ex/RvCore/FormalSpec.v`
- 5.4 Pipelined Processor Implementation: `src/Ex/RvCore/Core.v`
- 5.5 Behavioral Refinement Between `P_{impl}` and `S_{riscv}`
  + Theorem 5.2 (Adequacy)
    * This theorem is stated and proven in the external `FreeSim` library.
    * We use the theorem in our end-to-end proof in `src/Ex/RvCore/EndToEnd.v`:L80.
  + End-to-end theorem: `Theorem core_follow_riscv_formal` in `src/Ex/RvCore/EndToEnd.v`:L47


Reusability Guide
-----------------

- The main reusable part of the artifact is the formal syntax and semantics of Verilog.
- Users may want to design Verilog modules and define their state-transition functions by following the examples in `src/Ex/RvCore/Mem.v`. For example:
  + `ICache.M.m` contains a Verilog module definition, supported by rich notation provided by the framework.
  + `ICache.mtrs` defines the state-transition function for the module.

