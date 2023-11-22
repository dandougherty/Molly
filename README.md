# Molly: A Verified Compiler for Cryptoprotocol Roles

Molly is a program that compiles cryptographic protocol roles written
in a high-level notation into straight-line programs in an
intermediate-level imperative language, suitable for implementation in
a conventional programming language.
    
We define a denotational semantics for protocol roles based on an
axiomatization of the runtime, and generate a machine-checked proof
that the procedure it constructs is correct with respect to the
runtime semantics.  A notable feature of our approach is that we
assume that encryption is randomized.  Thus, at the runtime level we
treat encryption as a relation rather than a function.
    
The paper "Molly: A Verified Role Compiler" on the ArXiv at @@ gives a
comprehensive description of the code and a prose account of the
proofs.

This code  builds under Coq 8.17.1 with the command

make 

CoqDoc documentation can be built by 

make html


# Requires:
the Coq Equations plugin
http://github.com/mattam82/Coq-Equations

see also https://sozeau.gitlabpages.inria.fr/www/research/coq/equations.en.html

# Thanks

Some code in Decidability.v is adapted from the stdpp library
and from Gert Smolka's Base library

Some code in Utilities.v and ListUtil.v is from Smolka's Base library
 
CpdtTactics.v is mostly due to Adam Chlipala

TacticsMatch.v is code due to Tej Chajed

# Roadmap 

## Utilities

CpdtTactics.v

TacticsMatch.v

Decidability.v

Utilities.v

ListUtil.v


## Data Structure Definitions

Act.v

 - a polymorphic type for sends, receives, inputs and outputs


Runtime.v

 - has a typeclass for what we assume about runtime operations


Sorts.v
Term.v
Subterms.v

 - the message algrabra of symbolic terms

Role.v
TranscriptsRole.v

 - roles are inputs to the compiler.
   role transcripts define an operational semantics for roles

Proc.v
TranscriptsProc.v

 - procs are outputs of the compiler
   proc transcripts define an operational semantics for procs

## Compiling

SaturationClass.v

- a typeclass to axiomatize what we require about our Procs

SaturationRules.v

 - inference rules for saturation
 
SaturationLoop.v

  - saturation algorithm

Compile.v

 - main compiling routine, using saturation to handle receptions (and inputs)

## Verification 

Reasoning.v

 - proofs about the compilation process

Reflecting.v

 - main theorem: when role rl is compiled to Proc pr, 
   any transcript for pr is a transcript for rl


## Testing

roleToRole.v 

- translate Roletran's roles into our Roles

Examples.v

 - some sample roles.  Not built by default.

## Code extraction

Extraction.v

 - automatically extract Ocaml code from the Gallina compiling code
   Not built by default.


