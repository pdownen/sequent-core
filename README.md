Sequent Core
============

Sequent Core is a GHC plugin library based on a sequent calculus. It includes:

*   A set of datatypes for a language expressing function code as *interactions*
    between values and their contexts (*continuations*)
*   A library for writing GHC optimizer plugins that uses the Sequent Core
    language in place of the built-in Core language
*   An example plugin written using Sequent Core

At the moment, this library is highly experimental. We would appreciate any
feedback at <maurerl@cs.uoregon.edu>.

Luke Maurer  
Paul Downen  
Iavor S. Diatchki
