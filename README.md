# DafnyPrograms
This repository contains some dafny programs that I have worked in verifying. 
* automaton.dfy containing an automaton containing every step of applying a certain rule over an input sequence
* map-multiset-implementation.dfy containing an implementation of a multiset ADT using a map.
* prime-database.dfy containing a PrimeMap class that remembers whether a number is prime or not.
* If pressed by time, I recommend checking out automaton.dfy and perhaps map-multiset-implementation.dfy.

When a program is verified by Dafny, it means that Dafny has checked the program against a set of specifications and has found that the program meets those specifications precisely, using mathematical logic and automated theorem proving techniques. The verification process provides confidence that the program is correct and safe to use in different circumstances, that is why the language is most often used in developing critical components.

# Requirements
* Visual Studio Code
* Dafny extension

# Usage
1. Open the programs in Visual Studio Code.
2. The programs verify: a vertical green check appears on the left side of the code.
