# DyLean Libraries

This repository is a collection of DyLean extensions and libraries that extend the functionality of [DyLean](https://github.com/BobDyLean/dylean) with useful features that are often used in protocol analysis.
The repository also provides examples that show how to use the libraries.

## Overview

- **DyExtensions:**
    - Asymmetric encryption
    - Symmetric encryption
    - Updatable state
    - Immutable local-state storage predicates and invariant recovery (`DyExtensions.Actions.PersistentLocalState`)
    - Helper functions and theorems for events and random value generation
- **DyLibraries:**
    - Secure communication library (confidential messages, authenticated messages, confidential and authenticated messages, and TLS-like request-response communication)
    - Database library
    - Printing library to verify protocol models
    - SplitCrypto library to combine cryptographic predicates based on key usage
- **Examples:** Login example to demonstrate how to use the request-response functionality of the communication library
