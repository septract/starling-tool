/// Errors for the Z3 translator.
module Starling.Errors.Z3.Translator

open Starling.Model

/// A Z3 translation error.
type Error =
    /// The translator was given an indefinite constraint.
    /// The Z3 backend cannot handle indefinite constraints.
    | IndefiniteConstraint of viewdef: DFunc
