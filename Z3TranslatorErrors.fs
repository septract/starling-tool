/// Errors for the Z3 translator.
module Starling.Errors.Z3.Translator

open Starling.Core.Model

/// A Z3 translation error.
type Error =
    /// The translator was given an indefinite constraint.
    /// The Z3 backend cannot handle indefinite constraints.
    | IndefiniteConstraint of viewdef: DFunc
    /// Instantiation of a view failed.
    | InstantiationError of view: VFunc * details: Starling.Instantiate.Error
