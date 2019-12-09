module Prover
open ClassDefinition
open System
open PostOrderPreprocessing
open SoundnessChecks
open CheckEquality

let Prove  (ExpressionToProve: Expression) (Axioms: List<Expression>) (implication: BinOp) = 
   //This loop gets all axiom matchings.
   // Arguments: curListOfMatchings~ A list of tuples, first place is Axiom, second place list of matchings.
    let rec AxiomLoop (curListOfMatchings: List<Tuple<Expression, List<Expression>>>)(curAxiomList: List<Expression>): curListOfMatchings: List<Tuple<Expression, List<Expression>>> =
            match curAxiomList with 
                | [] -> curListOfMatchings
                | head::tail -> 
                    let matching = (MatchExpressionWithAxiom head ExpressionToProve)
                    (List.append curListOfMatchings [(head, matching)])
    //Main Loop.
    //Order of Operations.
    // (0) Check whether expression is a tautology. If not, stop. Theorem cannot be proved. 
    // (1) Determine Matchings.
    // (2) For each matching, determine dependencies.
    // (3) For each dependency, determine whether any have axiomatic form. 
    //     If all dependencies have axiomatic form, stop. Theorem is proven.
    // (4) For each dependency that does not have axiomatic form, attempt to fill each expression into each axiom. 
    //     During this phase, perform uniform replacement to all dependencies, i.e. if in filling the dependency a -> x with x and a -> x, where a is schematic and x is fixed,
    //     All occurences of schematic variable a in all dependencies must be replaced by (x and a)
    // 
    let rec MainLoop (expressionToProve: Expression) : List<Expression,Expression>  = 
        //First, check whether the expression is a tautology.
        //If expression is not a tautology, then the expression cannot be proved.
        match (CheckIfTautology expressionToProve) with 
            | false -> [Null]
            | true -> 
        // Now, check whether expression has axiomatic form.
                let axiomMatchingExpression = (CheckEqualityOfFormList expressionToProve Axioms)
                match (axiomMatchingExpression) with 
                    | Null -> 
                        //If this expression does not match any axiom, get list of matchings.
                        let listOfMatching = (MatchExpressionWithAxiomList expressionToProve Axioms)
                        //For each matching, get list of dependencies.
                        let listOfDependencies = (DetermineDependencies listOfMatching expressionToProve implication )
                        //If there exists at least one dependency without axiomatic form, attempt to fill each non-axiomatic expresssion, performing the requisite replacements
                        //on the other dependencies.
                    | _ ->
                        //If expression matches an axiom, return tuple containing expression and matching axiom.
                        (expressionToProve, axiomMatchingExpression)
                        
                        


  