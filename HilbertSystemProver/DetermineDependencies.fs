module DetermineDependencies
open ClassDefinition
open PostOrderPreprocessing
open System
//This function returns the right subtress with an imp root node
    let DetermineDependencies (axiomSubInstance: Expression) (theoremToProve: Expression) (op: BinOp) = 
        let rec loop (list: List<Expression>) (curExpression: Expression) (expressionToProve: Expression) =
            match (curExpression = theoremToProve) with
                | true -> list
                | false ->
                match curExpression with
                    | BinaryNode(op1, exp1, exp2) when op1 = op -> 
                        let newList = (List.append list [exp1])
                        (loop newList exp2 expressionToProve)
                    | BinaryNode(op1, exp1, exp2) ->
                        list
                    | UnaryNode(op, exp1) -> 
                        list
                    | AtomicNode(at) ->
                        list
                    | Null ->
                        list
        (loop [] axiomSubInstance theoremToProve)
   // This function takes a list of matchings and returns the List<Expression, List<Expression>>, giving for each matching its list of dependencies. 
   let DetermineDependenciesList (listOfMatchings: List<Expression>)(expressionToProve: Expression)(binop: BinOp): List<Tuple<Expression, List<Expression>>>= 
        let rec loop (curList: List<Expression>): List<Tuple<Expression, List<Expression>>> = 
            match curList with  
                | [] -> []
                | head::tail -> 
                    let curDependencies = (head, (DetermineDependencies head expressionToProve binop))
                    let recursiveCall = (loop tail)
                    (List.append [curDependencies] recursiveCall)
        (loop listOfMatchings)
   //This function takes a list of dependencies, and a list of AtomicVariables-Expression pair, and return the expressions resulting from replacing the schematic 
   //variables with their corresponding expressions. 
    let DependencyReplacement (listOfDependencies: List<Expression>) (matchings: List<Tuple<Expression, Expression>>) = 
        let rec loop curListOfExpressions listOfReplacedExpressions = 
            match curListOfExpressions with 
                | [] -> listOfReplacedExpressions 
                | head::tail -> 
                    let newExpression = (VariableReplacement head matchings)
                    (loop tail (List.append listOfReplacedExpressions [newExpression]))
        (loop listOfDependencies [])

            
        
