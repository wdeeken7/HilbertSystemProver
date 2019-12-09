module FillExpression
open ClassDefinition
open System
//Function checks whether an expression contains any schematic variables. 
let containsSchematics (expression: Expression) = 
    let rec loop exp = 
        match exp with 
            | AtomicNode(atom) -> 
                match atom.isSchematic with 
                    | true -> true
                    | false -> false
            | BinaryNode(op, exp1, exp2) -> 
                let leftSub = (loop exp1)
                let rightSub = (loop exp2)
                (leftSub || rightSub)
            
            | UnaryNode(op, exp1) ->
                (loop exp1)
            | Null -> false
                
    (loop expression)
//Function attempts to fill a mixed schematic/fixed expression for all fixed, matching with a schematic form. 
//This function mimics the beginning of the checkEqualityOfForm function above.
//If a fill operation fails, then return an expression with a singular Null node.
//Returns new expression, along with a list of tuples, first the schematic variable and second the expression that it replaced. 
let FillExpression (axiom: Expression)(mixedExpression: Expression): Tuple<Expression, List<Tuple<Expression, Expression>>> = 
    //This function gives a matching of schematic variables in expression to a subexpression of axiom, or a matching of schematic variables in the
    // axiom to fixed variables in the expression, or the schematic variables to subexpressions of cur expression.
    //(AxiomMember, ExpressionMember)
        let rec loopCreateVarMatchings curAxiom curExpression listOfTuples = 
            match curAxiom with
                | AtomicNode(atom) ->
                    match curExpression with
                        | AtomicNode(atom1) -> (List.append listOfTuples [(curAxiom, curExpression)])
                        | BinaryNode(op, exp1, exp2) -> (List.append listOfTuples [(curAxiom, curExpression)])
                        | UnaryNode(op, exp1) -> (List.append listOfTuples [(curAxiom, curExpression)])
                | BinaryNode(op, exp1, exp2) ->
                    match curExpression with
                        | AtomicNode(atom1) -> (List.append listOfTuples [(curAxiom, curExpression)]) 
                        | BinaryNode(op11, exp11, exp22) -> 
                            match (op11.symbol = op.symbol) with
                                | true ->
                                    let leftSubtreeList = (List.append listOfTuples (loopCreateVarMatchings exp1 exp11 []) )
                                    (List.append leftSubtreeList (loopCreateVarMatchings exp2 exp22 []))
                                | false -> (List.append listOfTuples [(Null, Null)])
                        | UnaryNode(op, exp1) -> 
                            (List.append listOfTuples [(Null, Null)])
                | UnaryNode(op, exp1) ->
                    match curExpression with 
                        | AtomicNode(atom1) -> (List.append listOfTuples [(curAxiom, curExpression)])
                        | BinaryNode(op, exp1, exp2) ->
                            (List.append listOfTuples [(Null, Null)])
                        | UnaryNode(op, exp11) ->
                            (List.append listOfTuples (loopCreateVarMatchings exp1 exp11 []))
        // This function fills the expression.
        let fillExpression (listOfTuples: List<Tuple<Expression, Expression>>)(axiomToFill: Expression) = 
            //Helper function checks list for occurences of variable.
            let rec checkList list (schematicVarToFind: AtomicVariable)  = 
                match list with 
                    | [] -> Null
                    | head :: tail -> 
                        let axEx, exEx = head
                        match axEx with
                            | AtomicNode(atom) ->
                                match atom.symbol=schematicVarToFind.symbol with
                                    | true -> exEx 
                                    | false -> (checkList tail schematicVarToFind)
                            | _ -> (checkList tail schematicVarToFind)
            let rec build curAxiom curListOfReplacements= 
                match curAxiom with
                    | AtomicNode(atom) -> 
                        let replacementExpression = (checkList listOfTuples atom)
                        match replacementExpression with
                            | Null -> (AtomicNode(atom), curListOfReplacements)
                            | _ -> (replacementExpression, [(curAxiom, replacementExpression)])
                    | BinaryNode(op, exp1, exp2) ->
                        let leftChild, list = (build exp1 [])
                        let rightChild, list1 = (build exp2 [])
                        let returnList = (List.append list list1)
                        (BinaryNode(op, leftChild, rightChild), (List.append curListOfReplacements returnList))
                    | UnaryNode(op, exp1) ->
                        let child, list = (build exp1 [])
                        (UnaryNode(op, child), (List.append curListOfReplacements list))
            (build axiomToFill [])          
            
        //This function checks whether there exists Null expression in list. The presence of a (Null, Null) value means that the
        //Expression cannot be filled according to this Axiom.
        let rec CheckForNulls (list: List<Tuple<Expression, Expression>>) = 
            match list with 
                |[] -> false
                |head :: tail -> 
                    match (head=(Null, Null)) with  
                        | true -> true
                        | false -> (CheckForNulls tail)
        //Main control block.
        let listOfMatchings = (loopCreateVarMatchings axiom mixedExpression [])
        //If nulls are in list, return null expression.
        //Else, continue to create filling.
        match (CheckForNulls listOfMatchings) with
            | true -> (Null, [])
            | false -> 
                (fillExpression listOfMatchings axiom)
