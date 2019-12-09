module SoundnessChecks
open System
open ClassDefinition
//This function checks whether a given expression is true.
//This function should only be used with those logics that use the same algebraic alphabet as classical propositional logic, and that is complete
// with respect to the class of all boolean algebras.
let CheckIfTautology (expression: Expression) (Imp: BinOp)(Con: BinOp)(Dis: BinOp)(Neg: UnOp) = 
    let rec checkIfAlreadyInList (currentDoubleCheckList: List<AtomicVariable>) (atomicVariable: AtomicVariable) = 
            match currentDoubleCheckList with 
                | [] -> false
                | head::tail -> 
                    match atomicVariable.symbol=head.symbol with
                        | true -> true
                        | false -> 
                            (checkIfAlreadyInList tail atomicVariable)
    let rec GetListOfDistinctVariables curExpression (curList: List<AtomicVariable>): List<AtomicVariable> = 
        
        match curExpression with 
            | AtomicNode(atom) -> 
                match (checkIfAlreadyInList curList atom) with 
                    | true ->  curList
                    | false -> (List.append curList [atom])
            | BinaryNode(op, exp1, exp2) -> 
                let leftSub = (GetListOfDistinctVariables exp1 curList)
                let rightSub = (GetListOfDistinctVariables exp2  leftSub) 
                rightSub
            | UnaryNode(op, exp1) -> 
                let sub = (GetListOfDistinctVariables exp1 [])
                (List.append curList sub)
    let ListOfDistinctVariables = (GetListOfDistinctVariables expression [])

    let rec BuildListOfTruthValueCombination (curSubList: List<bool>)(curInt: int) = 
        match (ListOfDistinctVariables.Length=curInt) with 
            | true -> 
                let listOne = (List.append curSubList [true])
                let listTwo = (List.append curSubList [false])
                (List.append [listOne] [listTwo])
            | false -> 
                let trueLists = (BuildListOfTruthValueCombination (List.append curSubList [true]) (curInt + 1))
                let falseLists = (BuildListOfTruthValueCombination (List.append curSubList [false]) (curInt + 1))
                (List.append trueLists falseLists)
    let ListOfPossibleTruthCombos = (BuildListOfTruthValueCombination [] 1)
    
    let rec GetValue (atomVar: AtomicVariable) (currentList: List<AtomicVariable>) (currentBoolList: List<bool>) = 
                    match currentList.Head=atomVar with 
                        | true -> currentBoolList.Head
                        | false -> 
                            (GetValue atomVar currentList.Tail currentBoolList.Tail)
    let rec EvaluateExpression (exp: Expression)(bools: List<bool>) = 
        match exp with 
            |AtomicNode(atom) -> 
                (GetValue atom ListOfDistinctVariables bools)
            |BinaryNode(op, exp1, exp2) -> 
                match op=Imp with 
                    |  true -> 
                        let left = (EvaluateExpression exp1 bools)
                        let right = (EvaluateExpression exp2 bools)
                        let return1 = (right || (not left))
                        return1
                    | false -> 
                        match op=Con with
                            | true -> 
                                let left = (EvaluateExpression exp1 bools)
                                let right = (EvaluateExpression exp2 bools)
                                let return1 = (left && right)
                                return1
                            | false -> 
                                match op=Dis with
                                    | true -> 
                                         let left = (EvaluateExpression exp1 bools)
                                         let right = (EvaluateExpression exp2 bools)
                                         let return1 = (left || right)
                                         return1
                                
                    
                        
             | UnaryNode(op, exp1) -> 
                let right = (EvaluateExpression exp1 bools)
                let return1 = (not right)
                return1
    let rec CheckEachCombo (curList: List<List<bool>>) = 
        match curList with  
            |[] -> true
            | head::tail -> 
                match (EvaluateExpression expression head) with 
                    | false -> 
                        false
                    | true -> 
                        (CheckEachCombo tail)
    (CheckEachCombo ListOfPossibleTruthCombos)
                
                            
                    
