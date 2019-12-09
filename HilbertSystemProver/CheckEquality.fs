module CheckEquality
open ClassDefinition
open System
open System.Linq

//let Prover (listOfAxioms: List<Expression>) (expressionToProve: Expression) = 
  //  let rec 
    // let rec loop (currentUnfiledAxiom: Expression) (currentFiledAxiom: Expression) =

//This function checks whether a 
let CheckEqualityOfForm (expMain: Expression) (ax: Expression) = 
   let rec checkEqualityWithAxiom (exp: Expression) (axiom: Expression) (listOfExpAtoms: List<Expression>)(listOfAxAtoms: List<AtomicVariable>) = 
        match axiom with
            | AtomicNode(atom) -> 
                ( (List.append listOfExpAtoms [exp]), (List.append listOfAxAtoms [atom]))
                
            | BinaryNode(op2, ex1, ex2) ->
                match exp with 
                    | AtomicNode(atom) ->
                        ((List.append listOfExpAtoms [Null]), (List.append listOfAxAtoms [null]))
                    | BinaryNode(op_2, ex_1, ex_2) ->
                        match op2=op_2 with
                            | true ->
                                let retExpAtoms1, retAxAtoms1 = (checkEqualityWithAxiom ex_1 ex1 [] [])
                                let retExpAtoms2, retAxAtoms2 = (checkEqualityWithAxiom ex_2 ex2 [] [])
                                let newExpAtomsList = (List.append (List.append listOfExpAtoms  retExpAtoms1) retExpAtoms2 )
                                let newAxAtomsList = (List.append (List.append listOfAxAtoms retAxAtoms1) retAxAtoms2)
                                ( newExpAtomsList, newAxAtomsList)
                            | false ->
                                ((List.append listOfExpAtoms [Null]), (List.append listOfAxAtoms [null]))
                                
                    | UnaryNode(op_1, exp_1) -> 
                        ((List.append listOfExpAtoms [Null]), (List.append listOfAxAtoms [null]))
            | UnaryNode(op1, ex1) ->
                match axiom with 
                    | AtomicNode(atom) ->
                        ((List.append listOfExpAtoms [Null]), (List.append listOfAxAtoms [null]))
                    | BinaryNode(op_2, ex_1, ex_2) ->
                        ((List.append listOfExpAtoms [Null]), (List.append listOfAxAtoms [null]))
                    | UnaryNode(op_1, ex_1) -> 
                        match op1=op_1 with
                            | true -> 
                                let retExpAtoms, retAxAtoms = (checkEqualityWithAxiom ex1 ex_1 [] [])
                                ((List.append listOfExpAtoms retExpAtoms), (List.append listOfAxAtoms retAxAtoms ))
                            | false -> 
                                ((List.append listOfExpAtoms [Null]), (List.append listOfAxAtoms [null]))
   let listExp, listAx = (checkEqualityWithAxiom expMain ax [] [])
   //After getting list, check whether there exists a Null expression.
   //Recursive function checks this.
   let rec checkForNulls curList = 
        match curList with
            |[] -> false
            |head::tail -> 
                match head with 
                    | Null -> true
                    | _ -> checkForNulls tail
   
   //This recursive function goes through list of axiom atoms, returning a list of tuples, each with a distinct atom and a list of index locations. 
   let rec checkLists  (axList: List<AtomicVariable>) =
        //First, make a list of tuple<expression, List<int>>, where each expression is an atom in listAx, and List<int> contains all 
        //indices it is located at. \
        
        let rec createListOfAxAtomLocations (curConstructedList: List<Tuple<AtomicVariable, List<int>>>) (currentAxList: List<AtomicVariable>) (index: int)= 
            match currentAxList with
                | head :: tail ->
                    let rec findOrAdd (prevList: List<Tuple<AtomicVariable, List<int>>>) (curList: List<Tuple<AtomicVariable, List<int>>>) (atomToAdd: AtomicVariable) (indexToAdd:int) =
                        match curList with
                            | head1 :: tail1 ->
                                //Check equality.
                                let exp, list = head1
                                match exp=atomToAdd with 
                                    | true -> 
                                        //Add new index to list, append to exsiting list, place into same list.
                                        let rec buildIndexList (beforeList: List<int>) (afterList:List<int>) = 
                                            match afterList with
                                                | [] -> (List.append beforeList [indexToAdd])
                                                | head2::tail2 -> (buildIndexList (List.append beforeList [head2]) tail2)
                                        let newBeforeList = (List.append prevList [(exp, (buildIndexList [] list))])
                                        let newTotalList = List.append newBeforeList tail1
                                        newTotalList
                                    | _ -> (findOrAdd (List.append prevList [head1]) tail1 atomToAdd indexToAdd)
                            | [] -> (List.append curConstructedList [(atomToAdd, [indexToAdd])])
                    let newConstructedList = (findOrAdd [] curConstructedList currentAxList.Head index)
                    (createListOfAxAtomLocations newConstructedList tail (index + 1))
                
                | [] -> (curConstructedList)
        (createListOfAxAtomLocations [] axList 0)
   //(checkLists listExp listAx)

   //This function goes through each atom, index list pairs, ensuring that the corresponding exps are all equal in expList.
   let rec CheckEqualityOfAtomicExpressions (atomExpressionMatchings: List<Tuple<AtomicVariable, List<int>>>) (expressionArray: Expression array) = 
        match atomExpressionMatchings with 
            | [] -> true
            | head::tail ->
                let rec checkAllEqual (intList: List<int>) (firstExpression: Expression) = 
                    match firstExpression with
                        | Null -> 
                             (checkAllEqual intList expressionArray.[intList.Head ])
                        | _ ->
                            match intList with
                                | [] -> true
                                | head::tail -> 
                                    match firstExpression=expressionArray.[head] with
                                        | true -> (checkAllEqual tail firstExpression)
                                        | false -> false
                let _, list = head
                match (checkAllEqual list Null) with 
                    | false -> false
                    | true  -> (CheckEqualityOfAtomicExpressions tail expressionArray)
   match (not (checkForNulls listExp)) && (listExp.Length = listAx.Length) with
        | false -> false
        | true ->
            let axiomAtomLocations = (checkLists listAx)
            (CheckEqualityOfAtomicExpressions axiomAtomLocations (List.toArray listExp))
//The following function loops through a list of axioms, and returns the first axiom whose form it has. Otherwise, return Null expression.
let CheckEqualityOfFormList (expression: Expression)(axioms: List<Expression>) =
    let rec loop curList = 
        match curList with 
            | [] -> Null
            | head::tail -> 
                match (CheckEqualityOfForm expression head) with 
                    | false -> (loop tail)
                    | true -> 
                        head
    (loop axioms)

        
                
            
            
        
        
        
  