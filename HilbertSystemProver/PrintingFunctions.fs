module PrintingFunctions
open ClassDefinition
open System
let PrintBinaryTree (expressionToPrint: Expression) = 
    //creates list of lists of expression ops/atoms
    //curList is the list of current level nodes, totalList is the list of level lists.
    let buildListOfAllNodes = 
        let rec loop (curList: List<Expression>) (createdList: List<Expression>) = 
            match curList.Length with
                | 0 -> createdList
                | _ -> 
                    match curList.Head with
                        | BinaryNode(op, exp1, exp2) ->
                            let exp1List = (List.append createdList  [exp1])
                            let totalList = List.append exp1List [exp2]
                            let newCurList1 = (List.append curList.Tail [exp1])
                            let newCurList = (List.append newCurList1 [exp2])
                            (loop newCurList totalList)
                
                        | UnaryNode(op, exp1) ->
                            let newTotalList = (List.append createdList [exp1])
                            let newCurList = (List.append curList.Tail [exp1])
                            (loop newCurList newTotalList)
                        | AtomicNode(var) -> 
                            (loop curList.Tail createdList)
                        | _ ->
                        createdList
        (loop [expressionToPrint] [expressionToPrint])
    //Builds list of strings.
    let buildListOfLists = 
        let rec innerLoop (listToBuildFrom: List<Expression>) (builtList: List<Expression>) curInt nextInt=
            match curInt with
                | 0 -> (listToBuildFrom, builtList, nextInt)
                | _ -> 
                    match listToBuildFrom.Head with
                        | BinaryNode(op, exp, exp2)  ->
                            
                            (innerLoop listToBuildFrom.Tail (List.append builtList [listToBuildFrom.Head]) (curInt - 1) (nextInt + 2))
                        | UnaryNode(op, exp1) ->
                            
                            (innerLoop listToBuildFrom.Tail (List.append builtList [listToBuildFrom.Head]) (curInt - 1) (nextInt + 1))
                        | AtomicNode(atom) ->
                            
                            (innerLoop listToBuildFrom.Tail (List.append builtList [listToBuildFrom.Head]) (curInt - 1) nextInt)
        //Builds outer list of lists.
        let rec outerLoop (listToBuildFrom: List<Expression>) (builtList: List<List<Expression>>) curInt= 
            match listToBuildFrom.Length with   
                | 0 -> builtList
                | _ ->
                    let remainingList, listToAdd, nextInt = (innerLoop listToBuildFrom [] curInt 0)
                    
                    (outerLoop remainingList (List.append builtList [listToAdd]) nextInt)
        (outerLoop buildListOfAllNodes [[]] 1)
    let stringBuilder (lists: List<List<Expression>>) = 
        //This function builds lines in between the node levels.
        let rec buildBranchLine string branchTypes = 
            match branchTypes with
                | [] -> [string]
                | BinaryNode(op, e, u) :: tail -> (buildBranchLine (string + "/  \\" + "     " ) tail)
                | UnaryNode(op, p) :: tail -> (buildBranchLine (string + "|" + "     ") tail)
                | AtomicNode(at) :: tail -> (buildBranchLine (string + " " + "     ") tail)
        //This function builds each node level.
        let rec buildLine string branchTypes = 
            match branchTypes with 
                | [] -> [string]
                | BinaryNode(op, exp1, ebp2) :: tail -> (buildLine (string + op.symbol.ToString() + "     ") tail)
                | UnaryNode(op, exp1) :: tail -> (buildLine (string + op.symbol.ToString() + "     ") tail)
                | AtomicNode(at) :: tail -> (buildLine (string + at.symbol.ToString() + "     ") tail)
        let rec build (listOfLists: List<List<Expression>>) curStringList = 
            match listOfLists with
                | []  -> curStringList
                | _ -> 
                    let firstLineAppend = (List.append curStringList (buildLine "" listOfLists.Head))
                    let secondLineAppend = (List.append firstLineAppend (buildBranchLine "" listOfLists.Head))
                    (build listOfLists.Tail secondLineAppend)
                    
        (build lists [])
    let myList = (stringBuilder buildListOfLists)
    
    //This function prints to console the binary tree.
    let rec printToConsole (list: List<string>) = 
        match list with 
            | [] -> 0
            | _ ->
                list.Head |> Console.WriteLine
                (printToConsole list.Tail)
    
    
    (printToConsole myList)
        
        
let InOrderTraversal(expression: Expression) = 
        let rec loop (string:string) exp = 
            match exp with
                | AtomicNode(atom) -> string + atom.symbol.ToString() + " "
                | UnaryNode(op, exp1) -> string   + op.symbol.ToString() + " ( " + (loop "" exp1) + " ) "
                | BinaryNode(op, exp1, exp2) -> string + "( " + (loop "" exp1) + " " + op.symbol.ToString() + " " + (loop "" exp2) + " ) "
        (loop "" expression)
let rec printList list = 
        match list with
            | [] -> 0
            | head::tail -> 
                (InOrderTraversal head).ToString() |> Console.WriteLine
                (printList tail)