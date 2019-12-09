module PostOrderPreprocessing
open ClassDefinition
open Microsoft.CSharp.RuntimeBinder
open System
//open Microsoft.FSharp.Collections.List
//This function returns a list of axiom-replacements.
let MatchExpressionWithAxiom (axiom: Expression) (expressionToCheck: Expression) = 
//This expression looks for the farthest right occurence of any operation. Return the subtree rooted at last occurence
    let findLastOccurence (expression: Expression) = 
        let rec loop exp prevExp = 
                match exp with
                    | AtomicNode(atom) -> prevExp
                    | UnaryNode(op, exp1) -> (loop exp1 exp)
                    | BinaryNode(op, exp1, exp2) ->   (loop exp2 exp) 
        (loop expression Null)
    //Finds a list of all right occurences of a given operation.
    let findAllRightOccurencesBin (expression: Expression) (opToMatch: BinOp) = 
        let rec loop expressionLoop list  = 
            match expressionLoop with
                | AtomicNode(at) -> list 
                | UnaryNode(op, exp1) -> (loop exp1 list ) 
                | BinaryNode(op, exp1, exp2) when op.symbol = opToMatch.symbol ->   
                    (loop exp2 (List.append list [expressionLoop]))
                | BinaryNode(op, exp1, exp2) -> 
                    (loop exp2 list)
        (loop expression [])
     //Finds a list of all right occurences of a unary operation.
    let findAllRightOccurencesUn (expression: Expression) (opToMatch: UnOp) = 
        let rec loop expressionLoop list = 
            match expressionLoop with
                | AtomicNode(at) -> list
                | BinaryNode(op, exp1, exp2) -> (loop exp2 list)
                | UnaryNode(op, exp1) when op.symbol = opToMatch.symbol -> 
                    (loop exp1 (List.append list [expressionLoop]))
                | UnaryNode(op, exp1) -> 
                    (loop exp1 list)
        (loop expression [])
    
    //This function returns a list of axiomatic atoms matched with an expression from the theorem to prove. If there exists a null entry, then a matching could not be made.
    let matchExpression (expToMatch: Expression) (expTheorem: Expression) : List<Tuple<Expression, Expression>> = 
        //let list :  List<Tuple<Expression, Expression>>  = new List<Tuple<Expression, Expression>>()
        let rec loop (expToMa: Expression) (expThe: Expression) curList = // : List<Tuple<Expression, Expression>>)= 
            match expToMa with 
                | AtomicNode(Atom) when Atom.isSchematic = true -> (List.append [(expToMa,expThe)] curList)
                | AtomicNode(Atom) -> (List.append [(Null, Null)] curList)
                | BinaryNode(Op, Exp1, Exp2) -> 
                    match expThe with
                        | AtomicNode(atom) -> (List.append [(Null, Null)] curList)
                        | BinaryNode(op, ext1, ext2) ->
                            match op with  
                                | Op -> 
                                    let firstRec =  (loop Exp1 ext1 [])
                                    let secRec = (loop Exp2 ext2 [])
                                    (List.append (List.append firstRec secRec) curList)
                                
                                | _ -> (List.append [( Null,Null )] curList)
                        | UnaryNode(op, exp1) -> (List.append [(Null, Null)] curList)
                        
                        
                | UnaryNode(Op, Exp1) -> 
                    match expThe with
                        | AtomicNode(atom) -> (List.append [(Null, Null)] curList)
                        | BinaryNode(op, exp1, extp) -> (List.append [(Null, Null)] curList)
                        | UnaryNode(op, exp1) -> 
                            match op with 
                                | Op -> 
                                    let firstRec = (loop Exp1 exp1 [])
                                    (List.append firstRec curList)
                                | _ -> (List.append [(Null, Null)] curList)
        (loop expToMatch expTheorem [])      
    
       
    //This function takes an axiomatic expression with a list of atom - expression pairs and return an expression with the atoms replaced by its pair. 
    let AxiomAtomReplacement (axiom: Expression) (List: List<Tuple<Expression, Expression>>): Expression = 
        //This function searces list for atom and returns its corresponding replacement expression. If atom is not found, then the existing expression is returned.
        let matched (exp: Expression): Expression = 
            let rec loop list = 
                match list with 
                    | [] -> exp
                    | (AtomicNode(atom), toReturn) :: tail -> 
                        match exp with 
                            | AtomicNode(atom2) when atom.symbol = atom2.symbol -> toReturn
                            | _ -> (loop tail)
            (loop List)

        //This recursive function creates the new axiom expression with replacements.  
        let rec loop (Exp: Expression) = 
            match Exp with 
                | BinaryNode(op, exp1, exp2) ->  BinaryNode(op ,(loop exp1), (loop exp2))
                | UnaryNode(op, exp1) -> UnaryNode(op, (loop exp1))
                | AtomicNode(atom) -> (matched Exp)
                
        (loop axiom)
    //This function is called in case the expression to prove and the axiom to match do not share any operations.
    //In this case, the expression to proves takes the place of the rightmost atom that is the right child of an implication.
    (*let AxiomAtomReplacementNoSharedOps (axiom: Expression)(theoremToProve: Expression) = 
        let rec loop (curExpression: Expression) (prevExpression: Expression) = 
            match curExpression with 
                | BinaryNode(op, exp1, exp2) -> *)
                    
                    
    //This function checks whether there exists a (Null, Null) entry in list. 
    let rec CheckForNulls (list: List<Tuple<Expression, Expression>>): bool = 
        match list with 
            | [] ->  false  
            | (Null, Null) :: tail -> 
                Console.WriteLine "Found some nulls!"
                true
            | _ :: tail -> (CheckForNulls tail )
            
    
    //Get all right occurences of the most significant operation.
    let allOccurences  = 
        match expressionToCheck with 
            | UnaryNode(op, exp1) -> (findAllRightOccurencesUn axiom op)
            | BinaryNode(op, exp1, exp2) -> (findAllRightOccurencesBin axiom op)
            
    
    //The following function attempts, for each matched subexpression in allOccurences, to perform MatchExpression. For each occurence, a matring is attemped. 
    //List of matchings are returned
    let rec matchings listOfOccurences listOfMatchings = 
        match listOfOccurences with
            | [] -> listOfMatchings
            | head::tail ->  
                let newList = (List.append listOfMatchings [(matchExpression head expressionToCheck)]) 
                (matchings tail newList) 
    let allMatchings = (matchings allOccurences [])
    //Now, attempt Axiom repracement with each matching. Store in a list.
    let rec attemptAxiomReplacement (listOfMatches: List<List<Tuple<Expression, Expression>>>) (returnList: List<Expression>) = 
         match listOfMatches with
            | [] -> returnList
            | head::tail ->
                match CheckForNulls(head) with 
                    | true -> (attemptAxiomReplacement tail returnList)
                    | false ->
                        let replacement = List.append returnList [(AxiomAtomReplacement axiom head)] 
                        (attemptAxiomReplacement tail replacement)
    (attemptAxiomReplacement allMatchings [])



//This function takes an expression, and a list of expression
let VariableReplacement (expression: Expression)(listOfRules: List<Tuple<Expression, Expression>>): Expression = 
    let rec findMatch key list = 
        match list with 
            | [] -> key
            | head:: tail -> 
                let curKey, expression = head
                match key=curKey with 
                    | true -> expression
                    | false -> 
                        (findMatch key tail)
    let rec loop curExpression = 
        match curExpression with 
            | AtomicNode(atom) -> 
                (findMatch curExpression listOfRules)
            | BinaryNode(op, exp1, exp2) -> 
                let leftSubtree = (loop exp1)
                let rightSubtree = (loop exp2)
                BinaryNode(op, leftSubtree, rightSubtree)
            | UnaryNode(op, exp1) ->
                let subTree = (loop exp1)
                UnaryNode(op, subTree)
    (loop expression)
//This function takes a list of axioms and a singular expression, and returns a List<Tuple<Expression, List<Expression>>>, where the first expression represents an
// axiom and the corresponding list contains matchings.
let MatchExpressionWithAxiomList (expression: Expression) (axioms: List<Expression>): List<Tuple<Expression, List<Expression>>> = 
    let rec loop curList = 
        match curList with 
            | [] -> [Null, [Null]]
            | head::tail ->
                let matchings = (MatchExpressionWithAxiom head expression)
                let returnList = (loop tail)
                (List.append returnList [(head, matchings)])
    (loop axioms)

                
            
            