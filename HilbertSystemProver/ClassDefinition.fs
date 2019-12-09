module ClassDefinition  
   type BinOp (name, symbol) = 
        member this.name = name
        member this.symbol = symbol
    type UnOp (name, symbol) =
        member this.name = name
        member this.symbol = symbol
    [<AllowNullLiteral>]
    type AtomicVariable(symbol, ?isSchematic) = 
        member this.symbol = symbol
        member this.isSchematic = defaultArg isSchematic false
    type Operation = 
        | Bi of BinOp
        | Un of UnOp
    //Expression member may either be an operation or a Schematic Variable.
    type ExpressionMember = 
        |BinOp
        |UnOp
        |AtomicVariable
    //Expression is represented as a tree.
    type Expression = 
        | AtomicNode of AtomicVariable 
        | BinaryNode of BinOp * Expression * Expression
        | UnaryNode of UnOp * Expression
        | Null
    
    
        
        
