// Learn more about F# at http://fsharp.org

open System
open ClassDefinition
open System.Linq.Expressions
open PrintingFunctions
open PostOrderPreprocessing
open DetermineDependencies
open CheckEquality
open FillExpression
open SoundnessChecks
[<EntryPoint>]
let main argv =
    Console.OutputEncoding <- System.Text.Encoding.Unicode
    //TEST
    //Define some connectives. 
    let Neg = new UnOp("Negation", "\u00AC")
    let Imp = new BinOp("Implication", "\u21D2")
    let Con = new BinOp("Conjunction", "\u2227")
    let Dis = new BinOp("Disjunction", "\u2228")
    //Define some AtomicVariables.
    let AVar = new AtomicVariable("A", true)
    let BVar = new AtomicVariable("B", true)
    let CVar = new AtomicVariable("C", true)
    let XVar = new AtomicVariable("X")
    let YVar = new AtomicVariable("Y")
    let ZVar = new AtomicVariable("Z")
    //Attempt to put axioms into expression tree.
    let Axiom1 = BinaryNode(Imp, 
                    AtomicNode(AVar),
                        BinaryNode(Imp, 
                            AtomicNode(BVar), AtomicNode(AVar)))
    let Axiom2 = BinaryNode(Imp, 
                    BinaryNode(Imp, AtomicNode(AVar), 
                        BinaryNode(Imp, AtomicNode(BVar), AtomicNode(CVar))),
                    BinaryNode(Imp, 
                        BinaryNode(Imp, AtomicNode(AVar), AtomicNode(BVar)), 
                        BinaryNode(Imp, AtomicNode(AVar), AtomicNode(CVar))))
    let Axiom3 = BinaryNode(Imp, AtomicNode(AVar), 
                    BinaryNode(Dis, AtomicNode(AVar), AtomicNode(BVar)))
    let Axiom4 = BinaryNode(Imp, AtomicNode(BVar),
                     BinaryNode(Dis, AtomicNode(AVar), AtomicNode(BVar)))
    let Axiom5 = BinaryNode(Imp, 
                    BinaryNode(Imp, AtomicNode(AVar), AtomicNode(CVar)), 
                    BinaryNode(Imp, 
                        BinaryNode(Imp, AtomicNode(BVar), AtomicNode(CVar)), 
                        BinaryNode(Imp, 
                            BinaryNode(Dis, AtomicNode(AVar), AtomicNode(BVar)),
                            AtomicNode(CVar))))
    let Axiom6 = BinaryNode(Imp, 
                        BinaryNode(Con, AtomicNode(AVar), AtomicNode(BVar)),
                        AtomicNode(AVar))
    let Axiom7 = BinaryNode(Imp, 
                        BinaryNode(Con, AtomicNode(AVar), AtomicNode(BVar)), 
                        AtomicNode(BVar))
                
    let Axiom8 = BinaryNode(Imp, 
                    BinaryNode(Imp, AtomicNode(AVar), AtomicNode(BVar)),
                    BinaryNode(Imp, 
                        BinaryNode(Imp, AtomicNode(AVar), AtomicNode(CVar)),
                        BinaryNode(Imp, AtomicNode(AVar), 
                            BinaryNode(Con, AtomicNode(BVar), AtomicNode(CVar)))))
    let Axiom9 = BinaryNode(Imp, 
                    BinaryNode(Imp, AtomicNode(AVar), UnaryNode(Neg, AtomicNode(BVar))), 
                    BinaryNode(Imp, AtomicNode(BVar), UnaryNode(Neg, AtomicNode(AVar))))
    let Axiom10 = BinaryNode(Imp, 
                    UnaryNode(Neg, BinaryNode(Imp, AtomicNode(AVar), AtomicNode(AVar))),
                    AtomicNode(BVar))
    let Axiom11 = BinaryNode(Dis, AtomicNode(AVar), UnaryNode(Neg, AtomicNode(AVar)))
    let ListOfAxioms = [Axiom1; Axiom2; Axiom3; Axiom4; Axiom5; Axiom6; Axiom7; Axiom8; Axiom9; Axiom10; Axiom11]
    let rec testLoopSoundness list = 
        match list with 
            | [] -> (Console.WriteLine "Soundness Check Complete")
            | head :: tail -> 
                ("Checking axiom " + (InOrderTraversal head)) |> Console.WriteLine
                ("Result " + (CheckIfTautology head Imp Con Dis Neg).ToString()) |> Console.WriteLine
                (testLoopSoundness tail)
                
    ("Axiom 1: " + (InOrderTraversal Axiom1 ))|> Console.WriteLine
    ("Axiom 2: " + (InOrderTraversal Axiom2 ))|> Console.WriteLine
    ("Axiom 3: " + (InOrderTraversal Axiom3 ))|> Console.WriteLine
    ("Axiom 4: " + (InOrderTraversal Axiom4 ))|> Console.WriteLine
    ("Axiom 5: " + (InOrderTraversal Axiom5 ))|> Console.WriteLine
    ("Axiom 6: " + (InOrderTraversal Axiom6 ))|> Console.WriteLine
    ("Axiom 7: " + (InOrderTraversal Axiom7 ))|> Console.WriteLine
    ("Axiom 8: " + (InOrderTraversal Axiom8 ))|> Console.WriteLine
    ("Axiom 9: " + (InOrderTraversal Axiom9 ))|> Console.WriteLine
    ("Axiom 10: " + (InOrderTraversal Axiom10 ))|> Console.WriteLine
    ("Axiom 11: " + (InOrderTraversal Axiom11 ))|> Console.WriteLine
    (testLoopSoundness ListOfAxioms)
    "Testing non-theorem X -> (X  AND Y)" |> Console.WriteLine
    let testSoundnessBad = BinaryNode(Imp, AtomicNode(XVar), BinaryNode(Con, AtomicNode(XVar), AtomicNode(YVar)))
    ("Result " + (CheckIfTautology testSoundnessBad Imp Con Dis Neg).ToString()) |> Console.WriteLine

    //Print off binary tree of each axiom
    (*
    Axiom1 |> PrintBinaryTree |> ignore
    Axiom2 |> PrintBinaryTree |> ignore
    Axiom3 |> PrintBinaryTree |> ignore
    Axiom4 |> PrintBinaryTree |> ignore
    Axiom5 |> PrintBinaryTree |> ignore
    Axiom6 |> PrintBinaryTree |> ignore
    Axiom7 |> PrintBinaryTree |> ignore
    *)
    
    
    let testMatching = BinaryNode(Imp, AtomicNode(XVar), AtomicNode(BVar))
    let test1 = (FillExpression Axiom3 testMatching)
    ("Test Expression: " + (InOrderTraversal testMatching)) |> Console.WriteLine
    //("Test One: " + (InOrderTraversal test1)) |> Console.WriteLine
    
    //let testMatching = BinaryNode(Imp, BinaryNode(Con, AtomicNode(XVar), AtomicNode(YVar)), BinaryNode(Imp, AtomicNode(XVar), AtomicNode(YVar)))
    //let matchings = (MatchExpressionWithAxiom Axiom2 testMatching)
    //(printList matchings) |> ignore
    (*
    let testList3 = 
        BinaryNode(Imp, BinaryNode(Imp, AtomicNode(XVar), AtomicNode(YVar)),BinaryNode(Imp, AtomicNode(XVar), AtomicNode(ZVar)))
    let testMatch_3 = 
        (MatchExpressionWithAxiom Axiom2 testList3)
    "Attempting to match '(X -> Y) -> (X -> Z)' with Axiom 2" |> Console.WriteLine
    (printList testMatch_3) |> ignore
    "Now Determing All Dependencies in this matching." |> Console.WriteLine
    let dependencies1 = (DetermineDependencies (testMatch_3.Head) testList3 Imp)
    let dependencies2 = (DetermineDependencies ((testMatch_3.Tail).Head) testList3 Imp)
    "Dependencies for first matching: " |> Console.WriteLine
    (printList dependencies1) |> ignore
    "Dependencies for second matching:" |> Console.WriteLine
    (printList dependencies2) |> ignore
    "Testing Axiom1" |> Console.WriteLine
    let test_match_4 = 
        BinaryNode(Imp, AtomicNode(XVar), BinaryNode(Imp, AtomicNode(YVar), AtomicNode(XVar)))
    let test = (MatchExpressionWithAxiom Axiom1 test_match_4)
    (printList test)

    "Testing EqualityOfForm function" |> Console.WriteLine
    let equalityOfFormTest1 = 
        BinaryNode(Imp, BinaryNode(Con, AtomicNode(XVar), AtomicNode(YVar)), BinaryNode(Imp, AtomicNode(YVar), BinaryNode(Con, AtomicNode(XVar), AtomicNode(YVar))))
    "Expression to test on Axiom1: " + (InOrderTraversal equalityOfFormTest1) |> Console.WriteLine
    "Test Result" + (CheckEqualityOfForm equalityOfFormTest1 Axiom1).ToString() |> Console.WriteLine
    "Expression to test on Axiom2: " + (InOrderTraversal equalityOfFormTest1) |> Console.WriteLine
    "Test Result" + (CheckEqualityOfForm equalityOfFormTest1 Axiom2).ToString() |> Console.WriteLine
    let equalityOfFormTest2 = 
        BinaryNode(Imp, BinaryNode(Imp, AtomicNode(XVar), AtomicNode(YVar)), BinaryNode(Imp, BinaryNode(Imp, AtomicNode(XVar), AtomicNode(YVar)), BinaryNode(Imp, BinaryNode(Dis, AtomicNode(XVar), AtomicNode(ZVar)), AtomicNode(YVar))))
    "Expression to test on Axiom1, Axiom5 : " + (InOrderTraversal equalityOfFormTest2) |> Console.WriteLine
    "Test result: " + (CheckEqualityOfForm equalityOfFormTest2 Axiom1).ToString() |> Console.WriteLine 
    "Test result: " + (CheckEqualityOfForm equalityOfFormTest2 Axiom5).ToString() |> Console.WriteLine

    *)
    Console.ReadLine()
    0
    



