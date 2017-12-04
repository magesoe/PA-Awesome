// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.
open System.IO
open System.Text
open Microsoft.FSharp.Text.Lexing

open Parser
open Lexer
open Analysis

let lexAndParseString str=
    let lexbuf = LexBuffer<_>.FromString str
    try 
        printfn "lexAndParseString"
        Main tokenize lexbuf
    with e ->
        let pos = lexbuf.EndPos
        printfn "Error near line %d, character %d\n" pos.Line pos.Column
        failwith "parser termination";;
    
let lexAndParseFromFile filename =
    if File.Exists(filename) then lexAndParseString(File.ReadAllText(filename))
    else invalidArg "Program" "File not found";;


[<EntryPoint>]
let main argv = 
    match argv with
    | [|filename; min; max|] -> 
        let program = lexAndParseFromFile filename
        printfn "Parsing completed"
        let (rdStart, rdMap, rdRes) = doRDAnalysis program
        let (lvStart, lvMap, lvRes) = doLVAnalysis program
        let (_, dosMap, dosRes) = doDetectSignsAnalysis program
        let (_, iaMap, iaRes) = doIntervalAnalysis (min |> int) (max |> int) program
        printfn "Program Graph forward:"
        printfn "%A" rdMap
        printfn "Start Node: %d" rdStart
        printfn "%A" dosMap
        printfn ""
        printfn "%A" iaMap
        printfn "Program Graph reverse:"
        printfn "%A" lvMap
        printfn "Start Node: %d" lvStart
        printfn "Reaching Definitions Analysis result:"
        printfn "%A" rdRes
        printfn "Live Variable Analysis result:"
        printfn "%A" lvRes
        printfn "Detection of Signs Analysis result:"
        printfn "%A" dosRes
        printfn "Interval Analysis result:"
        printfn "%A" iaRes
        0
    | _ -> failwith "Expected exactly three parameters";;
