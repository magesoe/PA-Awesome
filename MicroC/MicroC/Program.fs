// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.
open System.IO
open System.Text
open Microsoft.FSharp.Text.Lexing

open Parser
open Lexer

let lexAndParseString str =
    let lexbuf = LexBuffer<_>.FromString str
    try 
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
    printfn "%A" argv
    0 // return an integer exit code
