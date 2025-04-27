module Main

type _Dummy = FSharp.TpEx.TpEx<"">

module Contract =
    type G = { A: ResizeArray<byte> }
    type F = {X:int; Z: string; GG: G}

    type D =
        | A of g:int * wtf: F
        | B
        | C of D

    module FFF =
        type Blo = {B:string}
        type F = int

[<FSharp.TpEx.GenerateStringer (typeof<Contract>)>]
module StringerGenerated =
    do ()

open Contract
open StringerGenerated

[<EntryPoint>]
let main _ =
    let v = { GG = { A = ResizeArray () }; X = 1; Z = "deda" }
    let v2 = A (1, v)
    Stringer.String v |> printfn "%s"
    Stringer.String v2 |> printfn "%s"

    printfn "%A" v
    printfn "%A" v2
    0
