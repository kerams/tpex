namespace FSharp.TpEx

open System.Reflection
open Microsoft.FSharp.Core.CompilerServices
open ProviderImplementation.ProvidedTypes
open System.IO
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open AstHelpers

module Str =
    let appendCall m expr =
        app m [ "ignore" ] (app m [ "sb"; "Append" ] expr)

    let appendLiteral m string =
        SynExpr.Const (SynConst.String (string, SynStringKind.Regular, m), m)
        |> appendCall m

    let string1 m clsName typ =
        simpleLet
            m
            "sb"
            (app m [ "System"; "Text"; "StringBuilder" ] (exprUnit m))
            (sequentials m (app m [ "sb"; "ToString" ] (exprUnit m)) [ app m [ clsName; "String" ] (methodArgsExpr m [ identExpr m "x"; identExpr m "sb" ]) ])
        |> meth m "String" None false None [| "x", typ |]

    let string2rec m clsName (r: ExRecord) =
        sequentials
            m
            (appendLiteral m " }")
            [
                for i, (f, fTyp) in r.Fields () |> Array.indexed do
                    if i > 0 then
                        appendLiteral m $"; {f} = "
                    else
                        appendLiteral m $"{{ {f} = "

                    match fTyp with
                    | U _
                    | R _ -> app m [ clsName; "String" ] (methodArgsExpr m [ exprLongId m [ "x"; f ]; identExpr m "sb" ])
                    | _ -> appendCall m (exprLongId m [ "x"; f ])
            ]
        |> meth m "String" None false None [| ("x", $"{r.Path}{r.Name}"); ("sb", "System.Text.StringBuilder") |]

    let string2u m clsName (r: ExUnion) =
        match' m (identExpr m "x") [
            for c in r.Cases () do
                let fields = c.Fields ()

                match fields with
                | [||] ->
                    appendLiteral m c.Name
                    |> clause m (SynPat.LongIdent (dottedIdToSynLongId m $"{r.Path}{c.Name}", None, None, SynArgPats.Pats [], None, m))
                | [| _f, fTyp |] ->
                    sequentials m (exprUnit m) [
                        appendLiteral m $"{c.Name} "

                        match fTyp with
                        | U _
                        | R _ -> app m [ clsName; "String" ] (methodArgsExpr m [ exprLongId m [ "x" ]; identExpr m "sb" ])
                        | _ -> appendCall m (exprLongId m [ "x" ])
                    ]
                    |> clause m (SynPat.LongIdent (dottedIdToSynLongId m $"{r.Path}{c.Name}", None, None, SynArgPats.Pats [ identPat m [ Ident ("x", m) ] ], None, m))
                | _ ->
                    sequentials m (appendLiteral m ")") [
                        appendLiteral m $"{c.Name} "

                        for i, (f, fTyp) in Array.indexed fields do
                            if i > 0 then
                                appendLiteral m $", "
                            else
                                appendLiteral m $"("

                            match fTyp with
                            | U _
                            | R _ -> app m [ clsName; "String" ] (methodArgsExpr m [ exprLongId m [ f ]; identExpr m "sb" ])
                            | _ -> appendCall m (exprLongId m [ f ])
                    ]
                    |> clause m (SynPat.LongIdent (dottedIdToSynLongId m $"{r.Path}{c.Name}", None, None, patArgs m [ for (f, _) in fields -> f ], None, m))
        ]
        |> meth m "String" None false None [| ("x", $"{r.Path}{r.Name}"); ("sb", "System.Text.StringBuilder") |]

open Str

[<TypeProvider>]
type Providers (config) as this =
    inherit TypeProviderForNamespaces (config, assemblyReplacementMap = [("FSharp.TpEx", Path.GetFileNameWithoutExtension(config.RuntimeAssembly))], addDefaultProbingLocation = true)

    let getProviderType (assembly, nameSpace) = 
        let providerType = ProvidedTypeDefinition (assembly, nameSpace, "TpEx", Some typeof<obj>, hideObjectMethods = true)
    
        providerType.DefineStaticParameters (
            [ 
                ProvidedStaticParameter("Dummy", typeof<string>) 
            ],
            fun typeName _args -> ProvidedTypeDefinition (assembly, nameSpace, typeName, baseType = Some typeof<obj>, hideObjectMethods = true))
    
        providerType

    do 
        let assembly = Assembly.GetExecutingAssembly ()
        let nameSpace = this.GetType().Namespace
        
        this.AddNamespace (nameSpace, [ getProviderType (assembly, nameSpace) ])

    member _.GenerateStringer (m: range, vals: ExType[]): SynModuleDecl list =
        let cls = "Stringer"

        let full path name = $"{path}{name}"

        let ts =
            clas m cls (
                vals
                |> Array.collect (fun x ->
                   match x with
                    | R r ->
                        [|
                            string1 m cls (full r.Path r.Name)
                            string2rec m cls r
                        |]
                    | U u ->
                        [|
                            string1 m cls (full u.Path u.Name)
                            string2u m cls u
                        |]
                    | _ -> [||]
                )
                |> Array.toList
            )

        [ SynModuleDecl.Types ([ ts ], m) ]
