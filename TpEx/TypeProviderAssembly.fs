namespace FSharp.TpEx

open System.Reflection
open Microsoft.FSharp.Core.CompilerServices
open ProviderImplementation.ProvidedTypes
open System.IO
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open AstHelpers
open System

//module Str =
//    let appendCall m expr =
//        app m [ "ignore" ] (app m [ "sb"; "Append" ] expr)

//    let appendLiteral m string =
//        SynExpr.Const (SynConst.String (string, SynStringKind.Regular, m), m)
//        |> appendCall m

//    let string1 m clsName typ =
//        simpleLet
//            m
//            "sb"
//            (app m [ "System"; "Text"; "StringBuilder" ] (exprUnit m))
//            (sequentials m (app m [ "sb"; "ToString" ] (exprUnit m)) [ app m [ clsName; "String" ] (methodArgsExpr m [ identExpr m "x"; identExpr m "sb" ]) ])
//        |> meth m "String" None false false None [| "x", typ |]

//    let string2rec m clsName (r: ExRecord) =
//        sequentials
//            m
//            (appendLiteral m " }")
//            [
//                for i, (f, fTyp) in r.Fields () |> Array.indexed do
//                    if i > 0 then
//                        appendLiteral m $"; {f} = "
//                    else
//                        appendLiteral m $"{{ {f} = "

//                    match fTyp with
//                    | U _
//                    | R _ -> app m [ clsName; "String" ] (methodArgsExpr m [ exprLongId m [ "x"; f ]; identExpr m "sb" ])
//                    | _ -> appendCall m (exprLongId m [ "x"; f ])
//            ]
//        |> meth m "String" None false false None [| ("x", Some $"{r.Path}{r.Name}"); ("sb", Some "System.Text.StringBuilder") |]

//    let string2u m clsName (r: ExUnion) =
//        match' m (identExpr m "x") [
//            for c in r.Cases () do
//                let fields = c.Fields ()

//                match fields with
//                | [||] ->
//                    appendLiteral m c.Name
//                    |> clause m (SynPat.LongIdent (dottedIdToSynLongId m $"{r.Path}{c.Name}", None, None, SynArgPats.Pats [], None, m))
//                | [| _f, fTyp |] ->
//                    sequentials m (exprUnit m) [
//                        appendLiteral m $"{c.Name} "

//                        match fTyp with
//                        | U _
//                        | R _ -> app m [ clsName; "String" ] (methodArgsExpr m [ exprLongId m [ "x" ]; identExpr m "sb" ])
//                        | _ -> appendCall m (exprLongId m [ "x" ])
//                    ]
//                    |> clause m (SynPat.LongIdent (dottedIdToSynLongId m $"{r.Path}{c.Name}", None, None, SynArgPats.Pats [ identPat m [ Ident ("x", m) ] ], None, m))
//                | _ ->
//                    sequentials m (appendLiteral m ")") [
//                        appendLiteral m $"{c.Name} "

//                        for i, (f, fTyp) in Array.indexed fields do
//                            if i > 0 then
//                                appendLiteral m $", "
//                            else
//                                appendLiteral m $"("

//                            match fTyp with
//                            | U _
//                            | R _ -> app m [ clsName; "String" ] (methodArgsExpr m [ exprLongId m [ f ]; identExpr m "sb" ])
//                            | _ -> appendCall m (exprLongId m [ f ])
//                    ]
//                    |> clause m (SynPat.LongIdent (dottedIdToSynLongId m $"{r.Path}{c.Name}", None, None, patArgs m [ for (f, _) in fields -> f ], None, m))
//        ]
//        |> meth m "String" None false false None [| ("x", Some $"{r.Path}{r.Name}"); ("sb", Some "System.Text.StringBuilder") |]

//open Str

module Remoting =
    let fName (typ: ExTypeW) =
        let rec inner typ =
            match typ.GenericParameters () |> Array.map inner |> String.concat ", " with
            | "" -> typ.Name
            | x -> $"{typ.Name}<{x}>"
        
        $"deser__{inner typ}"

    let createBinding m name rhs =
        SynBinding (
            None,
            SynBindingKind.Normal,
            false,
            false,
            [],
            empty (),
            SynValData (None, SynValInfo ([ [ SynArgInfo ([], false, Some (Ident ("data", m))); SynArgInfo ([], false, Some (Ident ("pos", m))) ] ], SynArgInfo ([], false, None)), None),
            SynPat.LongIdent (
                dottedIdToSynLongId m name,
                None,
                None,
                SynArgPats.Pats ([
                    SynPat.Paren (SynPat.Tuple (false, [
                        typedPat m "data" (SynType.Array (1, SynType.LongIdent (dottedIdToSynLongId m "byte"), m))
                        typedPat m "pos" (SynType.App (SynType.LongIdent (dottedIdToSynLongId m "ref"), None, [ SynType.LongIdent (dottedIdToSynLongId m "int") ], [], None, true, m))
                    ], [], m), m)
                ]),
                None,
                m
            ),
            None,
            rhs,
            m,
            DebugPointAtBinding.NoneAtInvisible,
            zero())

    let rec generateUnionFunc (funcs: ResizeArray<_>) m name typ (u: ExUnion) =
        let b =
            match' m (app m [ "deserInt32" ] (tuple m [ exprLongId m [ "data" ]; exprLongId m [ "pos" ] ])) [
                for i, case in u.Cases () |> Array.indexed do
                    let rhs =
                        let caseName =
                            [
                                if not (String.IsNullOrWhiteSpace typ.Path) then
                                    yield! typ.Path.Split ([| '.' |], StringSplitOptions.RemoveEmptyEntries)
                                yield typ.Name
                                yield case.Name
                            ]
                            |> exprLongId m

                        match case.Fields () with
                        | [||] -> caseName
                        | [| _x |] ->
                            SynExpr.Paren (unchecked, m, None, m)
                            |> app' m caseName
                        | x ->
                            tuple m [
                                // todo
                                for _e in x do
                                    unchecked
                            ]
                            |> app' m caseName

                    clause m (SynPat.Const (SynConst.Int32 i, m)) rhs

                clause m (namedPat m "b") (apps m [ exprLongId m [ "failwithf" ]; constString m $"Unexpected tag %%d for DU {name}"; exprLongId m [ "b" ] ])
            ]
            |> createBinding m name
        
        funcs.Add ((name, b))

    and generateRecordFunc (funcs: ResizeArray<_>) m n _r =
        let b = createBinding m n unchecked
        funcs.Add ((n, b))

    and generateArray (funcs: ResizeArray<_>) m n _typ =
        let b = createBinding m n unchecked
        funcs.Add ((n, b))

    and generateFunc (funcs: ResizeArray<_>) m typ =
        let n = fName typ

        match typ.Repr with
        | R r -> generateRecordFunc funcs m n r
        | U u -> generateUnionFunc funcs m n typ u
        | Array typ -> generateArray funcs m n typ
        | _ -> failwith "unsup generateFunc"

        n

    let generateMethodProxy funcs m typName x =
        let ps =
            match x.Parameters with
            | [| { Repr = Unit } |] -> [||]
            | [| _ |] ->
                x.Parameters
                |> Array.indexed
                |> Array.map (fun (i, _x) -> $"x{i}", None)
            | _ -> failwith "unsupp generateMethodProxy"

        app m [ "backgroundTask" ] (
            SynExpr.ComputationExpr (
                false,
                simpleLetBang
                    m
                    "data"
                    (
                        apps m [
                            exprLongId m [ "post" ]
                            exprLongId m [ "http" ]
                            apps m [ exprLongId m [ "op_Addition" ]; exprLongId m [ "url" ]; constString m $"{typName}/{x.Name}" ]

                            match x.Parameters with
                            | [| { Repr = Unit } |] -> exprUnit m
                            | _ -> exprLongId m [ "x0" ]
                        ]
                    )
                    (
                        simpleLet m "pos" (app m [ "ref" ] (SynExpr.Const ((SynConst.Int32 0), m))) (

                            let n =
                                match x.ReturnType.Repr with
                                | Task x -> generateFunc funcs m x
                                | _ -> failwith "unsup"
                            
                            app m [ n ] (SynExpr.Paren (SynExpr.Tuple (false, [ exprLongId m [ "data" ]; exprLongId m [ "pos" ] ], [], m), m, None, m))
                            |> ret m
                        )
                    ),
                m)
        )
        |> meth m x.Name (Some "this") false true None ps

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

    //member _.GenerateStringer (m: range, vals: ExTypeW[]): SynModuleDecl list =
    //    let cls = "Stringer"

    //    let full path name = $"{path}{name}"

    //    let ts =
    //        clas m cls (
    //            vals
    //            |> Array.collect (fun x ->
    //                match x with
    //                | R r ->
    //                    [|
    //                        string1 m cls (full r.Path r.Name |> Some)
    //                        string2rec m cls r
    //                    |]
    //                | U u ->
    //                    [|
    //                        string1 m cls (full u.Path u.Name |> Some)
    //                        string2u m cls u
    //                    |]
    //                | _ -> [||]
    //            )
    //            |> Array.toList
    //        )

    //    [ SynModuleDecl.Types ([ ts ], m) ]

    member _.GenerateRemotingProxy (m: range, vals: ExTypeW[]): SynModuleDecl list =
        let funcs = ResizeArray ()

        let ts =
            vals
            |> Array.collect (fun x ->
                match x.Repr with
                | I r ->
                    [|
                        intf m $"{x.Name}Proxy" [
                            SynMemberDefn.ImplicitCtor (
                                None,
                                [],
                                SynPat.Paren (
                                    SynPat.Tuple (false, [
                                        typedPat m "http" (SynType.LongIdent (dottedIdToSynLongId m "HttpClient"))
                                        typedPat m "url" (SynType.LongIdent (dottedIdToSynLongId m "System.String"))
                                    ], [], m),
                                    m),
                                None,
                                FSharp.Compiler.Xml.PreXmlDoc.Empty,
                                m,
                                { AsKeyword = None }
                            )

                            SynMemberDefn.Interface (
                                SynType.LongIdent (dottedIdToSynLongId m $"{x.Path}{x.Name}"),
                                Some m,
                                Some (
                                    r.Members()
                                    |> Array.map (Remoting.generateMethodProxy funcs m x.CompiledName)
                                    |> Array.toList
                                ),
                                m
                            )
                        ]
                    |]
                | _ -> [||]
            )
            |> Array.toList

        [
            SynModuleDecl.Open (SynOpenDeclTarget.ModuleOrNamespace (dottedIdToSynLongId m "System.Net.Http", m), m)
            SynModuleDecl.Open (SynOpenDeclTarget.ModuleOrNamespace (dottedIdToSynLongId m "FSharp.TpEx.Remoting", m), m)

            for _, f in funcs |> Seq.distinctBy fst do
                SynModuleDecl.Let (false, [ f ], m)

            SynModuleDecl.Types (ts, m)
        ]
