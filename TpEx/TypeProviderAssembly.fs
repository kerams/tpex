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

    let caseOrFieldNameQualifiedExpr m typ caseOrField = 
        [
            if not (String.IsNullOrWhiteSpace typ.Path) then
                yield! typ.Path.Split ([| '.' |], StringSplitOptions.RemoveEmptyEntries)
            yield typ.Name
            yield caseOrField
        ]
        |> exprLongId m

    let caseOrFieldNameQualifiedSynLong m typ caseOrField = 
        dottedIdToSynLongId m $"{typ.Path}{typ.Name}.%s{caseOrField}"

    let deserCall' m (funcName, umxCastRequired) =
        let call = app m [ funcName ] (tuple m [ exprLongId m [ "data" ]; exprLongId m [ "pos" ] ])

        if umxCastRequired then
            app m [ "op_Splice" ] call
        else
            call

    let deserCall m funcName =
        deserCall' m (funcName, false)

    let rec generateUnionFunc (funcs: ResizeArray<_>) m name typ (u: ExUnion) =
        let b =
            // 1 element array if fieldless case
            // 2 element otherwise
            simpleLet m "_todoValidate" (deserCall m "readArrayLength") (
                match' m (deserCall m "deserInt32") [
                    for i, case in u.Cases () |> Array.indexed do
                        let rhs =
                            let caseName = caseOrFieldNameQualifiedExpr m typ case.Name

                            match case.Fields () with
                            | [||] -> caseName
                            | [| _name, typF |] ->
                                // single field cases serialized directly
                                SynExpr.Paren (deserCall' m (generateFunc funcs m typF), m, None, m)
                                |> app' m caseName
                            | x ->
                                // multi field need an array
                                simpleLet m "_todoValidate" (deserCall m "readArrayLength") (
                                    tuple m [
                                        for _name, typF in x do
                                            deserCall' m (generateFunc funcs m typF)
                                    ]
                                    |> app' m caseName
                                )

                        clause m (SynPat.Const (SynConst.Int32 i, m)) rhs

                    clause m (namedPat m "b") (apps m [ exprLongId m [ "failwithf" ]; constString m $"Unexpected tag %%d for DU {name}"; exprLongId m [ "b" ] ])
                ]
            )
            |> createBinding m name
        
        funcs.Add ((name, b))

    and generateOptionFunc (funcs: ResizeArray<_>) m name typ =
        let b =
            iff
                m
                (apps m [ exprLongId m [ "op_GreaterThan" ]; deserCall m "readArrayLength"; constInt m 2 ])
                (app m [ "failwith" ] (constString m "expected array with fewer than 3 elements for option"))
                (
                    SynExpr.Sequential (
                        DebugPointAtSequential.SuppressBoth,
                        true,
                        SynExpr.LongIdentSet (dottedIdToSynLongId m "pos.Value", apps m [ exprLongId m [ "op_Addition" ]; exprLongId m [ "pos"; "Value" ]; constInt m 1 ], m),
                        (
                            iff
                                m
                                (
                                    apps m [
                                        exprLongId m [ "op_Equality" ]
                                        
                                        SynExpr.DotIndexedGet (
                                            exprLongId m [ "data" ],
                                            (
                                                apps m [ exprLongId m [ "op_Subtraction" ]; exprLongId m [ "pos"; "Value" ]; constInt m 1 ]
                                            ),
                                            m,
                                            m
                                        )

                                        SynExpr.Const (SynConst.Byte 0uy, m)
                                    ]
                                )
                                (exprLongId m [ "Option"; "None" ])
                                (
                                    app m [ "Option"; "Some" ] (SynExpr.Paren (deserCall' m (generateFunc funcs m typ), m, None, m))
                                    |> Some
                                )
                        ),
                        m,
                        zero ()
                    )
                    |> Some
                )
            |> createBinding m name
        
        funcs.Add ((name, b))

    and generateRecordFunc (funcs: ResizeArray<_>) m n typ r =
        let b =
            simpleLet m "_todoValidate" (deserCall m "readArrayLength") (
                SynExpr.Record (
                    None,
                    None,
                    [
                        for name, typF in r.Fields () do
                            SynExprRecordField (
                                (caseOrFieldNameQualifiedSynLong m typ name, true),
                                None,
                                Some (deserCall' m (generateFunc funcs m typF)),
                                None
                            )
                    ],
                    m
                )
            )
            |> createBinding m n

        funcs.Add ((n, b))

    and generateArray (funcs: ResizeArray<_>) m n typ =
        let b =
            simpleLet m "len" (deserCall m "readArrayLength") (
                simpleLet m "a" (app m [ "zeroCreateUnchecked" ] (exprLongId m [ "len" ])) (
                    SynExpr.Sequential (
                        DebugPointAtSequential.SuppressBoth,
                        true,
                        (
                            foreach
                                m
                                (namedPat m "i")
                                (SynExpr.IndexRange (Some (constInt m 0), m, Some (apps m [ exprLongId m [ "op_Subtraction" ]; exprLongId m [ "len" ]; constInt m 1 ]), m, m, m))
                                (SynExpr.DotIndexedSet (
                                    exprLongId m [ "a" ],
                                    exprLongId m [ "i" ],
                                    deserCall' m (generateFunc funcs m typ),
                                    m,
                                    m,
                                    m)
                                )
                        ),
                        exprLongId m [ "a" ],
                        m,
                        zero()
                    )
                )
            )
            |> createBinding m n

        funcs.Add ((n, b))

    and generateTuple (funcs: ResizeArray<_>) m n types =
        let b =
            simpleLet m "_todoValidate" (deserCall m "readArrayLength") (
                tuple m [ for typ in types -> deserCall' m (generateFunc funcs m typ) ]
            )
            |> createBinding m n

        funcs.Add ((n, b))

    // let deserInt32StringFSharpOptionStringTupleMap (data: byte[], pos: int ref) =
    //     let len = readArrayLength (data, pos)
    //     Array.init len (fun _ -> deserInt32 (data, pos), deserStringFSharpOptionStringTuple (data, pos))
    //     |> Map.ofArray
    and generateMap (funcs: ResizeArray<_>) m n typK typV =
        let b =
            simpleLet m "_todoValidate" (deserCall m "readArrayLength") (
                apps m [
                    exprLongId m [ "Map"; "ofArray" ]

                    apps m [
                        exprLongId m [ "Array"; "init" ]
                        exprLongId m [ "_todoValidate" ]

                        lambda m [ SynSimplePat.Id (Ident ("_", m), None, true, false, false, m) ] (
                            tuple m [
                                deserCall' m (generateFunc funcs m typK)
                                deserCall' m (generateFunc funcs m typV)
                            ]
                        )
                    ]
                ]
            )
            |> createBinding m n

        funcs.Add ((n, b))

    and generateFunc (funcs: ResizeArray<_>) m typ =
        let rec inner typ =
            match typ.Repr with
            | Tuple _
            | F _
            | MapEx _
            | Array _
            | Unit
            | Option _
            | Task _ -> typ.Name
            | _ ->
                match typ.GenericParameters () |> Array.map inner |> String.concat "," with
                | "" -> typ.Name
                | x -> $"{typ.Name}<{x}>"

        let n = $"deser_{inner typ}"

        let existing =
            match typ.Repr with
            | R r -> generateRecordFunc funcs m n typ r; None
            | U u -> generateUnionFunc funcs m n typ u; None
            | Option typ -> generateOptionFunc funcs m n typ; None
            | Array typ -> generateArray funcs m n typ; None
            | Tuple types -> generateTuple funcs m n types; None
            | MapEx (typK, typV) -> generateMap funcs m n typK typV; None
            | Unit -> Some ("deserUnit", false)
            | C _ ->
                match typ.Name with
                | "String" -> ("deserString", true)
                | "Boolean" -> ("deserBoolean", false)
                | "Int16" -> ("deserInt16", true)
                | "Int32" -> ("deserInt32", true)
                | "Int64" -> ("deserInt64", true)
                | "TimeOnly" -> ("deserTimeOnly", false)
                | "DateOnly" -> ("deserDateOnly", false)
                | "DateTimeOffset" -> ("deserDateTimeOffset", false)
                | "Guid" -> ("deserGuid", true)
                | _ -> failwithf "unsup generateFunc %A" typ
                |> Some
            | Task _
            | F _
            | I _ -> failwithf "unsup generateFunc %A" typ

        existing |> Option.defaultValue (n, false)

    let generateMethodProxy funcs m typName x =
        let ps =
            match x.Parameters with
            | [| { Repr = Unit } |] -> [||]
            | [| _ |] ->
                x.Parameters
                |> Array.indexed
                |> Array.map (fun (i, _x) -> $"x{i}", None)
            | _ -> failwithf "unsupp generateMethodProxy parameters %s.%s" typName x.Name

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

                            let n, umxCastRequired =
                                match x.ReturnType.Repr with
                                | Task x -> generateFunc funcs m x
                                | _ -> failwithf "unsupp generateMethodProxy return type %s.%s" typName x.Name
                            
                            let call = app m [ n ] (SynExpr.Paren (SynExpr.Tuple (false, [ exprLongId m [ "data" ]; exprLongId m [ "pos" ] ], [], m), m, None, m))
                            
                            if umxCastRequired then
                                app m [ "op_Splice" ] call |> ret m
                            else
                                ret m call
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
            SynModuleDecl.Open (SynOpenDeclTarget.ModuleOrNamespace (dottedIdToSynLongId m "FSharp.UMX", m), m)

            for _, f in funcs |> Seq.distinctBy fst do
                SynModuleDecl.Let (false, [ f ], m)

            SynModuleDecl.Types (ts, m)
        ]
