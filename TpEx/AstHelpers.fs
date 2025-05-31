module internal FSharp.TpEx.AstHelpers

open FSharp.Compiler.Syntax
open FSharp.Compiler.Xml
open FSharp.Compiler.SyntaxTrivia
open FSharp.Compiler.Text.Range

#nowarn 77

let memberFlags isStatic isIntImpl: SynMemberFlags = {
    IsInstance = not isStatic
    IsDispatchSlot = false
    IsOverrideOrExplicitImpl = isIntImpl
    IsFinal = false
    GetterOrSetterIsCompilerGenerated = false
    MemberKind = SynMemberKind.Member
}

let inline zero () : ^T = (^T : (static member Zero : ^T) ())
let inline empty () : ^T = (^T : (static member Empty : ^T) ())

let dottedIdToSynLongId m (id: string) =
    let idents =
        id.Split '.'
        |> Array.map (fun x -> Ident (x, m))
        |> Array.toList

    SynLongIdent (idents, [ for _ in 1 .. idents.Length - 1 -> m ], [])

let exprLongId m (ids: string list) =
    let dots = List.init (ids.Length - 1) (fun _ -> m)
    let ids =
        ids
        |> List.map (fun x -> Ident (x, m))
    SynExpr.LongIdent (false, SynLongIdent (ids, dots, []), None, m)

let identExpr m id = SynExpr.Ident (Ident (id, m))

let compInfo m typName =
    SynComponentInfo ([], None, [], [ Ident (typName, m) ], PreXmlDoc.Empty, false, None, m)

let compInfo' m atts typName =
    SynComponentInfo (atts, None, [], [ Ident (typName, m) ], PreXmlDoc.Empty, false, None, m)

let identPat m id =
    SynPat.LongIdent (SynLongIdent (id, [], []), None, None, SynArgPats.Pats [], None, m)

let namedPat m id =
    SynPat.Named (SynIdent (Ident (id, m), None), false, None, m)

let typedPat m id typ =
    SynPat.Typed (namedPat m id, typ, m)

let constString m x = SynExpr.Const (SynConst.String (x, SynStringKind.Regular, m), m)

let methodArgsExpr m args =
    SynExpr.Paren (
        SynExpr.Tuple (
            false,
            args,
            [],
            m
        ),
        m,
        None,
        m
    )

let patArgs m args =
    SynArgPats.Pats [
        SynPat.Paren (
            SynPat.Tuple (
                false,
                [
                    for a in args do
                        namedPat m a
                ],
                [],
                m
            ),
            m
        )
    ]

let prop m name (this: string option) isIntImpl body =
    let flags = memberFlags this.IsNone isIntImpl
    let curriedInfos =
        match this with
        | None -> [ [] ]
        | _ -> [ [ SynArgInfo ([], false, None) ]; [] ]

    let valData = SynValData (Some flags, SynValInfo (curriedInfos, SynArgInfo ([], false, None)), None)
    let id = [
        match this with
        | Some this -> Ident (this, m)
        | _ -> ()
        
        Ident (name, m)  
    ]
    let headPat = identPat m id
    let bin = SynBinding (None, SynBindingKind.Normal, false, false, [], PreXmlDoc.Empty, valData, headPat, None, body, m, DebugPointAtBinding.NoneAtInvisible, zero())

    SynMemberDefn.Member (bin, m)

let meth m name (this: string option) inlin isIntImpl ret param body =
    let flags = memberFlags this.IsNone isIntImpl

    let param' =
        param
        |> Array.map (fun (name, _) ->
            SynArgInfo ([], false, Ident (name, m) |> Some)
        )
        |> Array.toList

    let curriedInfos =
        match this with
        | None -> [ param' ]
        | _ -> [ [ SynArgInfo ([], false, None) ]; param' ]

    let valData = SynValData (Some flags, SynValInfo (curriedInfos, SynArgInfo ([], false, None)), None)
    let id = [
        match this with
        | Some this -> Ident (this, m)
        | _ -> ()
        
        Ident (name, m)  
    ]

    let pats =
        param
        |> Array.map (fun (name, typ) ->
            let name = namedPat m name

            match typ with
            | Some t ->
                SynPat.Typed (
                    name,
                    SynType.LongIdent (dottedIdToSynLongId m t),
                    m
                )
            | _ -> name
        )
        |> Array.toList

    let argPats =
        match pats with
        | [] -> SynArgPats.Pats [ SynPat.Paren (SynPat.Const (SynConst.Unit, m), m) ]
        | [p] -> SynArgPats.Pats [ SynPat.Paren (p, m) ]
        | _ -> SynArgPats.Pats [ SynPat.Paren (SynPat.Tuple (false, pats, [], m), m) ]

    let headPat = SynPat.LongIdent (SynLongIdent (id, [], []), None, None, argPats, None, m)
    let ret =
        match ret with
        | Some typ -> SynBindingReturnInfo (SynType.LongIdent (dottedIdToSynLongId m typ), m, [], { ColonRange = None }) |> Some
        | _ -> None

    let bin = SynBinding (None, SynBindingKind.Normal, inlin, false, [], PreXmlDoc.Empty, valData, headPat, ret, body, m, DebugPointAtBinding.NoneAtInvisible, zero())

    SynMemberDefn.Member (bin, m)


let field m name typ = SynField ([], false, Some (Ident (name, m)), typ, false, PreXmlDoc.Empty, None, m, zero())

let record m name fields =
    let fields =
        fields
        |> List.map (fun (name, typ) -> field m name typ)

    let repr = SynTypeDefnRepr.Simple (SynTypeDefnSimpleRepr.Record (None, fields, m), m)
    SynTypeDefn (compInfo m name, repr, [], None, m, zero())

let union m name cases =
    let cases =
        cases
        |> List.map (fun (name, _fields) ->
            SynUnionCase ([], SynIdent (Ident (name, m), None), SynUnionCaseKind.Fields [], PreXmlDoc.Empty, None, m, { BarRange = None }))

    let repr = SynTypeDefnRepr.Simple (SynTypeDefnSimpleRepr.Union (None, cases, m), m)
    SynTypeDefn (compInfo m name, repr, [], None, m, zero())

let clas m name members =
    let repr = SynTypeDefnRepr.ObjectModel (SynTypeDefnKind.Class, members, m)
    SynTypeDefn (compInfo m name, repr, [], None, m, zero())

let intf m name members =
    let repr = SynTypeDefnRepr.ObjectModel (SynTypeDefnKind.Unspecified, members, m)
    SynTypeDefn (compInfo' m [ { Range = m; Attributes = [ { TypeName = dottedIdToSynLongId m "Sealed"; ArgExpr = SynExpr.Const (SynConst.Unit, m); Target = None; AppliesToGetterAndSetter = false; Range = m } ] } ] name, repr, [], None, m, zero())

let match' m expr clauses =
    SynExpr.Match (DebugPointAtBinding.NoneAtInvisible, expr, clauses, m, { MatchKeyword = m; WithKeyword = m })

let clause m pat expr =
    SynMatchClause (pat, None, expr, m, DebugPointAtTarget.No, zero())

let catchAll m expr = clause m (SynPat.Wild m) expr

let tuple m exprs =
    SynExpr.Paren (
        SynExpr.Tuple (false, exprs, [], m),
        m,
        None,
        m
    )

let app m lid args = SynExpr.App (ExprAtomicFlag.NonAtomic, false, exprLongId m lid, args, m)

let app' m func arg = SynExpr.App (ExprAtomicFlag.NonAtomic, false, func, arg, m)

let apps m (exprs: _ list) =
    let rec inner cont exprs =
        match exprs with
        | [] -> cont
        | h :: t -> SynExpr.App (ExprAtomicFlag.NonAtomic, false, inner h t, cont, m)

    let exprs = List.rev exprs
    inner exprs.Head exprs.Tail

let tapp m expr args = SynExpr.TypeApp (expr, m, args, [], None, m, m)

let exprUnit m = SynExpr.Const (SynConst.Unit, m)

let simpleLet m name rhs body =
    SynExpr.LetOrUse (
        false,
        false,
        [
            SynBinding (
                None,
                SynBindingKind.Normal,
                false,
                false,
                [],
                PreXmlDoc.Empty,
                SynValData (None, SynValInfo ([], SynArgInfo ([], false, None)), None),
                namedPat m name,
                None,
                rhs,
                m,
                DebugPointAtBinding.NoneAtInvisible,
                zero())
        ],
        body,
        m,
        zero())

let simpleLetBang m name rhs body =
    SynExpr.LetOrUseBang (
        DebugPointAtBinding.NoneAtInvisible,
        false,
        true,
        namedPat m name,
        rhs,
        [],
        body,
        m,
        zero())

let ret m expr =
    SynExpr.YieldOrReturn (
        (false, true),
        expr,
        m,
        zero()
    )

let rec sequentials m cont exprs =
    match exprs with
    | [] -> cont
    | h :: t -> SynExpr.Sequential (DebugPointAtSequential.SuppressBoth, true, h, sequentials m cont t, m, zero())

let unchecked = tapp range0 (exprLongId range0 [ "Unchecked"; "defaultof" ]) [ SynType.Anon range0 ]