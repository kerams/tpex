module internal FSharp.TpEx.AstHelpers

open FSharp.Compiler.Syntax
open FSharp.Compiler.Xml
open FSharp.Compiler.SyntaxTrivia

let memberFlags isStatic: SynMemberFlags = {
    IsInstance = not isStatic
    IsDispatchSlot = false
    IsOverrideOrExplicitImpl = false
    IsFinal = false
    GetterOrSetterIsCompilerGenerated = false
    MemberKind = SynMemberKind.Member
}

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

let identPat m id =
    SynPat.LongIdent (SynLongIdent (id, [], []), None, None, SynArgPats.Pats [], None, m)

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
                        SynPat.Named (SynIdent (Ident (a, m), None), false, None, m)
                ],
                [],
                m
            ),
            m
        )
    ]

let prop m name (this: string option) body =
    let flags = memberFlags this.IsNone
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
    let bin = SynBinding (None, SynBindingKind.Normal, false, false, [], PreXmlDoc.Empty, valData, headPat, None, body, m, DebugPointAtBinding.NoneAtInvisible, SynBindingTrivia.Zero)

    SynMemberDefn.Member (bin, m)

let meth m name (this: string option) inlin ret param body =
    let flags = memberFlags this.IsNone

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
            SynPat.Typed (
                SynPat.Named (SynIdent (Ident (name, m), None), false, None, m),
                SynType.LongIdent (dottedIdToSynLongId m typ),
                m
            )
        )
        |> Array.toList

    let headPat = SynPat.LongIdent (SynLongIdent (id, [], []), None, None, SynArgPats.Pats [ SynPat.Paren (SynPat.Tuple (false, pats, [], m), m) ], None, m)
    let ret =
        match ret with
        | Some typ -> SynBindingReturnInfo (SynType.LongIdent (dottedIdToSynLongId m typ), m, [], { ColonRange = None }) |> Some
        | _ -> None

    let bin = SynBinding (None, SynBindingKind.Normal, inlin, false, [], PreXmlDoc.Empty, valData, headPat, ret, body, m, DebugPointAtBinding.NoneAtInvisible, SynBindingTrivia.Zero)

    SynMemberDefn.Member (bin, m)


let field m name typ = SynField ([], false, Some (Ident (name, m)), typ, false, PreXmlDoc.Empty, None, m, SynFieldTrivia.Zero)

let record m name fields =
    let fields =
        fields
        |> List.map (fun (name, typ) -> field m name typ)

    let repr = SynTypeDefnRepr.Simple (SynTypeDefnSimpleRepr.Record (None, fields, m), m)
    SynTypeDefn (compInfo m name, repr, [], None, m, SynTypeDefnTrivia.Zero)

let union m name cases =
    let cases =
        cases
        |> List.map (fun (name, _fields) ->
            SynUnionCase ([], SynIdent (Ident (name, m), None), SynUnionCaseKind.Fields [], PreXmlDoc.Empty, None, m, { BarRange = None }))

    let repr = SynTypeDefnRepr.Simple (SynTypeDefnSimpleRepr.Union (None, cases, m), m)
    SynTypeDefn (compInfo m name, repr, [], None, m, SynTypeDefnTrivia.Zero)

let clas m name members =
    let repr = SynTypeDefnRepr.ObjectModel (SynTypeDefnKind.Class, members, m)
    SynTypeDefn (compInfo m name, repr, [], None, m, SynTypeDefnTrivia.Zero)

let match' m expr clauses =
    SynExpr.Match (DebugPointAtBinding.NoneAtInvisible, expr, clauses, m, { MatchKeyword = m; WithKeyword = m })

let clause m pat expr =
    SynMatchClause (pat, None, expr, m, DebugPointAtTarget.No, SynMatchClauseTrivia.Zero)

let app m lid args = SynExpr.App (ExprAtomicFlag.NonAtomic, false, exprLongId m lid, args, m)

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
                SynPat.Named (SynIdent (Ident (name, m), None), false, None, m),
                None,
                rhs,
                m,
                DebugPointAtBinding.NoneAtInvisible,
                SynBindingTrivia.Zero)
        ],
        body,
        m,
        SynExprLetOrUseTrivia.Zero)

let rec sequentials m cont exprs =
    match exprs with
    | [] -> cont
    | h :: t -> SynExpr.Sequential (DebugPointAtSequential.SuppressBoth, true, h, sequentials m cont t, m, SynExprSequentialTrivia.Zero)