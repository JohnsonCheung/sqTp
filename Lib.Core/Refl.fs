#nowarn "40" 
#nowarn "64" 
namespace Lib.Refl
open Lib.Core
open System.Reflection
type ty = System.Type
type nmTy<'a when 'a : (member Name:string)> = class end
[<AutoOpen>]
module Asm =
    let asmLis(asm:Assembly) = 
        (*
        let a:Assembly = null
        a.LoadModule ppDomain.CurrentDomain.ActivationContext.
        let x = System.Diagnostics.Process.GetCurrentProcess().Modules
        [ for i in x do yield i.FileName ]
        *)
        asm
[<AutoOpen>]
module Ty =
    let tyAss(ty:ty) = ty.Assembly
    let tyAssOf<'a> = typeof<'a> |> tyAss
    let tyPrpNy(ty:ty) = ty.GetProperties() |> ayMap (fun(p:PropertyInfo)->p.Name)
    let tyPrpNyOf<'a> = typeof<'a> |> tyPrpNy
open Ty
/// object reflection
[<AutoOpen>]
module ObjRefl =
    let tyNm(ty:ty) = ty.Name
    let tyFullNm(ty:ty) = ty.FullName
    let tyNmOf<'a> = typeof<'a> |> tyNm
    let tyFullNmOf<'a> = typeof<'a> |> tyFullNm
    let ty o = o.GetType()
    let oNz f o = if isNull o then null else f o
    let oTy = oNz (fun(o:obj)->o.GetType()) 
    let oAss o = o |> oTy |> tyAss
    let pubPrp = BindingFlags.Public + BindingFlags.GetProperty + BindingFlags.Instance + BindingFlags.IgnoreCase
    let oMInfAy o = o.GetType().GetMembers(pubPrp)
    let isPrp(mInf:MemberInfo) = 
        match mInf with 
        | :? PropertyInfo as p -> p.GetMethod.GetParameters().Length = 0
        | _ -> false
    let hasPrp prpNm o =
        if isNull o then false else
            let mInfAy = o.GetType().GetMember(prpNm,pubPrp)
            if mInfAy.Length <> 1 then false else mInfAy.[0] |> isPrp
    let prpInf nm o = 
        if isNull o then null else 
            if hasPrp nm o |> not then null else
                o.GetType().GetMember(nm,pubPrp).[0]:?>PropertyInfo
    let prp nm o =
        let p = prpInf nm o
        if isNull p then null else p.GetValue o
    let prpNm o = prp "Name" o :?> string
    let sprp = prp >> string
    let prpNy o = oMInfAy o |> Array.where isPrp |> Array.map prpNm
[<AutoOpen>]
module Union =
    open Microsoft.FSharp.Reflection
    let isUnion<'a> = FSharpType.IsUnion(typeof<'a>)
    let assertIsUnion<'a> =
        if isUnion<'a> |> not then er "Given {ty} is not Union-Type" [tyNmOf<'a>]
    let unionCaseNm(unionCase:UnionCaseInfo):string = unionCase.Name
    let unionNy<'a> : ny = FSharpType.GetUnionCases typeof<'a> |> ayMap unionCaseNm

    let private y<'a> ignoreCase nm:'a option = 
        let eq = if ignoreCase then (=~) else (=)
        let eqNm(x:UnionCaseInfo) = eq x.Name nm
        match FSharpType.GetUnionCases typeof<'a> |> ayWh eqNm with
        | [|c|] -> FSharpValue.MakeUnion(c,[||]) :?> 'a |> some
        | _ -> None
    let private x<'a> ignoreCase nm:'a =
        match y<'a> ignoreCase nm with
        | Some x -> x
        | _ -> 
            let tyNm = tyFullNmOf<'a>
            let names = unionNy<'a> |> jn " | " |> quote "[]"
            er "{nm} is not any unioncase case of {type}.  This is possible {cases}" [nm;tyNm;names]
    let unionParse<'a> = x<'a> false
    let unionParseI<'a> = x<'a> true
    let unionTryParse<'a> = y<'a> false
    let unionTryParseI<'a> = y<'a> false

//    let unionParse<'a>:'a = isInAy unionNy<'a>
//    let enmValAy<'a> :'a[] = 
