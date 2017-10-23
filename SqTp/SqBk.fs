#nowarn "40" 
#nowarn "64" 
namespace Lib.SqTp
open Lib.Core
open Typ
open Er
open Ay
open Predict
open Term
open Rmk
open Builder
open StrOp
open Lis
open Dic
module SqBk =
    let x = 1
type SqBk(tpBk:TpBk) =
    inherit TpBk(tpBk.lyBk)
    let a = if tpBk.ty <> SqBt.SwBk then er "Given {tpBk} is not SwBk" [tpBk]
    member x.aa(prm:Sdic,sw:Sdic):bool*string[] = true,[||]
    member x.vdt(prm:Sdic)(sw:Sdic):bool*string[] = // () = //(prm:Sdic,sw:Sdic):bool*string[] =
        let l = x.ly |> IxLin.wh (pNot isRmkLin)
        let r3 = l |> IxLin.chkDupTermOne
        let r = Array.concat[r3]
        IxLin.srcPutRslt r x.ly


