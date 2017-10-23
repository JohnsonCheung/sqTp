#nowarn "40" 
#nowarn "64" 
namespace Lib.SqTp
open Lib.Core
open Lib.SqTp
open Typ
open Er
open Predict
open Dic
module PrmBk =
    type prmDic = Map<string,string>
open PrmBk
type PrmBk(tpBk:TpBk) =
    inherit TpBk(tpBk)
    let a = if (tpBk.ty) <> SqBt.SqBk then er "Given {tpBk} does not have type {PrmBk}" [tpBk]
    member x.vdt(prm:Sdic)(sw:Sdic):bool*string[] =
        (*
        let l = x.ly |> IxLin.wh (pNot isRmkLin)
        let r1 = l |> IxLin.chkSrcLin swL'chk
        let r2 = l |> IxLin.chkSrcLin (chkSwLin1 prm sw)
        let r3 = l |> IxLin.chkDupTermOne
        let r = Array.concat[r1;r2;r3]
        *)
        true,[||]
    member x.evl(): prmDic = empSdic
