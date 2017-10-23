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
module SwBk =
    let swL'chk lin = oneOf {
        if (fstChr lin) <> "?" then return "must begin with ?"
        let nTerm = nTerm lin
        if nTerm < 3 then return "must have 3 or more terms"
        let s = sndTerm lin
        if s |> isInLis ["EQ";"NE";"AND";"OR"] |> not then return "2nd term is operator, it must be [NE EQ OR AND]"
        if s |> isInLis ["EQ";"NE"] && (nTerm<>4) then return "when 2nd term is [EQ|NE], it must have 4 terms"
        }
    let chkSwLin1 prm lin = Some ""
open SwBk
type SwBk(tpBk:TpBk) =
    inherit TpBk(tpBk.lyBk)
    let a = if tpBk.ty <> SqBt.SwBk then er "Given {tpBk} is not SwBk" [tpBk]
    member x.aa(prm:Sdic,sw:Sdic):bool*string[] = true,[||]
    member  x.vdt(prm:Sdic):bool*string[] = // () = //(prm:Sdic,sw:Sdic):bool*string[] =
        let l = x.ly |> IxLin.wh (pNot isRmkLin)
        let r1 = l |> IxLin.chkSrcLin swL'chk
        let r2 = l |> IxLin.chkSrcLin (chkSwLin1 prm)
        let r3 = l |> IxLin.chkDupTermOne
        let r = Array.concat[r1;r2;r3]
        IxLin.srcPutRslt r x.ly

