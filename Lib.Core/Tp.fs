namespace Lib.Tp
open Lib.Core
type linPfx = string
type tp = lines
type tpFt = ft
type bk(fstLinOpt:lin option,ly:ly) =
    member x.fstLinOpt = fstLinOpt
    member val ly = ly with get,set
[<AutoOpen>]
module ZTyp =
    let empBk = bk(None,[||])
module H1 =
    open Lib.Core
    open ZTyp
    let bkLines(bk:bk):lines = 
        let l = jnCrLf bk.ly
        if isSome bk.fstLinOpt then bk.fstLinOpt.Value+"\r\n"+l else l
    let bkAyTp(bkAy:bk[]):tp = ayMap bkLines bkAy |> jnCrLf
module H2 =
    open Lib.Core
    open ZTyp
    let toBk linPfx ly = 
        match fstEleOpt ly with
        | Some l0 ->
            let withPfx = l0 |> hasPfx linPfx
            let fstLinOpt = if withPfx then Some l0 else None
            let ly' = if withPfx then ayRmvFstEle ly else ly
            bk(fstLinOpt,ly')
        | _ -> empBk
    let toLyLis linPfx tpLy =
        let f (o,curLis) l = 
            if l |> hasPfx linPfx 
            then
                o @ [curLis],[l]
            else
                o,curLis @ [l]
        let o,curLis = tpLy |> ayFold f ([],[]) 
        o @ [curLis] |> lisWh (List.isEmpty|>pNot)
                     |> lisMap(List.toArray) 
       
    let tpBkAy linPfx = splitCrLf >> toLyLis linPfx >> lisMap (toBk linPfx) >> lisToAy
    let tpFtBkAy linPfx = ftLines >> tpBkAy linPfx
[<AutoOpen>]
module Tp =
    let tpBkAy = H2.tpBkAy
    let tpFtBkAy = H2.tpFtBkAy
    let bkAyTp = H1.bkAyTp
    let empBk = ZTyp.empBk