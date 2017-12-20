[<AutoOpen>]
module Lib.Tp
open Lib.Core
type linPfx = string
type tp = lines
type tpFt = ft
type bk = {fstLinOpt:lin option;ly:ly}
let empBk = {fstLinOpt=None;ly=[||]}
let bkLines(bk:bk):lines = 
    let l = jnCrLf bk.ly
    if isSome bk.fstLinOpt then bk.fstLinOpt.Value+"\r\n"+l else l
let bkAyTp(bkAy:bk[]):tp = ayMap bkLines bkAy |> jnCrLf
let toBk linPfx ly = 
    match fstEleOpt ly with
    | Some l0 ->
        let withPfx = l0 |> hasPfx linPfx
        let fstLinOpt = if withPfx then Some l0 else None
        let ly' = if withPfx then ayRmvFstEle ly else ly
        {fstLinOpt=None;ly=ly'}
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
