namespace Lib.Tp
open Lib.Core
[<AutoOpen>]
module ZTyp =
    type LyBk = {fstLinStr:string;ly:string[]}
    type LyTp = {linPfx:string;tp:string}
    let empLyBk = {fstLinStr="";ly=[||]}
module internal LyBk =
    let tp{fstLinStr=fstLinStr;ly=ly} = ly |> jnSyCrLf |> addPfx fstLinStr

    let make(linPfx:string)(ly:string[])=
        let l0 = ly.[0]
        let withPfx = l0 |> hasPfx linPfx
        let fstLinStr = if withPfx then l0 + "\r\n" else ""
        let ly' = if withPfx then ayRmvFstEle ly else ly
        {fstLinStr=fstLinStr;ly=ly'}
module internal BkLy =
    let lyBk linPfx bkLy = 
        if Array.isEmpty bkLy then empLyBk else
            let l0 = bkLy.[0]
            let fstLinStr =
                if l0="" then "" else l0 + "\r\n"
            let ly = Array.skip 1 bkLy
            {fstLinStr=fstLinStr;ly=ly}
module internal LlisLis =
    let rmvEmpLis = lisWh (List.isEmpty |> pNot)
module internal TpLy =
    let llisLis linPfx tpLy =
        let f (o,curLis) l = 
            if l |> hasPfx linPfx 
            then
                o @ [curLis],[l]
            else
                o,curLis @ [l]
        let o,curLis = tpLy |> ayFold f ([],[]) 
        o @ [curLis]
    let lyBkAy linPfx tpLy :LyBk[] =
        tpLy |> llisLis linPfx
             |> LlisLis.rmvEmpLis
             |> List.map List.toArray
             |> List.map (BkLy.lyBk linPfx)
             |> List.toArray
module internal LyBkAy =
    let tp lyBkAy = lyBkAy |> ayMap LyBk.tp |> jnSyCrLf
module internal Tp =
    let lyBkAy linPfx tp = 
        let ly = (tp|>splitCrLf)
        TpLy.lyBkAy linPfx ly

[<AutoOpen>]
module AutoOpen =
    let tpBrk(linPfx:string)(tp:string) : LyBk[] = Tp.lyBkAy linPfx tp
