namespace Lib.Core
type LyBk(fstLinStr:string,ly:string[]) =
    member x.ly = ly
    member x.tp = ly |> jnSyCrLf |> addPfx fstLinStr
    member x.fstLinStr = fstLinStr
    new(lyBk:LyBk) = LyBk(lyBk.fstLinStr,lyBk.ly)
module LyTp =
    let ly'lyBk(linPfx:string)(ly:string[])=
        let l0 = ly.[0]
        let withPfx = l0 |> hasPfx linPfx
        let fstLinStr = if withPfx then l0 + "\r\n" else ""
        let ly' = if withPfx then ayRmvFstEle ly else ly
        LyBk(fstLinStr,ly')

    let ly'llisLis linPfx ly =
        let f (o,curLis) l = 
            if l |> hasPfx linPfx 
            then
                o @ [curLis],[l]
            else
                o,curLis @ [l]
        let o,curLis = ly |> ayFold f ([],[]) 
        o @ [curLis]
    let llisLis'rmvEmpLis = lisWh (List.isEmpty |> pNot)

open LyTp
type LyTp(linPfx:string,ly:string[]) =
    let lyBkAy' = 
        ly |> ly'llisLis linPfx
           |> llisLis'rmvEmpLis
           |> List.map List.toArray
           |> List.map (ly'lyBk linPfx)
           |> List.toArray
    new(linPfx,tp) = LyTp(linPfx,splitCrLf tp)
    member x.tp = lyBkAy' |> ayMap(fun(i:LyBk)->i.tp) |> jnSyCrLf
    member x.ly = ly
    member x.linPfx = linPfx
    member x.lyBkAy = lyBkAy'