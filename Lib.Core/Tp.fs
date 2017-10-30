namespace Lib.Tp
open Lib.Core
type Bk = {fstLinStr:string;mutable ly:string[]}
module ZTyp =
    let empBk = {fstLinStr="";ly=[||]}
open ZTyp
module internal Bk =
    let tp{fstLinStr=fstLinStr;ly=ly} = ly |> jnCrLf |> addPfx fstLinStr
    let make linPfx (ly:string[])=
        let l0 = ly.[0]
        let withPfx = l0 |> hasPfx linPfx
        let fstLinStr = if withPfx then l0 + "\r\n" else ""
        let ly' = if withPfx then ayRmvFstEle ly else ly
        {fstLinStr=fstLinStr;ly=ly'}
module internal BkLy =
    let bk linPfx bkLy :Bk = 
        let ly = bkLy
        if Array.isEmpty ly then empBk else
            let l0 = ly.[0]
            let fstLinStr =
                if l0="" then "" else l0 + "\r\n"
            let ly = Array.skip 1 ly
            {fstLinStr=fstLinStr;ly=ly}
module internal Ly =
    let bkLyLis linPfx ly:string[] list =
        let f (o,curLis) l = 
            if l |> hasPfx linPfx 
            then
                o @ [curLis],[l]
            else
                o,curLis @ [l]
        let o,curLis = ly |> ayFold f ([],[]) 
        let a = o @ [curLis]
        let b = a |> lisWh (List.isEmpty|>pNot)
        let c = b |> lisMap(List.toArray) 
        c
    let bkAy linPfx ly =
        ly |> bkLyLis linPfx
           |> List.map (BkLy.bk linPfx)
           |> List.toArray
module internal BkAy =
    let tp bkAy = 
        let a = bkAy |> ayMap Bk.tp 
        let o = a |> jnCrLf
        o
module Tp' =
    let bkAy linPfx tp:Bk[] = 
        let ly = (tp|>splitCrLf)
        Ly.bkAy linPfx ly
    let tst() =
        let tp ="""
lskdfjlsdkfsdf
=============
lsdfjlskdf
============
lsdfkj
"""
        printf "%A" (bkAy "--" tp)
[<AutoOpen>]
module Tp =
    let tpBrk = Tp'.bkAy
    let tpBkAyToStr = BkAy.tp 
    let tst = Tp'.tst