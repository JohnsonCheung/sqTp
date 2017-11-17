#nowarn "40" 
#nowarn "64" 
namespace Lib.Dta
open Lib.Core
type simTy = SimNbr|SimTxt|SimLgc|SimDte|SimObj
type sdr = string[]
type dr = obj[]
type sdry = string[][]
type dry = obj[][]
type drs = {fny:string[];tyAy:simTy[];dry:dry}
type dt = {nm:string;drs:drs}
type ds = {nm:string;dtDic:dic<dt>}
open Lib.Core
module H = 
    let simTy(s:string) = 
        match s.ToUpper() with 
        | "NBR" -> SimNbr
        | "TXT" -> SimTxt
        | "LGC" -> SimLgc
        | "DTE" -> SimDte
        | "OBJ" -> SimObj
        | _ -> er "{simTy str} is invalid.  This is {valid}" [s;"[NBR | TXT | LGC | DTE | OBJ]"]
    let mkLin(wdtAy:int[]) filler sy =
        let left,mid,right = 
            let sep =
                match filler with 
                | " "->"|" 
                | "-" -> "+" 
                | _ -> er "{filler} should be '-' or ' '" [filler]
            let l = sep + filler
            let r = filler + sep
            let m = filler + sep + filler
            l,m,r
        let o = sy
        o|>Array.iteri (fun i cell -> o.[i] <- alignL(wdtAy.[i])(cell))
        left + (o|>jn mid) + right
    let toSimTy(o:obj):simTy = 
        match o.GetType().Name with 
        | "String" -> SimTxt
        | "DateTime" -> SimDte
        | _ -> SimObj
    let objToStr(o:obj):string = if (isNull o) then "#null" else o.ToString()
    let drSy = ayMap objToStr
    let sdryWdtAy(sdry:sdry) = 
        let f o dr =
            let oSz = sz o
            let drSz = sz dr
            let o = ayRz drSz 0 o
            dr |> Array.iteri (fun i s -> if len s > o.[i] then o.[i] <- len s)
            o
        sdry |> ayFold f [||]
    let drySdry(dry:dry):sdry =
        let f o dr = o @ [drSy dr]
        dry|>ayFold f [] |> lisToAy
    let sdryFmtLy sdry =
        let wdtAy = sdryWdtAy sdry
        let hdr =
            let f o w = o@[strDup w "-"]
            let ay = wdtAy |> ayFold f [] |> lisToAy
            mkLin wdtAy "-" ay
        let dtaLis =
            let f o sdr = o@[mkLin wdtAy " " sdr]
            sdry |> ayFold f []
        hdr::dtaLis@[hdr] |> lisToAy
    let dryFmtLy dry =
        let sdry = drySdry dry
        sdryFmtLy sdry
    let drs fldLvs simTyLvs dry = 
        let fny = splitLvs fldLvs
        let tyAy = splitLvs simTyLvs |> ayMap simTy
        if sz fny <> sz tyAy then er "{fldLvs}-{sz1} and {simTyLvs}-{sz1} are diff" [fldLvs;sz fny; simTyLvs; sz tyAy]
        {fny=fny;tyAy=tyAy;dry=dry}
    let drsFmtLy(drs:drs) =
        let fny = drs.fny
        let sdryFmtLy = 
            let sdry = drySdry drs.dry
            sdryFmtLy (ayAdd [|fny|] sdry)
        let lin= sdryFmtLy.[0]
        ayInsBef 2 [|lin|] sdryFmtLy
    let dt nm drs = {nm=nm;drs=drs}
    let dtFmtLy(dt:dt) = 
        let nm = dt.nm
        let drsFmtLy = drsFmtLy dt.drs
        Array.concat[[|"*Dt = " + nm|];drsFmtLy]
    let isSdic(o:obj) = match o with :? sdic -> true | _ -> false
    let dicDry(dic:Map<string,'a>):obj[][]= [|for i in dic do yield [|i.Key;i.Value|] |]
    let dicDrs dic = drs "Key Val" "Txt Obj" (dicDry dic)
    let dicDt dtNm dic = dt dtNm (dicDrs dic) 
    let dicFmtLy dic = dic |> dicDrs |> drsFmtLy
[<AutoOpen>]
module Dta =
    open H
    let dicDt = dicDt
    let dicDrs = dicDrs
    let dicDry = dicDry
    let dicFmtLy = dicFmtLy
    let dt = dt
    let drs = drs
    let dtFmtLy = dtFmtLy
    let drsFmtLy = drsFmtLy
    let dryFmtLy = dryFmtLy
    let sdryFmtLy = sdryFmtLy
