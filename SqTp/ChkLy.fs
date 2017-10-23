#nowarn "40" 
#nowarn "64" 
namespace Lib.ChkLy
open Lib.Core
module Typ =
    type ILin = { ix: int; lin: string }
    type IMsg = { ix: int; msg: string }
open Typ
module H1 =
    let wh(cond:string->bool)(ly:string[]):ILin[] = 
        let x(i,lin)=if(cond lin) then Some({ix=i;lin=lin}) else None
        ayAddIdx ly |> ayChoose x
    let private fndMsg i r = r|>ayWh(fun r->r.ix = i)|>ayMap(fun r->r.msg) 
    let private addMsg r i lin = lin,fndMsg i r
    let private pack rLin = 
        let lin,msg = rLin
        let len = len lin
        syTab lin len msg
    let private unpack rLin = if rLin|>snd|>Array.isEmpty then [|rLin|>fst|>rtrim|] else pack rLin
    let private put' r src = src |> syAlignL |> ayMapi(addMsg r) |> ayMap unpack |> Array.concat
module ChkDupF1 = 
    let x dup fstTermLis =                      // for each ix of value f in fstTermAy,
                                                // if f is in dup, 
                                                // return string option list indicating which fstTermLis item has dup(f)
                                                   
        let f fstTerm = if (fstTerm |> isInLis dup) then Some(sprintf "dup(%s)" fstTerm) else None
        let o = fstTermLis |> lisMap f
        o
    let doc = """{dupLis} {fstTermLis} -> {string option list}
for each fstTerm, if found in dupLis return Some "Dup(?)" else None
"""
    let eg() =
        let dup = ["aa";"bb"]
        let fstTerm = ["aa";"aa";"cc";"bb";"dd"]
        erLines doc [dup;fstTerm;x dup fstTerm]
module ChkDupF =
    let x(linLis:string list):string option list =
        let fstTermLis = linLis |> lisMap fstTerm
        let dup = lisWhDup fstTermLis              // duplicated fstTerm items
        let o = ChkDupF1.x dup fstTermLis           // find its ly-index
        o
    let doc = """{linLis} -> {string option list} Check-Duplicate-Function
where the (output-list-item).Some is the er msg for dup item: in dup(?)
"""
    let eg() = 
        let tp = """
xx bb cc
aa bb
cc dd
aa dd
cc dd
ddd
xxx
cc  dd"""
        let linLis = splitCrLf tp |> ayToLis
        prtS "linLis: "
        prtS tp
        x linLis
module Chk =
    let x ixLis erOptLis = 
        query {
            for (ix,erOpt) in List.zip ixLis erOptLis do
            where (isSome erOpt)
            select (ix,erOpt.Value)
        } |> Seq.map (fun(ix,msg)->{ix=ix;msg=msg}) |> Seq.toList
    let lin (ixLis:int list,linLis:string list)(chkLinF:string->string option):IMsg list = 
        let erOptLis = linLis |> lisMap chkLinF
        x ixLis erOptLis
    let bk(ixLis:int list,linLis:string list)(chkBkF:string list->string option list):IMsg list =
        let erOptLis = linLis |> chkBkF
        x ixLis erOptLis

module Put =
    let x(r:IMsg list)(src:string[]):bool*string[] = 
        // if (List.isEmpty r) then false,src else true,put r src
        true,[||]
module ChkLy =
    let chkDup lis = Chk.bk lis ChkDupF.x
    let skip skipLinF ly : int list * string list =
        query {
            for (i,lin) in ayAddIdx ly do
            where (skipLinF lin)
            select (i,lin)
        } |> Seq.toList |> List.unzip

    /// use {skipLinF} to limit the {ly} become {ly'} to be checked
    /// use {chkLinF} & {chkBkF} & {chkTermOneDup} to check {ly'}
    /// return {isEr} and {tp}
    let x ly skipLinF chkLinF chkBkF chkTermOneDup = 
        let lis = skip skipLinF ly
        let r1 = chkLinF |> lisMap (Chk.lin lis) |> List.concat
        let r2 = chkBkF  |> lisMap (Chk.bk lis) |> List.concat
        let r3 = if chkTermOneDup then chkDup lis else []
        Put.x (r1@r2@r3) ly
open ChkLy
type ChkLy(ly:string[],
           chkLinF:(string->string option) list,
           chkBkF:(string list->string option list) list,
           ?chkTermOneDup':bool,
           ?skipLinF':string->bool) =
    let chkTermOneDup = optDft false chkTermOneDup'
    let skipLinF = optDft isRmkLin skipLinF'
    let isEr,tp'= ChkLy.x ly skipLinF chkLinF chkBkF chkTermOneDup
    member x.vdt = isEr,tp'
