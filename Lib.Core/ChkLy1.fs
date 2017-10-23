#nowarn "40" 
#nowarn "64" 
namespace Lib.ChkLy1
open Lib.Core
type ILin = { ix: int; lin: string }
type IMsg = { ix: int; msg: string }
module internal Chk =
    let x ixLis erOptLis = 
        if List.length ixLis <> List.length erOptLis then er "{ixLis} and {erOptLis} have diff length" [ixLis;erOptLis]
        query {
            for (ix,erOpt) in List.zip ixLis erOptLis do
            where (isSome erOpt)
            select (ix,erOpt.Value)
        } |> Seq.map (fun(ix,msg)->{ix=ix;msg=msg}) |> Seq.toList
    let lin (ixLis:int list,linLis:string list)(chkLinF:string->string option):IMsg list = 
        let erOptLis = linLis |> lisMap chkLinF
        x ixLis erOptLis
    let bk(ixLis:int list,linLis:string list)(chkBkF:string list->string option list):IMsg list =
        let erOptLis = chkBkF linLis
        x ixLis erOptLis
module internal ChkDup1 = 
    let x dup fstTermLis =                      // for each ix of value f in fstTermAy,
                                                // if f is in dup, 
                                                // return string option list indicating which fstTermLis item has dup(f)
        let f fstTerm = if (fstTerm |> isInLis dup) then Some(sprintf "dup(%s)" fstTerm) else None
        let o = fstTermLis |> lisMap f
        o
    let doc,eg =
        let doc = """{dupLis} {fstTermLis} -> {string option list}
for each fstTerm, if found in dupLis return Some "Dup(?)" else None
"""
        let eg() =
            let dup = ["aa";"bb"]
            let fstTerm = ["aa";"aa";"cc";"bb";"dd"]
            erLines doc [dup;fstTerm;x dup fstTerm]
        doc,eg
module internal ChkDupXX =
    let f(linLis:string list):string option list =
        let fstTermLis = linLis |> lisMap fstTerm
        let dup = lisWhDup fstTermLis              // duplicated fstTerm items
        let o = ChkDup1.x dup fstTermLis           // find its ly-index
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
        erLines doc [linLis; f linLis]
module internal H =
    let mge_into_lines(lin:string,msgLis:string list):string =
        let s = (len lin) + 1 |> spc
        let s0 = lin + " "
        msgLis |> lisMapi (fun i msg -> if i=0 then s0 + msg else s + msg) |> lisToAy |> jnSyCrLf
    let fnd_msgLis(imsgLis:IMsg list)(ix:int) : string list= 
        let msg {ix=_; msg=msg'} = msg'
        let eqIx {ix=ix'; msg=_} = ix=ix'
        imsgLis |> lisWh eqIx |> lisMap msg
type ChkLy(ly:string[],
           chkLinF:(string->string option) list,
           chkBkF:(string list->string option list) list,
           ?chkTermOneDup':bool,
           ?skipLinF':string->bool) =
    let ly' = ly |> syRmv3DashRmk |> ayMap rtrim            // ly'  cleaned ly  (no 3dash & rtrim)

    let chkTermOneDup = optDft false chkTermOneDup'
    let skipLinF = optDft isRmkLin skipLinF'
    let skipped =                                           // skipped: ixLis,LinLis   (no remark lines)
        query {
            for (i,lin) in ayAddIdx ly' do
            where (skipLinF lin)
            select (i,lin)
        } |> Seq.toList |> List.unzip
    member x.tpOld:string = ly |> jnSyCrLf
    member x.tpNew:string=
        let imsgLis = x.imsgLis
        if List.isEmpty imsgLis then (ly' |> jnSyCrLf) else
            let tp = ly |> syAlignL|> ayMapi (fun i lin -> (lin, H.fnd_msgLis imsgLis i)) |> ayMap H.mge_into_lines |> jnSyCrLf
            tp
    member x.tpOpt = 
        let o = x.tpOld
        let n = x.tpNew
        if o = n then None else Some n
    member x.isEr = x.imsgLis |> List.isEmpty |> not
    member x.chk = x.isEr, x.tpNew
    member x.imsgLis = x.imsgLin @ x.imsgBk @ x.imsgTermOneDup
    member x.imsgLin = chkLinF |> List.map (Chk.lin skipped) |> List.concat
    member x.imsgBk  = chkBkF  |> List.map (Chk.bk  skipped) |> List.concat
    member __.imsgTermOneDup = if not chkTermOneDup then [] else  Chk.bk skipped ChkDup.f