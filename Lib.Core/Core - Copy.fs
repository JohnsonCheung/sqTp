#nowarn "40"
#nowarn "64"
namespace Lib
module Builder =
    type MayBeBuilder() = 
        member x.Return m = Some m
        member x.Zero() = None 
        member x.Combine(a:'a option,b) = if(a.IsNone) then None else b
        member x.Delay f = f()
    type AllBuilder()   = member x.Return m = m; member x.Zero() = true;  member x.Combine(a,b) = if(a) then true else b; member x.Delay(f) = f()
    type AnyBuilder()   = member x.Return m = m; member x.Zero() = false; member x.Combine(a,b) = if(a)then true else b; member x.Delay(f) = f()
    type OneOf() = class
        member x.Zero() = None
        member x.Return(m) = Some m
        member x.ReturnFrom = None
        member x.Combine(a,b) = match a with 
                                | None -> b 
                                | _ -> a
        member x.Delay(f) = f()
        end
    let oneOf = OneOf()
    let mayBe = new MayBeBuilder()
    let all   = new AllBuilder()
    let any   = new AnyBuilder()
module Itm =
    let itmT a = a = true
    let itmF a = a = false
    let itmEq(a:'a)(itm) = a = itm
    let itmSelf itm = itm
[<AutoOpen>]
module Fail =
    let fail s = failwith s |> ignore
module Shell =
    open Microsoft.VisualBasic
    type sty = AppWinStyle
    let shell cmd (sty:sty) = Interaction.Shell(cmd,sty,false,-1) |> ignore
[<AutoOpen>]
module Alias = 
    let ayZip  = Array.zip
    let ayFind = Array.find
    let ayMap  = Array.map
    let ayMapi = Array.mapi
    let ayMax  = Array.max
    let ayWh   = Array.filter
    let ayPick = Array.pick
    let ayAll  = Array.forall
    let ayAny  = Array.exists
    let ayFold = Array.fold
    let lisWh   = List.filter
    let lisAll  = List.forall
    let lisAny  = List.exists 
    let lisToAy = List.toArray
    let lisFold = List.fold
module Predict =
    let pAll pLis a = pLis |> lisAll (fun p -> p a)
    let pAny pLis a = pLis |> lisAny (fun p -> p a)
    let pAnd p1 p2 a = p1 a && p2 a
    let pNot(p:'a->bool)(a:'a):bool = p a |> not
    let pOr(p1:'a->bool)(p2:'a->bool)(a:'a):bool = (p1 a) || (p2 a)
module StrHas =
    open Predict
    let hasSs ss (s:string) = s.Contains ss
    let hasAnySs ssLis s    = ssLis |> lisAny (fun ss -> hasSs ss s)
    let hasLf               = hasSs "\n"
    let hasCr               = hasSs "\r"
    let hasCrOfLf           = pOr hasCr hasLf
    let hasSpc              = hasSs " "
    let hasDblSpc           = hasSs "  "
module Zip =
    let zipOpt opt1 opt2 = match opt1,opt2 with Some a1,Some a2 -> Some(a1,a2) | _ -> None
    let ayZipFst2Ele(ay:'a[]) = ay.[0],ay.[1]
    /// convert a function-f which takes 2 parameter to take 1 parameter of tuple-of-2.
    let fZip(f:'a->'b->'c):('a*'b->'c) = fun(a,b) -> f a b
    let zip a b =a,b
    let zipF f (a,b) = f a b
    let zipNe(a,b)=a<>b
    let zipEq(a,b)=a=b
    let zipF2(f:'b->'c)(z:'a*'b) = zip(fst z)(snd z|>f)
    let zipF1(f:'a->'c)(z:'a*'b) = zip(fst z|>f)(snd z)
module StrOp =
    open Microsoft.VisualBasic
    let left  len s          = Strings.Left(s,len)
    let right len s          = Strings.Right(s,len)
    let len   (s:string)     = Strings.Len(s)
    let mid   fm len s       = Strings.Mid(s,fm,len)
    let midFm fm     s       = Strings.Mid(s,fm)
    let ltrim                = Strings.LTrim
    let rtrim                = Strings.RTrim
    let trim                 = Strings.Trim
    let pos    (ss:string)(s:string) = s.IndexOf(ss)
    let posRev (ss:string)(s:string) = s.LastIndexOf(ss)
    let posFm  fm ss s       = Strings.InStr(fm,s,ss,CompareMethod.Binary)
    let spc    nSpc          = Strings.Space nSpc    
    let fstChr = left 1
    let lasChr = right 1
    let alignL w s = let l = len s in if w >= l then s + spc (w - l) else (left(w-2) s) + ".."
    open Predict
    open StrHas
    let isBlankStr (s:string)   = s.Trim() = ""
    let isEmpStr                = pOr (System.String.IsNullOrEmpty) isBlankStr //' not(trim s) match "\S+") 
    let isSomStr s = isEmpStr s |> not
    let isSs  s ss = hasSs ss s
    let somstrAddPfx pfx somstr  = if(isSomStr somstr) then pfx+somstr else somstr
    let somstrAddSfx sfx somstr  = if(isSomStr somstr) then somstr+sfx else somstr
module StrBrk = 
    open StrOp
    let brkAt pos sepLen s  = 
        let s1 = s |> left pos |> trim
        let s2 = s |> midFm (pos+sepLen) |> trim
        s1,s2
    let private er sep s  = fail("no sep{" + sep + "} in s{" + s + "}")

    let b1 fPos sep s = 
        let p = fPos sep s in 
        if(p = -1) then er sep s
        brkAt p (len sep) s
    let brk     = b1 pos    
    let brkRev  = b1 posRev 

    let private b2 fPos f sep s = let p=fPos sep s in if(p= -1) then (f s) else brkAt p (len sep) s
    let private m1 s = (trim s,"")
    let private m2 s = ("",trim s)
    let brk1    = b2 pos    m1
    let brk1Rev = b2 posRev m1
    let brk2    = b2 pos    m2
    let brk2Rev = b2 posRev m2
    
    let brk1Spc = brk1 " "
    let brk2Spc = brk2 " "
    let brkSpc  = brk  " "
module StrTak =
    open StrBrk
    open StrOp
    let takAft sep       = brk sep >> snd
    let takAftOrNone sep = brk1 sep >> snd
    let takAftSpc        = takAft " "
    let takBef      sep  = brk sep >> fst
    let takBefOrAll sep  = brk1 sep >> fst
    let takBefSpcOrAll   = takBefOrAll " " 
module Quote =
    open StrOp
    let brkQuote q =
        match len q with
        | 1 -> q,q
        | 2 -> (left 1 q),(right 1 q) 
        | _ ->  let p = pos "*" q
                if p=0 then 
                    let m = "q{" + q + "} must be len 1 or 2 or has *"
                    fail m
                (left p q),(midFm (p+2) q)
    let quote q s  = let q1,q2 = brkQuote q in q1 + s + q2
    let takBetQ quote s = 
        let q1,q2 = brkQuote quote
        let p1 = pos q1 s
        let p2 = posFm (p1+1) q2 s
        match p1=0 with | true -> "" | _ -> if p2>p1 then mid(p1+1)(p2-p1)s else ""
module ConvertTo =
    let oToStr(o:obj):string = sprintf "%A" o
    let toStr(a:'a):string = box a |> oToStr
    let seqToOlis seq   = [ for i in seq -> box i]
    let seqToOy seq     = [| for i in seq -> box i|]
    let seqToSlis seq   = [ for i in seq -> oToStr i]
    let ayToOy(ay:'a[]):obj[] = ayMap box ay
    let ayToSy(ay:'a[]):string[] = ay |> ayMap toStr
    let lisToSlis lis = [for i in lis -> oToStr i]
    let oyToSy(oy:obj[]):string[] = [| for i in oy -> toStr i|]
module Jn =
    open Microsoft.VisualBasic
    open ConvertTo
    let jnSy sep (sy:string[]) = Strings.Join(sy,sep)
    let jnSyCrLf               = jnSy "\r\n"
    let jnSyDblCrLf            = jnSy "\r\n\r\n"
    let jnSySpc                = jnSy " " 
    let jnAy sep   = oyToSy >> jnSy sep
    let jnSlis sep = lisToAy >> jnSy sep
    let jnLis sep (lis) = lis |> lisToSlis |> jnSlis sep
module Prt = 
    open ConvertTo
    let prtS (s:string) = System.Console.Out.Write(s)
    let prtLis(lis:'a list) = lis |> lisToSlis |> List.iter prtS
    let prtNL() = System.Console.Out.WriteLine()
    let prtLisNL(lis:obj list) = prtLis lis; prtNL()
module Vbl =
    type Vbl = Vbl of string
    let isVbl s = true 
    let assertIsVbl s = if(not(isVbl s)) then fail("s{"+s+"} is not a Vbl VBar-Line")
module Opt =
    let mkOpt opt itm = if opt then Some itm else None
    let isSome(a:'a option) = a.IsSome
    let isNone(a:'a option) = a.IsNone
    /// return true if all elements of given {opy} isSome
    let opyAllSome ay = ay |> ayAll isSome
    let opyAnySome ay = ay |> ayAny isSome
    let opyAllNone ay = ay |> ayAll isNone
    let opyAnyNone ay = ay |> ayAny isNone
    let optApply(f:'a->'b)(opt:'a option) = if opt.IsNone then None else Some(f opt.Value)
    let optVal(a:'a option) = a.Value
    let optDft dft (a:'a option) = if isSome a then a.Value else dft
    /// return {'a option[]} from {opy:'a option[]} for those element has value.
    let opyWhSome(opy:'a option[]) = opy |> ayWh isSome
    /// return {'a[]} from {opy:'a option[]} for those element has value.
    let opyWhSomVal(opy:'a option[]):'a[] = opy|>opyWhSome|>ayMap optVal
module AyWh =
    open Itm
    open Option
    let ayWhByBoolAyForT boolAy ay = ayZip boolAy ay |> ayWh (fst>>itmT)
    let ayWhByBoolAyForF boolAy ay = ayZip boolAy ay |> ayWh (fst>>itmT)
    let ayWhByOnyForNone ony ay = ayZip ony ay |> ayWh (fst>>isNone) |> ayMap snd
    let ayWhByOnyForSome ony ay = ayZip ony ay |> ayWh (fst>>isSome) |> ayMap snd
    let ayWhDup  ay = ay |> Array.countBy(fun a->a) |> Array.choose (fun(k,c) -> if(c>1) then Some k else None)
module Bool =
    open Itm
    let boolayAnyTrue = ayAny itmT
    let boollisAnyTrue = lisAny itmT
module Ay =
    open Zip
    open Itm
    open ConvertTo
    open StrOp
    open Opt
    let empSy   = Array.empty<string>
    let sz (ay:'a[]) = ay.Length 
    let ub ay        = (sz ay) - 1
    let isInAy ay a = ay |> ayAny(itmEq a)
    let ayAdd ay1 ay2     = Array.concat(seq{yield ay1;yield ay2})
    let ayAddIdx(ay:'a[]) = ayMapi zip ay
    let ayAdj f n ay = ayMapi (fun itm i-> if i=n then f itm else itm)
    let ayIns(i:'a)(ay:'a[]) = ([i]@(Array.toList ay)) |> Array.ofList
    let ayZipF f ay1 ay2 = ayZip ay1 ay2 |> ayMap (zipF f)
    let ayShift(ay:'a[]) = if(sz ay)=0 then None,ay else (Some ay.[0]),Array.skip 1 ay
    let ayRepeat n dft = seq {for j=1 to n do yield  dft} |> Seq.toArray
    let ayRz n dft ay = 
        let s = sz ay
        if n = s then ay
        else 
            match n > s with
            | true -> ayAdd ay (ayRepeat (n-s) dft)
            | false -> Array.take (s-n) ay
    let syShift(sy:string[]) = let a0,sy1 = ayShift sy in optDft "" a0, sy1
    let syWdt sy = sy |> ayMap len |> ayMax 
    let syAlignL'w w sy = sy |> ayMap (alignL w)
    let syAlignL sy = sy |> syAlignL'w (syWdt sy)
    let syRTrim = ayMap rtrim
    let syLTrim = ayMap ltrim
    let syTrim  = ayMap trim
module Function =
    let fSwapPrm (f:'a->'b->'c)  = fun (b:'b)(a:'a) -> f a b
module Env =
    let env nm = System.Environment.GetEnvironmentVariable nm
module FtRead =
    open System.IO
    let ftLy            = File.ReadAllLines 
    let ftStr           = File.ReadAllText
module OpnFil =
    open System.IO
    let opnAppFt    = File.AppendText
    let opnFt       = File.OpenText
    let opnWrtFt ft   = new System.IO.StreamWriter(File.OpenWrite ft)
module PfxSfx =
    open StrOp
    let takFrontSpc (s:string) = s.ToCharArray() |> Array.findIndex (fun c -> c<>' ') |> spc
    let takPfx = len>>left
    let takSfx = len>>right
    let addPfxIfEmp pfx s     = if isEmpStr s then pfx+s else ""
    let addSfxIfEmp sfx s     = if isEmpStr s then s+sfx else ""
    let hasPfx pfx s = takPfx pfx s = pfx
    let hasSfx sfx s = takSfx sfx s = sfx
    let addPfx pfx (s:string) = pfx + s
    let addSfx sfx (s:string) = s + sfx
    let rmvPfx pfx s = if hasPfx pfx s then midFm(len pfx) s else s
    let rmvSfx sfx s = if hasSfx sfx s then left(len sfx) s else s
    let syWhNotPfx pfx = ayWh <| hasPfx pfx
    let syAddPfx  pfx = addPfx pfx |> ayMap
    let syAddSfx  sfx = addSfx sfx |> ayMap
    /// if s has enough front space to allow pfx to be replaced, just replace the s-front-space by {pfx}
    /// else replace all s-front-space by {pfx} and keep 1 space left
    let rplPfx pfx s   =
        let frontSpc = takFrontSpc s
        if (len pfx) > (len frontSpc) 
        then pfx + " " + ltrim(s)
        else alignL ((len frontSpc) - (len pfx)) pfx + trim(s)
module Pth =
    open System.IO
    open PfxSfx
    open Jn
    let isPthExist pth = System.IO.Directory.Exists(pth)
    let crtPth    pth  = System.IO.Directory.CreateDirectory(pth) |> ignore
    let ensPth    pth  = if(not(isPthExist pth)) then crtPth pth
    let pthSep         = Path.DirectorySeparatorChar.ToString() 
    let rmvPthSfx      = rmvSfx pthSep
    let pthSegLisJn pthSegLis = (pthSegLis |> List.map rmvPthSfx |> jnSlis pthSep)  +  pthSep
module Ffn =
    open Pth
    open StrOp
    let ffnExt ffn = let p = posRev "."    ffn in if(p=0) then ""  else midFm p ffn
    let ffnFn  ffn = let p = posRev pthSep ffn in if(p=0) then ffn else midFm (p+1) ffn
    let ffnPth ffn = let p = posRev pthSep ffn in if(p=0) then ""  else left p ffn
module Dic =
    open StrBrk
    type Sdic = Map<string,string>
    let empSdic = Map.empty<string,string>
    let dicVopt         k    (dic:Map<'k,'v>) = if dic.ContainsKey(k) then Some(dic.Item k) else None
    let dicAddKV        (k,v)(dic:Map<'k,'v>) = dic.Add(k,v)
    let dicAddKVSkipDupK(k,v)(dic:Map<'k,'v>) = if dic.ContainsKey(k) |> not then dic.Add(k,v) else dic
    let private f1 (d:Sdic) lin = dicAddKVSkipDupK(brk1Spc lin) d
    let private f2 (d:Sdic) lin = dicAddKV        (brk1Spc lin) d
    let private s f ly = ly |> Array.fold f empSdic
    let sdicByLySkipDup = s f1
    let sdicByLy        = s f2
module StrRpl =
    open Microsoft.VisualBasic
    open StrTak
    open StrOp
    open StrHas
    let rpl ss by s = Strings.Replace(s,ss,by)
    let rplOnce ss by s = Strings.Replace(s,ss,by,Count=1)
    let rplDblSpc s = let rec r s = if (hasDblSpc s) then r (rpl "  " " " s) else s in r s
    let rplVbar     = rpl "|" "\r\n"
[<AutoOpen>]
module Fmt =
    open StrRpl
    open ConvertTo
    let fmtQQ qqStr (olis:obj list) = olis |>lisFold (fun o v->(rplOnce "?" (oToStr v) o)) qqStr
module StrSplit =
    open StrRpl
    open StrOp
    open Microsoft.VisualBasic
    let split sep s     = Strings.Split(s,sep)
    let splitCrLf lines = split "\r\n" lines
    let splitSpc = split " "
    let splitLvs s = rplDblSpc s |> trim |> splitSpc
    let splitVbar lines = split "|" lines
module Term =
    open Ay
    open StrTak
    open StrOp
    open StrSplit
    let rmvFstTerm s = takBefSpcOrAll s |> ltrim
    let fstTerm s = takBefSpcOrAll s
    let sndTerm   = takAftSpc >> fstTerm
    let shiftTerm s =(fstTerm s),(rmvFstTerm s)
    let brkNTerm'f (lis,s) _ = let t,s=shiftTerm s in if(isEmpStr t) then lis,s else lis@[t],s
    let brkNTerm  atMost s   = seq {1..atMost} |> Seq.fold brkNTerm'f ([],s) |> fst |> List.toArray
    let is1term    s = (brkNTerm 2 s |> sz) = 1
    let is3Term    s = (brkNTerm 4 s |> sz) = 3
    let nTerm lin = sz (splitLvs lin)
module Rmk =
    open StrTak
    open StrHas
    open Predict
    open StrOp
    let has2Dash   = hasSs "--"
    let has3Dash   = hasSs "---"
    let isRmkLin    = pOr isEmpStr has2Dash
    let isNonRmkLin = pNot isRmkLin
    let rmvRmk rmk s = takBefOrAll rmk s |> rtrim
    let rmv3DashRmk = rmvRmk "---"
    let rmv2DashRmk = rmvRmk "--"
    let syRmv3DashRmk = ayMap rmv3DashRmk
    let syRmv2DashRmk = ayMap rmv2DashRmk
    let syRmvRmkLin          = ayWh isNonRmkLin
    let syRmvEmpLin = ayWh (pNot isRmkLin)
[<AutoOpen>]
module Lis =
    open Itm
    let empSlis = List.empty<string>
    let olis(objLis:obj list) = objLis
    let isInLis(lis:'a list when 'a : equality) a = lis |> lisAny(itmEq a)
    let lisMinus lis1 lis2    = lis1|>lisWh(fun i->isInLis i lis2)
module Tab =
    open StrOp
    open Jn
    open PfxSfx
    open StrSplit
    open Ay
    let syTab pfx nSpc sy = 
        let sy = sy |> syAddPfx (spc nSpc)
        if(sz sy > 0) then sy.[0] <- rplPfx pfx (sy.[0])
        sy
    let linesTab pfx nSpc = splitCrLf >> syTab pfx nSpc >> jnSyCrLf
module Tmp =
    open System
    open Env
    open Pth
    let tmpPth        = pthSegLisJn[env "tmp";"fsharp"]
    let tmpNm    ()   = "T" + DateTime.Now.ToString("yyyy_MM_dd_HHmmss")
    let tmpFn    ext  = tmpNm() + ext
    let tmpFtFn  ()   = tmpFn ".txt" 
    let tmpFdr   fdr  = let p = pthSegLisJn[tmpPth;fdr;tmpNm()] in ensPth p; p 
    let tmpFt    ()   = tmpPth + tmpFtFn()
    ensPth tmpPth
module Wrt =
    open ConvertTo
    open System.IO
    open Opt
    let wrtStr ft s = File.WriteAllText(ft,s)
    let wrtStrOpt ft s' = if(isSome s') then wrtStr ft (optVal s')
    let wrtSy ft sy = File.WriteAllLines(ft,sy)
    let wrtAy ft ay  = ay |> ayToSy |> wrtSy ft
[<AutoOpen>]
module Brw =
    open Wrt
    open Tmp
    open ConvertTo
    open Jn
    open Shell
    open Pth
    let brwFt ft = shell(sprintf """notepad.exe "%s" """ ft)(sty.NormalFocus )
    let brwStr s = let t = tmpFt() in wrtStr t s; brwFt t
    let brwAy ay = ay|>ayToSy|>jnSyCrLf|>brwStr
    let brwOy oy = oy|>oyToSy|>jnSyCrLf|>brwStr
    let brwObj o = o|> oToStr|>brwStr
    let brwPth pth  = if(isPthExist pth) then shell(sprintf """explorer "%s" """ pth)  sty.NormalFocus
    let brwTmpPth ()  = brwPth tmpPth
module FtSrt =
    open Jn
    open FtRead
    open Wrt
    let srtFt ft = ft |> ftLy |> Array.sort |> jnSyCrLf |> wrtStr ft
module MacroStr =
    open StrSplit
    open Quote
    open StrHas
    open StrTak
    let macroStrToSy s = 
        let sy = split "{" s
        let sy1 = sy |> ayWh (fun i-> hasSs "}" i)
        let sy2 = sy1 |> ayMap (fun i -> takBef "}" i)
        let q = quote "{}"
        sy2 |> ayMap q
[<AutoOpen>]
module Er =
    open ConvertTo
    open StrOp
    open Jn
    open MacroStr
    open Tab
    open Ay
    let erVarLines(nm:string)(o:obj)  = 
        let lines = oToStr o
        let lines = linesTab nm (len nm) lines
        fmtQQ "\t?||?" [nm;lines]
    let erLines macroStr (olis:obj list) = 
        let oy = olis |> List.toArray
        let x(o,nm) = erVarLines nm o
        macroStrToSy macroStr |> syAlignL |> ayZip oy |> ayMap x |> jnSyCrLf
    let er macroStr olis = failwith (erLines macroStr olis) |> ignore
module Blk =
    open Ay
    open Jn
    open StrSplit
    type Blk = {fstLin:string;ly:string[]}
    type Blks = {sep:string;blkAy:Blk[]}
    let blkToLy(b:Blk) = ayIns(b.fstLin)(b.ly)
    let blkToLines(b:Blk) = jnSyCrLf(blkToLy b)
    let mkBlk i s:Blk =
        let ly = splitCrLf s
        let fstLin,ly = if i=0 then "",ly else syShift ly
        {fstLin=fstLin;ly=ly}
    let mkBlks(tp:string)(sep:string):Blks =
        let sep1 ="\r\n" + sep
        let sy = split sep1 tp
        let blkAy:Blk[] = sy |> ayMapi mkBlk
        {sep=sep;blkAy=blkAy}
    let blksToTp(blks:Blks) = ayMap blkToLines >> jnSy(blks.sep + "\r\n")
