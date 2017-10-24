#nowarn "40"
#nowarn "64"
namespace Lib.Core
type Doc = {doc:string; eg: (unit->string) list}
[<AutoOpen>]
module Itm =
    let itmF _ = false
    let itmT _ = true
    let zip a b = a,b
    let self itm = itm
    let itmIfMap p f itm = if(p itm) then Some(f itm) else None
    let itmIf c itm = if c then Some itm else None 
    let inLis lis itm = List.contains itm lis
    let inSeq  seq itm = Seq.contains  itm seq

[<AutoOpen>]
module Builder =
    type MayBeBuilder() = 
        member x.Return m = Some m
        member x.Zero() = None 
        member x.Combine(a:'a option,b) = if(a.IsNone) then None else b
        member x.Delay f = f()
    type AllBuilder()   = member x.Return m = m; member x.Zero() = true;  member x.Combine(a,b) = if(a) then true else b; member x.Delay(f) = f()
    type AnyBuilder()   = member x.Return m = m; member x.Zero() = false; member x.Combine(a,b) = if(a)then true else b; member x.Delay(f) = f()
    type OneOfBuilder() = class
        member x.Zero() = None
        member x.Return(m) = Some m
        member x.ReturnFrom = None
        member x.Combine(a,b) = match a with 
                                | None -> b 
                                | _ -> a
        member x.Delay(f) = f()
        end
    let oneOf = OneOfBuilder()
    let mayBe = MayBeBuilder()
    let all   = AllBuilder()
    let any   = AnyBuilder()

[<AutoOpen>]
module Shell =
    open Microsoft.VisualBasic
    type sty = AppWinStyle
    let shell cmd (sty:sty) = Interaction.Shell(cmd,sty,false,-1) |> ignore

[<AutoOpen>]
module Alias = 
    let gt = (>)
    let gte = (>)
    let lt = (<)
    let lte = (<=)
    let eq = (=)
    let ne = (<>)
    let ayApp = Array.append
    let aySrt = Array.sort  
    let ayZip  = Array.zip
    let ayFind = Array.find
    let ayMap  = Array.map
    let ayMapi = Array.mapi
    let ayMax  = Array.max
    let ayWh   = Array.filter
    let ayPick = Array.pick
    let ayAll  = Array.forall
    let ayAny  = Array.exists
    let ayChoose = Array.choose
    let ayToLis = Array.toList
    let ayFold = Array.fold
    let ayHas = Array.contains
    let listHas = List.contains
    let lisChoose = List.choose
    let lisMap = List.map
    let lisMapi = List.mapi
    let lisWh   = List.filter
    let lisAll  = List.forall
    let lisAny  = List.exists 
    let lisToAy = List.toArray
    let lisFold = List.fold
    let seqHas = List.contains
    let seqMap = Seq.map
    let setHas = Set.contains

[<AutoOpen>]
module P =
    let pNot p a = p a |> not
    let pVal v p = if p v then Some v else None
    let pAll pLis a = pLis |> List.forall (fun p -> p a)
    let pAny pLis a = pLis |> List.exists (fun p -> p a)
    let pAnd p1 p2 a = p1 a && p2 a
    let pOr p1 p2 a = p1 a || p2 a
    let pT = eq true
    let pF = eq false

[<AutoOpen>]
module DtaFun =
    open Alias
    let incr = (+)
    let decr n a = a - n
    /// if (c) then (f a) else (a)
    let ifMap c f a = if c then f a else a
    let always a = fun()->a
    let tee f a = f a; a

[<AutoOpen>]
module StrHas =
    open Alias
    let hasSs ss (s:string) = s.Contains ss
    let hasAnySs ssLis s    = ssLis |> lisAny (fun ss -> hasSs ss s)
    let hasLf               = hasSs "\n"
    let hasCr               = hasSs "\r"
    let hasCrOrLf           = pOr hasCr hasLf
    let hasSpc              = hasSs " "
    let hasDblSpc           = hasSs "  "

[<AutoOpen>]
module Zip =
    let zipOpt opt1 opt2 = match opt1,opt2 with Some a1,Some a2 -> Some(a1,a2) | _ -> None
    let ayZipFst2Ele(ay:'a[]) = ay.[0],ay.[1]
    /// convert a function-f which takes 2 parameter to take 1 parameter of tuple-of-2.
    let zip a b =a,b
    let zipF f (a,b) = f a b
    let zipNe(a,b)=a<>b
    let zipEq(a,b)=a=b
    let zipF2 f z = zip(fst z)(snd z|>f)
    let zipF1 f z = zip(fst z|>f)(snd z)

[<AutoOpen>]
module StrOp =
    open Microsoft.VisualBasic
     open StrHas
    let strEqIgnCas a b = System.String.Compare(a,b,true) = 0
    /// string eq ignorecase 
    let (=~) = strEqIgnCas
    let left  len s          = Strings.Left(s,len)
    let right len s          = Strings.Right(s,len)
    let len    (s:string)    = Strings.Len(s)
    let mid   fmIx len (s:string) = s.Substring(fmIx,len)
    let midFm fmIx     (s:string) = s.Substring(fmIx)
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
    let isBlankStr (s:string)   = s.Trim() = ""
    let isEmpStr                = pOr (System.String.IsNullOrEmpty) isBlankStr //' not(trim s) match "\S+") 
    let isSomStr s = isEmpStr s |> not
    let isSs  s ss = hasSs ss s
    let somstrAddPfx pfx somstr  = if(isSomStr somstr) then pfx+somstr else somstr
    let somstrAddSfx sfx somstr  = if(isSomStr somstr) then somstr+sfx else somstr

[<AutoOpen>]
module StrBrk = 
    open StrOp
    let brkAt pos sepLen s  = 
        let s1 = s |> left pos |> trim
        let s2 = s |> midFm (pos+sepLen) |> trim
        s1,s2
    let private er sep s  = failwith("no sep{" + sep + "} in s{" + s + "}")

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

[<AutoOpen>]
module StrTak =
    open StrBrk
    let takAft          sep = brk  sep >> snd
    let takAftOrAll     sep = brk1 sep >> snd
    let takAftOrNone    sep = brk2 sep >> snd
                        
    let takBef          sep = brk  sep >> fst
    let takBefOrAll     sep = brk1 sep >> fst
    let takBefOrNone    sep = brk2 sep >> fst

    let takRevAft       sep = brkRev  sep >> snd
    let takRevAftOrAll  sep = brk1Rev sep >> snd
    let takRevAftOrNone sep = brk2Rev sep >> snd

    let takRevBef       sep = brkRev  sep >> fst
    let takRevBefOrAll  sep = brk1Rev sep >> fst
    let takRevBefOrNone sep = brk2Rev sep >> fst

    let takAftSpc           = takAft " "
    let takAftSpcOrAll      = takAftOrAll " "
    let takAftSpcOrNone     = takAftOrNone " "
                         
    let takBefSpc           = takBef " "
    let takBefSpcOrAll      = takBefOrAll " "
    let takBefSpcOrNone     = takBefOrNone " "

    let takRevAftSpc        = takAft " "
    let takRevAftSpcOrAll   = takAftOrAll " "
    let takRevAftSpcOrNone  = takAftOrNone " "
    
    let takRevBefSpc        = takBef " "
    let takRevBefSpcOrAll   = takBefOrAll " "
    let takRevBefSpcOrNone  = takBefOrNone " "

[<AutoOpen>]
module Quote =
    open StrOp
    let brkQuote q =
        match len q with
        | 1 -> q,q
        | 2 -> (left 1 q),(right 1 q) 
        | _ ->  let p = pos "*" q
                if p=0 then failwith("q{" + q + "} must be len 1 or 2 or has *")
                (left p q),(midFm (p+2) q)
    let quote q s  = let q1,q2 = brkQuote q in q1 + s + q2
    let quoteBkt  = quote "()"
    let takBetQ quote s = 
        let q1,q2 = brkQuote quote
        let p1 = pos q1 s
        let p2 = posFm (p1+1) q2 s
        match p1=0 with | true -> "" | _ -> if p2>p1 then mid(p1+1)(p2-p1)s else ""

[<AutoOpen>]
module Convert =
    open Alias
    let oToStr(o:obj):string = sprintf "%A" o
    let toStr(a:'a):string = box a |> oToStr
    let seqToOlis seq   = [ for i in seq -> box i]
    let seqToOy seq     = [| for i in seq -> box i|]
    let seqToSlis seq   = [ for i in seq -> oToStr i]
    let ayToOy(ay:'a[]):obj[] = ayMap box ay
    let ayToSy(ay:'a[]):string[] = ay |> ayMap toStr
    let lisToSlis lis = [for i in lis -> oToStr i]
    let oyToSy(oy:obj[]):string[] = [| for i in oy -> toStr i|]

[<AutoOpen>]
module Jn =
    open Microsoft.VisualBasic
    open Convert
    open Alias

    let jnSy sep (sy:string[]) = Strings.Join(sy,sep)
    let jnSyCrLf               = jnSy "\r\n"
    let jnSyDblCrLf            = jnSy "\r\n\r\n"
    let jnSySpc                = jnSy " " 
    let jnAy sep   = oyToSy >> jnSy sep

    let jnSlis sep = lisToAy >> jnSy sep
    let jnSlisCrLf  = jnSlis "\r\n"
    let jnLis sep (lis) = lis |> lisToSlis |> jnSlis sep

[<AutoOpen>]
module Enm = 
    open Jn
    open Alias
    open System
    open Quote
    let private x<'a> ignoreCase s = Enum.Parse(typeof<'a>,s,ignoreCase) :?> 'a
    let private y<'a> ignoreCase s =         
        try 
            Some (x<'a> ignoreCase s)
        finally
            None
    let enmParse<'a> s  = x<'a> false s
    let enmParseI<'a> s = x<'a> true s
    let enmTryParse<'a> s  = y<'a> false s
    let enmTryParseI<'a> s = y<'a> true s
    let enm'str<'a>() = Enum.GetNames typeof<'a> |> aySrt |> jnSy " | " |> quote "[]"

[<AutoOpen>]
module Prt = 
    open Convert
    let prtS (s:string) = System.Console.Out.Write(s)
    let prtLis(lis:'a list) = lis |> lisToSlis |> List.iter prtS
    let prtNL() = System.Console.Out.WriteLine()
    let prtLisNL(lis:obj list) = prtLis lis; prtNL()

[<AutoOpen>]
module Vbl =
    type Vbl = Vbl of string
    open StrHas
    let isVbl = pAnd (pNot hasCr)(pNot hasLf) 
    let assertIsVbl s = if isVbl s|>not then failwith("s{"+s+"} is not a Vbl VBar-Line")

[<AutoOpen>]
module Opt =
    open Alias
    let some a = Some a
    let value(opt:'a option) = opt.Value
    let mkOpt opt itm = if opt then Some itm else None
    let isSome(a:'a option) = a.IsSome
    let isNone(a:'a option) = a.IsNone
    let dft dft opt = if isSome opt then value opt else dft
    /// return true if all elements of given {opy} isSome
    let opyAllSome ay = ay |> ayAll isSome
    let opyAnySome ay = ay |> ayAny isSome
    let opyAllNone ay = ay |> ayAll isNone
    let opyAnyNone ay = ay |> ayAny isNone
    let optDo f opt = if isSome opt then f (value opt)
    let optMap f opt = if isNone opt then None else Some (f (value opt))
    let optMapDft f dft opt = if isNone opt then dft else f (value opt)
    let optDft dft (a:'a option) = if isSome a then a.Value else dft
    /// return {'a option[]} from {opy:'a option[]} for those element has value.
    let opyWhSome(opy:'a option[]) = opy |> ayWh isSome
    /// return {'a[]} from {opy:'a option[]} for those element has value.
    let opyWhSomVal(opy:'a option[]):'a[] = opy|>opyWhSome|>ayMap value

[<AutoOpen>]
module AyWh =
    open Opt
    open Alias
    let ayWhByBoolAyForT boolAy ay = ayZip boolAy ay |> ayWh(fst>>pT)
    let ayWhByBoolAyForF boolAy ay = ayZip boolAy ay |> ayWh(fst>>pF)
    let ayWhByOnyForNone ony ay = ayZip ony ay |> ayWh(fst>>isNone) |> ayMap snd
    let ayWhByOnyForSome ony ay = ayZip ony ay |> ayWh(fst>>isSome) |> ayMap snd
    let ayWhDup  ay = ay |> Array.countBy(fun a->a) |> ayChoose (fun(k,c) -> if(c>1) then Some k else None)

[<AutoOpen>]
module Ay =
    open Zip
    open Convert
    open StrOp
    open Opt
    open Alias
    open System.Linq
    let empSy = Array.empty<string>
    let sz (ay:'a[]) = ay.Length 
    let ub ay        = (sz ay) - 1
    let isInAy ay a = ay |> ayAny(eq a)
    type aa ={aa:string; bb:string; cc:string}
    let a: System.Linq.IGrouping<string,int> = null
    let ayDupMsg ay=()
    let ayDup(ay:'a[]) = 
        query { 
            for i in ay do
            groupBy i into g
            where (g.Count()>1)
            select g.Key}
    let ayCut(fmIx,toIx)(ay:'a[]) = [|for i=fmIx to toIx do yield ay.[i]|]
    let ayFstEleOpt ay = if sz ay = 0 then None else Some(ay.[0])
    let ayFstEleDft dft = ayFstEleOpt >> optDft dft
    let ayLasEleOpt ay = let n = sz ay in if n=0 then None else Some(ay.[n-1])
    let ayLasEleDft dft = ayLasEleOpt >> optDft dft
    let ayAdd ay1 ay2     = Array.concat(seq{yield ay1;yield ay2})
    let ayAddIdx(ay:'a[]) = ayMapi zip ay
    let ayAdj f n ay = ayMapi (fun itm i-> if i=n then f itm else itm)
    let ayIns(i:'a)(ay:'a[]) = ([i]@(Array.toList ay)) |> Array.ofList
    let ayZipF f ay1 ay2 = ayZip ay1 ay2 |> ayMap (zipF f)
    let ayShift(ay:'a[]) = if(sz ay)=0 then None,ay else (Some ay.[0]),Array.skip 1 ay
    let ayIdx itm = Array.findIndex (eq itm)
    let ayIdxOpt itm = Array.tryFindIndex (eq itm)
    let ayIdxAy itmAy ay = itmAy |> ayMap (fun itm -> ayIdx itm ay)
    let ayIdxOptAy itmAy ay = itmAy |> ayMap (fun itm -> ayIdxOpt itm ay)
    let ayRepeat n dft = seq {for j=1 to n do yield  dft} |> Seq.toArray
    let ayRmvFstEle ay = Array.skip 1 ay
    let ayRmvLasEle ay = Array.take (sz ay - 1) ay
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

[<AutoOpen>]
module Function =
    open Microsoft.VisualBasic
    let msgOk msg = Interaction.MsgBox(msg,MsgBoxStyle.OkOnly) |> ignore
    let fSwapPrm (f:'a->'b->'c)  = fun (b:'b)(a:'a) -> f a b

[<AutoOpen>]
module FtRead =
    open System.IO
    let ftLy  = File.ReadAllLines 
    let ftStr = File.ReadAllText

[<AutoOpen>]
module OpnFil =
    open System.IO
    let opnAppFt = File.AppendText
    let opnFt    = File.OpenText
    let opnWrtFt ft = new System.IO.StreamWriter(File.OpenWrite ft)

[<AutoOpen>]
module PfxSfx =
    open StrOp
    open Alias
    let takFrontSpc (s:string) = s.ToCharArray() |> Array.findIndex (fun c -> c<>' ') |> spc
    let takPfx = len>>left
    let takSfx = len>>right
    let addPfxIfEmp pfx s = if isEmpStr s then pfx+s else ""
    let addSfxIfEmp sfx s = if isEmpStr s then s+sfx else ""
    let hasPfx pfx s = takPfx pfx s = pfx
    let hasSfx sfx s = takSfx sfx s = sfx
    let hasPfxI pfx s = takPfx pfx s =~ pfx
    let hasSfxI sfx s = takSfx sfx s =~ sfx
    let hasPfxLis pfxLis s = pfxLis |> lisAny (fun pfx -> hasPfx pfx s)
    let hasPfxLisI pfxLis s = pfxLis |> lisAny (fun pfx -> hasPfxI pfx s)
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
        else alignL (len frontSpc) pfx + trim(s)

[<AutoOpen>]
module Pth =
    open System.IO
    open PfxSfx
    open Jn
    let isPthExist pth = System.IO.Directory.Exists(pth)
    let pthCrt     pth = System.IO.Directory.CreateDirectory(pth) |> ignore
    let pthEns     pth = if(not(isPthExist pth)) then pthCrt pth
    let pthSep         = Path.DirectorySeparatorChar.ToString()
    let pthRmvSfx      = rmvSfx pthSep
    let jnPthSeqLis pthSegLis = (pthSegLis |> List.map pthRmvSfx |> jnSlis pthSep)  +  pthSep

[<AutoOpen>]
module Ffn =
    open Pth
    open StrOp
    open StrTak
    let ffnExt ffn = let p = posRev "."    ffn in if(p=0) then ""  else midFm p ffn
    let ffnFn  ffn = let p = posRev pthSep ffn in if(p=0) then ffn else midFm (p+1) ffn
    let ffnPth ffn = let p = posRev pthSep ffn in if(p=0) then ""  else left p ffn
    let ffnRmvExt ffn      = takRevBefOrAll "." ffn
    let ffnRplExt ext ffn  = (ffnRmvExt ffn) + ext

[<AutoOpen>]
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
[<AutoOpen>]
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
    open Convert
    open Alias
    let fmtQQ qqStr (olis:obj list) = olis |>lisFold (fun o v->(rplOnce "?" (oToStr v) o)) qqStr


[<AutoOpen>]
module StrSplit =
    open StrRpl
    open StrOp
    open Microsoft.VisualBasic
    let split sep s     = Strings.Split(s,sep)
    let splitCrLf = split "\r\n"
    let splitLf = split "\r\n"
    let splitSpc = split " "
    let splitLvs = rplDblSpc >> trim >> splitSpc
    let splitVbar = split "|"

[<AutoOpen>]
module Term =
    open Ay
    open AyWh
    open StrTak
    open StrOp
    open StrSplit
    let rmvFstTerm s = takBefSpcOrAll s |> ltrim
    let fstTerm = takBefSpcOrAll
    let sndTerm = takAftSpc >> fstTerm
    let shiftTerm s =(fstTerm s),(rmvFstTerm s)
    let brkNTerm'f (lis,s) _ = let t,s=shiftTerm s in if(isEmpStr t) then lis,s else lis@[t],s
    let brkNTerm atMost s    = seq {1..atMost} |> Seq.fold brkNTerm'f ([],s) |> fst |> List.toArray
    let brk3Term    = brkNTerm 3
    let brk2Term    = brkNTerm 2
    let isNterm n s = (brkNTerm (n+1) s |> sz) = n
    let is1term     = isNterm 1
    let is2term     = isNterm 2
    let is3Term     = isNterm 3
    let nTerm lin   = sz (splitLvs lin)

[<AutoOpen>]
module DupFstTerm =
    open Term
    open Alias
    open AyWh
    open Ay
    let lyFstTermDupAy ly = ly |> ayMap fstTerm |> ayWhDup
    let lyFstTermDupIdxAy ly = 
        let f = ly |> ayMap fstTerm 
        let dupAy = ayWhDup f
        let x(idx,fst) : int option = if fst |> isInAy dupAy then Some idx else None
        f |> ayAddIdx |> ayChoose x

[<AutoOpen>]
module Rmk =
    open Alias
    open StrTak
    open StrHas
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
    let syRmvRmkLin   = ayWh isNonRmkLin
    let syRmvEmpLin = ayWh (pNot isRmkLin)

[<AutoOpen>]
module Lis =
    open Alias
    open StrOp
    open PfxSfx
    let empSlis = List.empty<string>
    let olis(objLis:obj list) = objLis
    let isInLis(lis:'a list when 'a : equality) a = lis |> lisAny(eq a)
    let isInLisI(lis:'a list when 'a : equality) a = lis |> lisAny(strEqIgnCas a)
    let lisMinus lis1 lis2    = lis1|>lisWh(fun i->isInLis i lis2)
    let lisAddIdx lis = lis |> List.mapi (fun i itm -> i,itm)

[<AutoOpen>]
module LisWh =
    let lisWhDup lis =  lis |> List.countBy(fun a->a) |> lisChoose (fun(k,c) -> if(c>1) then Some k else None)

[<AutoOpen>]
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

[<AutoOpen>]
module Tmp =
    open System
    open Pth
    let tmpPth        = jnPthSeqLis[Environment.GetEnvironmentVariable "tmp";"fsharp"]
    let tmpNm    ()   = "T" + DateTime.Now.ToString("yyyy_MM_dd_HHmmss")
    let tmpFn    ext  = tmpNm() + ext
    let tmpFtFn  ()   = tmpFn ".txt" 
    let tmpFdr   fdr  = let p = jnPthSeqLis[tmpPth;fdr;tmpNm()] in pthEns p; p 
    let tmpFt    ()   = tmpPth + tmpFtFn()
    pthEns tmpPth

[<AutoOpen>]
module Wrt =
    open Convert
    open System.IO
    open Opt
    let wrtStr ft s = File.WriteAllText(ft,s)
    let wrtStrOpt ft s' = if(isSome s') then wrtStr ft (Opt.value s')
    let wrtSy ft sy = File.WriteAllLines(ft,sy)
    let wrtAy ft ay  = ay |> ayToSy |> wrtSy ft

[<AutoOpen>]
module Brw =
    open Wrt
    open Tmp
    open Convert
    open Jn
    open Shell
    open Pth
    let brwFt ft = shell(sprintf "code.cmd \"%s\" " ft)(sty.NormalFocus )
    let brwStr s = let t = tmpFt() in wrtStr t s; brwFt t
    let brwAy ay = ay|>ayToSy|>jnSyCrLf|>brwStr
    let brwOy oy = oy|>oyToSy|>jnSyCrLf|>brwStr
    let brwObj o = o|> oToStr|>brwStr
    let brwPth pth  = if(isPthExist pth) then shell(sprintf """explorer "%s" """ pth)  sty.NormalFocus
    let brwTmpPth ()  = brwPth tmpPth

[<AutoOpen>]
module FtSrt =
    open Alias
    open FtRead
    open Wrt
    let srtFt ft = ft |> ftLy |> aySrt |> wrtAy ft

[<AutoOpen>]
module MacroStr =
    open StrSplit
    open Quote
    open StrHas
    open StrTak
    open Alias
    let macroStrToSy s = 
        let sy = split "{" s
        let sy1 = sy |> ayWh (fun i-> hasSs "}" i)
        let sy2 = sy1 |> ayMap (fun i -> takBef "}" i)
        let q = quote "{}"
        sy2 |> ayMap q

[<AutoOpen>]
module Er =
    open Convert
    open StrOp
    open Jn
    open MacroStr
    open Tab
    open Ay
    open Alias
    open PfxSfx
    let erVarLines(nm:string)(o:obj)  = 
        linesTab nm ((len nm)+1) (toStr o)
    let erLines macroStr (olis:obj list) = 
        let oy = olis |> List.toArray
        let x(o,nm) = erVarLines nm o
        let s = 
            macroStrToSy macroStr 
            |> syAlignL 
            |> syAddPfx "    " 
            |> ayZip oy
            |> ayMap x
            |> jnSyCrLf
        macroStr + "\r\n" + s
    let er macroStr olis = failwith (erLines macroStr olis)

module OptSeq =
    open System.Linq
    let zip seq seq' = 
        query {
            for (seq,seq') in Seq.zip seq seq' do
            where (isSome seq')
            select (a,Opt.value seq')
        } 
    let lis lis lis' = 
        query {
            for (lis,lis') in List.zip lis lis' do
            where (isSome lis')
            select (lis, Opt.value lis')
        } |> Seq.toList
module OptLis =
    open System.Linq
    let zip lis lis' = 
        query {
            for (lis,lis') in List.zip lis lis' do
            where (isSome lis')
            select (lis,Opt.value lis')
        } |> Seq.toList

[<AutoOpen>]
module AddIx =
    let seqAddIx seq = seq |> Seq.mapi zip
    let ayAddIx ay = ay |> Array.mapi zip
    let lisAddIx lis = lis |> List.mapi zip

[<AutoOpen>]
module SeqUnzip =
    let seqUnZip(seq:('a*'b) seq) = (seq |>Seq.map (fun(a:'a,_)->a)),(seq |>Seq.map(fun(_,b:'b)->b))

[<AutoOpen>]
module Dup =
    open Convert
    open System.Linq
    let dupList lis = 
        query {
            for i in Queryable.AsQueryable(lis) do
            groupBy i into g
            where(g.Count()>1)
            select g.Key } |> Seq.toList
    let dupMsgLisByDup dup lis =
        let dupMsg itm = sprintf "dup(%s)" (toStr itm)
        let msgOpt = itmIfMap (inSeq dup) dupMsg
        let o = lis |> List.map msgOpt
        o
    let dupMsgLis lis = dupMsgLisByDup (dupList lis) lis
    let dupFstTermMsgLis lis = lis |> List.map fstTerm |> dupMsgLis
    let doc'msglisByDup =
        let doc = 
            """
msgOptOfDup'doc = {dup}      {seq}   :  {dupMsgOpt}
                : seq<'a> -> seq<'a> -> string option list
it is mapping of {seq} to some {dupMsgOpt} if {seq}-itm is found in {dup}
"""
        let eg0() =
            let dup = ["aa";"bb"]
            let lis = ["aa";"aa";"cc";"bb";"dd"]
            Er.erLines doc [dup;lis;dupMsgLisByDup dup lis]
        let eg = [eg0]
        {doc=doc;eg=eg}
    let doc'msgOpt =
        let doc = """
msgOpt = {linLis} : {msgOpt}
       : 'a list -> string option list
where the (output-list-item).Some is the er msg for dup item: in dup(?)
 """
        let eg0() = 
            let tp = """
xx bb cc
aa bb
cc dd
aa dd
cc dd
ddd
xxx
cc  dd"""
            let lis = splitCrLf tp |> ayToLis
            erLines doc [lis; dupMsgLis lis]
        let eg = [eg0]
        {doc=doc; eg=eg}
