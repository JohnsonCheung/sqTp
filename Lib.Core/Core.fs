#nowarn "40"
#nowarn "64"
namespace Lib.Core
open System.Linq
open Microsoft.VisualBasic
open System.IO
open System
type key = string
type ffn = string
type ext = string
type fn = string
type msg = string
type msgs = msg list
type msgOpt = msg option
type lyMsgs = msgs[]
type msgOptAy = msgOpt[]
type oneEleAy<'a> = 'a[]
type oneEleLis<'a> = 'a list
type dupSeq<'a> = 'a seq
type dic<'a> = Map<string,'a>
type wdt = int
type pos = int
type len = int
type sep = string
type s = string
type s1 = string
type s2 = string
type term = string
type termLvs = string
type sub = string
type fstTerm = string
type ix = int
type jx = int
type pfx = string
type nSpc = int
type isEr = bool
type lin = string
type pth = string
type ft = string
type nm = string
type lines = string
type ly = lin[]
type dupFstTermLy = ly
type sy = string[]
type oy = obj[]
type olis = obj list
type slis = string list
type ss = string seq
type pred<'a> = 'a->bool
type macroStr = string
type er=macroStr*olis
type vbl = string
type ny = string[]
type cnt = int
type bdic = Map<string,bool>
type sdic = Map<string,string>
type kstr = Collections.Generic.KeyValuePair<string,string>
type doc = {nm:string; nmSpc: string; sgn:string; doc:string; eg: (unit->string) list}
type fmTo = ix*ix
type ixCnt = ix*cnt
type LyMsgs(lyMsgs:msgs[]) =
    member x.lyMsgs = lyMsgs
    new() = LyMsgs([||])
[<AutoOpen>]
module Core = 
    // emp
    let empSlis:slis = []

    // Int
    let nDig n = 
        if 0>n then failwith(sprintf "n-{%i} should be +ve" n) else 
            if n<10 then 1 else
                if n<100 then 2 else
                    if n<1000 then 3 else
                        if n<10000 then 4 else
                            5
    let runningSy n : sy=
        let fmt =   match nDig n with
                    | 1 -> sprintf "%01i"
                    | 2 -> sprintf "%02i"
                    | 3 -> sprintf "%03i"
                    | 4 -> sprintf "%04i"
                    | _ -> sprintf "%05i"
        [| for i in {0..n-1} do yield fmt i |]

    // Opt
    let optVal(opt:'a option) = opt.Value

    // Obj
    let isSs(o:obj) = match o with :? ss -> true | _ -> false
    let isSy(o:obj) = match o with :? sy -> true | _ -> false
    let isNull(o:obj) = match o with null -> true | _ -> false
    let tyCd o = Type.GetTypeCode(o.GetType())
    let tryTyCd o = if isNull o then None else Some(tyCd o)
    let nzF f o = if isNull o then false else f o
    let isAy(o:obj) = nzF(fun o->o.GetType().IsArray) o
    let isStr(o:obj) = tryTyCd o = Some(TypeCode.String)
    let isSeq(o:obj) = match o with | :? ('a seq) -> true | _ -> false

    // Turn : return a unit-functor
    let turnNone () = None
    let turnT() = true
    let turnF() = false
    let turnUnit() = ()

    // Itm: function on itm
    let itmT _ = true
    let itmF _ = false
    let itmSelf itm = itm
    let itmNone _ = None
    let itmMap f itm = f itm
    let itmDo(act:'a->unit)(itm:'a) = act itm
    let itmNothing _ = ()
    let zip a b = a,b
    let itmSome  p itm     = if(p itm) then Some itm else None
    let itmIf    p t f itm = if(p itm) then t() else f() 
    let itmIfMap p t f itm = if(p itm) then t itm else f itm
    let isInLis lis itm = List.contains itm lis
    let isInSeq seq itm = Seq.contains itm seq

    // Builder
    type MsgsBuilder()=
        member x.Yield m=false,[m]
        member x.Return(_)=true,[]
        member x.Combine(m,f)=
            match m with
            | false,aMsgs->
                let bRet,bMsgs = f()
                bRet,aMsgs@bMsgs
            | true,_->m
        member x.Delay f=fun()->f()
        member x.Run(f):msgs = f() |> snd
        member x.Zero()= false,[]
    let msgs = new MsgsBuilder()
    type YieldRetBuilder() =
        member x.Yield m=false,[m]
        member x.Return(_)=true,[]
        member x.Combine(m,f)=
            match m with
            | false,aLis->
                let bRet,bLis = f()
                bRet,aLis@bLis
            | true,_->m
        member x.Delay(f)=fun()->f()
        member x.Run(f) = f()|>snd
        member x.Zero() = []
    type MayBeBuilder() = 
        member x.Return m = Some m
        member x.Zero() = None 
        member x.Combine(a:'a option,b) = if(a.IsNone) then None else b
        member x.Delay f = f()
    type RetBuilder() =
        member x.Zero() = None
        member x.Return m = Some(m)
        member x.Combine(m,f) =
            match m with
            | None -> f()
            | _ ->m
        member x.Delay(f)=fun()->f()
        member x.Run(f)=f()|>optVal
    type AnyTrueBuilder() =
        member x.Return m = m
        member x.Zero() = false
        member x.Combine(a,b) = if(a)then true else b
        member x.Delay(f) = f()
    type LisOfBuilder() =
        member x.Zero() = None
        member x.Return m = m
        member x.Combine(a,b) = match a with None -> b | Some a -> b@[a]
    type OneOfBuilder() = 
        member x.Zero() = None
        member x.Return m = Some m
        member x.Combine(a,b) = match a with None -> b | _ -> a
        member x.Delay(f) = f()
    type ShortCutBuilder() = 
        member x.Zero() = None
        member x.Return m = Some m
        member x.ReturnFrom _ = Some None
        member x.Combine(a,b) = match a with None -> b | _ -> a
        member x.Delay(f) = f()
    let shortCut = ShortCutBuilder()
    let oneOf = OneOfBuilder()
    let ret = RetBuilder()
    let lisOf = LisOfBuilder()
    let mayBe = MayBeBuilder()
    let anyTrue = AnyTrueBuilder()

    // Shell
    type sty = AppWinStyle
    let shell cmd (sty:sty) = Interaction.Shell(cmd,sty,false,-1) |> ignore

    // Alias
    let gt = (>)
    let gte = (>)
    let lt = (<)
    let lte = (<=)
    let eq = (=)
    let ne = (<>)
    let ayApp = Array.append
    let aySrt = Array.sort  
    let ayZip  = Array.zip
    let ayZip3 = Array.zip3
    let ayUnzip  = Array.unzip
    let ayFind = Array.find
    let ayMap  = Array.map
    let ayIsEmpty = Array.isEmpty
    let ayTryLas = Array.tryLast
    let ayLas = Array.last
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
    let lisHas = List.contains
    let lisChoose = List.choose
    let lisMap = List.map
    let lisIsEmpty = List.isEmpty
    let lisMapi = List.mapi
    let lisWh   = List.filter
    let lisAll  = List.forall
    let lisAny  = List.exists 
    let lisToAy = List.toArray
    let lisFold = List.fold
    let lisDup = List.replicate
    let seqAll = Seq.forall
    let seqMax = Seq.max
    let seqHas = Seq.contains
    let seqMap = Seq.map
    let setHas = Set.contains
    let seqToAy = Seq.toArray
    let seqToLis = Seq.toList
    let seqZip = Seq.zip

    // Pred
    let pNot(p:'a->bool) a = p a |> not
    let pSomVal v (p:pred<'a>) = if p v then Some v else None
    let pAll pLis a = pLis |> List.forall (fun p -> p a)
    let pAny pLis a = pLis |> List.exists (fun p -> p a)
    let pAnd p1 p2 a = p1 a && p2 a
    let pOr(p1:pred<'a>)(p2:pred<'a>) a = p1 a || p2 a
    let (.|) = pOr
    let (.&) = pAnd
    let pT = eq true
    let pF = eq false

    // DtaFun
    let incr = (+)
    let decr n a = a - n

    /// if (c) then (f a) else (a)
    let ifMap c f a = if c then f a else a
    let always a = fun()->a
    let tee f a = f a; a

    // StrHas
    let hasSub(sub:sub)(s:s) = s.Contains sub
    let isSub  s sub = hasSub sub s
    let hasAnySub subLis s  = subLis |> lisAny(isSub s)
    let hasLf               = hasSub "\n"
    let hasCr               = hasSub "\r"
    let hasCrOrLf           = pOr hasCr hasLf
    let hasSpc              = hasSub " "
    let hasDblSpc           = hasSub "  "

    // Zip
    let zipOpt opt1 opt2 = match opt1,opt2 with Some a1,Some a2 -> Some(a1,a2) | _ -> None
    let ayZipFst2Ele(ay:'a[]) = ay.[0],ay.[1]
    /// convert a function-f which takes 2 parameter to take 1 parameter of tuple-of-2.
    let zipF f (a,b) = f a b
    let zipNe(a,b)=a<>b
    let zipEq(a,b)=a=b
    let zipF2 f z = zip(fst z)(snd z|>f)
    let zipF1 f z = zip(fst z|>f)(snd z)

    // StrOp
    let toLower(s:string)=s.ToLower()
    let toUpper(s:string)=s.ToUpper()
    let strEqIgnCas a b = System.String.Compare(a,b,true) = 0
    /// string eq ignorecase 
    let (=~) = strEqIgnCas
    let strDup n (s:string) = Strings.StrDup(n,s)
    let left  len s         = Strings.Left(s,len)
    let right len s         = Strings.Right(s,len)
    let len    (s:string)   = Strings.Len(s)
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
    let toBool s = if s="1" then true else let a,b = (System.Boolean.TryParse s) in a||b
    let lasChr = right 1
    let rmvFstChr = midFm 1
    let rmvLasChr s = left (len s - 1) s
    let alignL w s = let l = len s in if w >= l then s + spc (w - l) else (left(w-2) s) + ".."
    let isBlankStr (s:string)   = s.Trim() = ""
    let isEmpStr                = pOr (System.String.IsNullOrEmpty) isBlankStr //' not(trim s) match "\S+") 
    let isSomStr s = isEmpStr s |> not
    let somstrAddPfx pfx somstr  = if(isSomStr somstr) then pfx+somstr else somstr
    let somstrAddSfx sfx somstr  = if(isSomStr somstr) then somstr+sfx else somstr

    // StrBrk
    let brkAt(pos:pos)(sepLen:len)(s:s):(s1*s2)  = 
        let s1 = s |> left pos |> trim
        let s2 = s |> midFm (pos+sepLen) |> trim
        s1,s2
    let private er sep s  = failwith("no sep[" + sep + "] in s[" + s + "]")

    let private b1 fPos (sep:sep)(s:s) = 
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

    // StrTak
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

    // Quote
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

    // Convert
    let toOy(seq1:'a seq):oy = [| for i in seq1 do yield(box i)|]
    
    // Ss: string seq
    let ssSy(ss:ss) = if isSy(box ss) then ss:?>sy else ss |> seqToAy

    // Jn: join seq
    let jn(sep:sep)(ss:ss):lin = if Seq.isEmpty ss then "" else Strings.Join(ss|>ssSy,sep)
    let jnDbCrLf ss:lines = jn "\r\n\r\n" ss
    let jnCrLf   ss:lines = jn "\r\n" ss
    let jnSpc    ss:lin = jn " " ss
    let jnComma  ss:lin = jn ", " ss

    // Vbl
    let isVbl = pAnd (pNot hasCr)(pNot hasLf) 
    let assertIsVbl s = if isVbl s|>not then failwith("s{"+s+"} is not a Vbl VBar-Line")

    // Opt
    let mkOpt c itm = if c then Some itm else None
    let some a = Some a
    let isSome(a:'a option) = a.IsSome
    let isNone(a:'a option) = a.IsNone

    let optOneEleLis a:oneEleLis<'a> = if isSome a then [a.Value] else []
    let optOneELeAy  a:oneEleAy<'a> = if isSome a then [|a.Value|] else [||]

    /// do {act} if is some else doNothing
    let optDo     act a' = if isSome a' then act() else ()
    let optDoSelf act a' = if isSome a' then act a' else ()

    /// apply f to a.Value if Some
    let optMap f        a' = if isSome a' then a'|>optVal|>f|>some else None
    let optDftMap dft f a' = if isSome a' then a'|>optVal|>f else dft
    let optDft dft      a' = if isSome a' then optVal a' else dft
    let dft                = optDft
    
    /// return {'a option[]} from {opy:'a option[]} for those element has value.
    let opyWhSome opy = opy |> ayWh isSome

    /// return {'a[]} from {opy:'a option[]} for those element has value.
    let opyWhSomVal opy = opy|>opyWhSome|>ayMap optVal

    /// return true if all elements of given {opy} isSome
    let opyAllSome ay = ay |> ayAll isSome
    let opyAnySome ay = ay |> ayAny isSome
    let opyAllNone ay = ay |> ayAll isNone
    let opyAnyNone ay = ay |> ayAny isNone

    let private x nullStr (a:'a):string = 
        let o = box a
        if isNull o then "<null>" else o.ToString() 

    let toStr o = x "" o
    let toStrNull o = x "<null>" o
    let toSs(seq1:'a seq):ss = seq { for i in seq1 -> toStr i }
    let toSlis(seq1:'a seq):slis = [for i in seq1 -> toStr i]
    let toSy(seq1:'a seq):sy = [| for i in seq1 do yield(toStr i)|]

    // Prt
    let NL() = System.Console.Out.WriteLine()
    let prt o = System.Console.Out.Write(toStrNull o)
    let prtNL o = prt o; NL()
    let prtLis(lis:'a list) = lis |> toSlis |> List.iter prt
    let prtLisNL(lis:'a list) = prtLis lis; NL()
    
    // Ay
    let sz = Array.length
    let ayIsSamSz ay1 ay2 = sz ay1 = sz ay2
    let ayPush itm ay = Array.append ay [|itm|]

    // AyWh
    let ayWhOne cond ay = ay |> ayPick (fun(i)->if cond i then Some i else None)
    let ayWhByBoolAyForT boolAy ay = ayZip boolAy ay |> ayWh(fst>>pT)
    let ayWhByBoolAyForF boolAy ay = ayZip boolAy ay |> ayWh(fst>>pF)
    let ayWhByOnyForNone ony ay = ayZip ony ay |> ayWh(fst>>isNone) |> ayMap snd
    let ayWhByOnyForSome ony ay = ayZip ony ay |> ayWh(fst>>isSome) |> ayMap snd
    let ayWhDup  ay = ay |> Array.countBy(fun a->a) |> ayChoose (fun(k,c) -> if(c>1) then Some k else None)

[<AutoOpen>]
module Seq =
    let isAny = Seq.exists
    let isAll = Seq.forall
    let toAy = seqToAy
    let toLis = seqToLis
    let hasFstEle seq = seq |> Seq.tryHead |> isSome
    let fstEleOpt = Seq.tryHead
    let fstEleDft dft = fstEleOpt >> optDft dft
    let dmp seq = seq |> Seq.iter(fun o->prtNL o)
    let isAllEqTo(a:'a)(seq:'a seq) =
        if Seq.isEmpty seq then false else
            seqAll(eq a)(seq)
    let isAllEq(seq:'a seq) = 
        if Seq.isEmpty seq then true else
            isAllEqTo(seq.First())(seq) 
    let dupFmTo(seq:'a seq) =
        if Seq.isEmpty seq then None else
            let mutable las = None
            let p(ix,x) = 
                match las with
                | None -> las <- Some(ix,x,true); None
                | Some(ix',x',fstTime) -> 
                    match fstTime,x=x' with 
                    | true,true-> las <-Some(ix',x,false); None
                    | true,false-> las <-Some(ix,x,true); None
                    | _,true -> None
                    | _,false-> Some(ix',ix-1)
            seq |> Seq.mapi zip |> Seq.tryPick p
[<AutoOpen>]
module Ay =
    let aySs(ay:'a[]):ss=ay|>seqMap toStr
    let ayRplByFmTo by (fmTo:fmTo) ay =
        let (fmIx,toIx) = fmTo
        let p1 = Array.take fmIx ay
        let p2 = Array.skip(toIx+1) ay
        Array.concat[p1;by;p2]
    let empSy:sy = [||]
    let sz (ay:'a[]) = ay.Length 
    let ub ay        = (sz ay) - 1
    let isInAyI ay a = ay |> ayAny(strEqIgnCas a)
    let isInAy ay a = ay |> ayAny(eq a)
    let ayDupMsg ay=()
    let ayDup(ay:'a[]) = 
        query { 
            for i in ay do
            groupBy i into g
            where (g.Count()>1)
            select g.Key}
    let ayAddItm itm ay = Array.append ay [|itm|]
    let ayCut(fmIx,toIx)(ay:'a[]) = [|for i=fmIx to toIx do yield ay.[i]|]
    let ayLasEleDft dft = ayTryLas >> optDft dft
    let ayAdd ay1 ay2     = Array.concat(seq{yield ay1;yield ay2})
    let ayAddIdx(ay:'a[]) = ayMapi zip ay
    let ayAdj f n ay = ayMapi (fun itm i-> if i=n then f itm else itm)
    let ayIns(i:'a)(ay:'a[]) = ([i]@(Array.toList ay)) |> Array.ofList
    let ayInsBef(bef:int)(i:'a[])(ay:'a[]) =
        let lisBrkBef bef lis = List.take bef lis,List.skip bef lis
        let p1,p2=lisBrkBef bef (ayToLis ay)
        let lis = p1@(ayToLis i)@p2
        lis |> Array.ofList
    let ayZipF f ay1 ay2 = ayZip ay1 ay2 |> ayMap (zipF f)
//    let ayZipF f = ayZip >> (ayMap (zipF f))
    let ayShift(ay:'a[]) = if(sz ay)=0 then None,ay else (Some ay.[0]),Array.skip 1 ay
    let ayIdx itm = Array.findIndex (eq itm)
    let ayIdxOpt itm = Array.tryFindIndex (eq itm)
    let ayIdxAy itmAy ay = itmAy |> ayMap (fun itm -> ayIdx itm ay)
    let ayIdxOptAy itmAy ay = itmAy |> ayMap (fun itm -> ayIdxOpt itm ay)
    let ayRepeat n dft = seq {for j=1 to n do yield  dft} |> Seq.toArray
    let ayRmvFstEle ay = Array.skip 1 ay
    let ayRmvLasEle ay = Array.take (sz ay - 1) ay
    let ayRmvDup ay =
        let f o c = if (o|>ayHas c) then o else ayAddItm c o
        ay |> Array.fold f [||]
    let ayRz n dft ay = 
        let s = sz ay
        if n = s then ay
        else 
            match n > s with
            | true -> ayAdd ay (ayRepeat (n-s) dft)
            | false -> Array.take (s-n) ay
    let syShift sy = let a0,sy1 = ayShift sy in (dft "" a0), sy1
    let ssWdt(ss:ss) = ss |> seqMap len |> seqMax 
    let syAlignL'w w sy = sy |> ayMap (alignL w)
    let syAlignL sy = sy |> syAlignL'w (ssWdt sy)
    let syRTrim = ayMap rtrim
    let syLTrim = ayMap ltrim
    let syTrim  = ayMap trim
    let syQuote q = ayMap (quote q)

[<AutoOpen>]
module Function =
    let tee f a = f a; a
    let msgOk msg = Interaction.MsgBox(msg,MsgBoxStyle.OkOnly) |> ignore
    let swapPrm f = fun b a -> f a b
    
    // module FtRead =
    let ftLy(ft:ft):ly  = File.ReadAllLines ft
    let ftLines(ft:ft):lines = File.ReadAllText ft

    // OpnFil =
    let opnAppFt = File.AppendText
    let opnFt    = File.OpenText
    let opnWrtFt ft = new System.IO.StreamWriter(File.OpenWrite ft)

    // PfxSfx =
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
    let addSfxIfNonBlank sfx s = if isBlankStr s then "" else addSfx sfx s
    let rmvPfx pfx s = if hasPfx pfx s then midFm(len pfx) s else s
    let rmvSfx sfx s = if hasSfx sfx s then left(len sfx) s else s
    let syWhNotPfx pfx = ayWh <| hasPfx pfx
    let syAddPfx  pfx = addPfx pfx |> ayMap
    let syAddSfx  sfx = addSfx sfx |> ayMap
    let rplPfx pfx by = rmvPfx pfx >> addPfx by
    let syPfxCnt pfx ly =
        let f (c1,c2) lin = if lin |> hasPfx pfx then c1+1,c2 else c1,c2+2
        ly |> Array.fold f (0,0)

    // Pth =
    let isPthExist pth = System.IO.Directory.Exists(pth)
    let pthCrt     pth = System.IO.Directory.CreateDirectory(pth) |> ignore
    let pthEns     pth = if(not(isPthExist pth)) then pthCrt pth
    let pthSep         = Path.DirectorySeparatorChar.ToString()
    let pthRmvSfx      = rmvSfx pthSep
    let jnPthSeqLis pthSegLis = (pthSegLis |> List.map pthRmvSfx |> jn pthSep)  +  pthSep
    let curPth = System.AppDomain.CurrentDomain.BaseDirectory

    // Ffn =
    let ffnExt ffn:ext = let p = posRev "."    ffn in if(p=0) then ""  else midFm p ffn
    let ffnFn  ffn:fn = let p = posRev pthSep ffn in if(p=0) then ffn else midFm (p+1) ffn
    let ffnPth ffn = let p = posRev pthSep ffn in if(p=0) then ""  else left p ffn
    let ffnRmvExt ffn      = takRevBefOrAll "." ffn
    let ffnRplExt ext ffn  = (ffnRmvExt ffn) + ext

    // StrRpl
    let rpl ss by s = Strings.Replace(s,ss,by)
    let rplOnce ss by s = Strings.Replace(s,ss,by,Count=1)
    let rplDblSpc s = let rec r s = if (hasDblSpc s) then r (rpl "  " " " s) else s in r s
    let rplVbar     = rpl "|" "\r\n"

    // StrSplit =
    let split sep s     = Strings.Split(s,sep)
    let splitCrLf:lines->lin[] = split "\r\n"
    let splitLf:lines->lin[] = split "\r\n"
    let splitSpc = split " "
    let splitLvs:lin->term[] = rplDblSpc >> trim >> splitSpc
    let splitVbar:lin->lin[] = split "|"

    // Dic
    let mkKstr k v = kstr(k,v)
    let private fDotNN(k:string)(ly:string[]):string =
        let n = sz ly
        let r = runningSy n
        let zip = ayZip r ly
        let ly = zip |> ayMap(fun(runningNo,lin)->k+"."+runningNo+" " + lin)
        ly |> jnCrLf
    let private fDupKey(k:string)(ly:string[]):string = [ for i in ly do yield k + " " + i ] |> lisToAy |> jnCrLf
    let private kstrToStr_ (keyWithRunningN:bool)(kstr:kstr):string =
        let k = kstr.Key
        let s = kstr.Value
        if hasSub "\r\n" s |> not then k + " " + s else
            let f = if keyWithRunningN then fDotNN else fDupKey
            s|> splitCrLf |> f k
    let kstrToStr kstr = kstrToStr_ false kstr
    let kstrToStrN(kstr:kstr) = kstrToStr_ true kstr

    /// if the value-str has \r\n, the key will be repeated for each value-line
    let sdicToStr(sdic:sdic) = [ for i in sdic do yield (kstrToStr i) ] |> jnCrLf

    /// if the value-str has \r\n, the key will be repeated as key.nnn for each line
    let sdicToStrN(sdic:sdic) = [ for i in sdic do yield (kstrToStrN i) ] |> jnCrLf
    //sdicByVbl "lskdf sldkfj lskdj f|lksdjf lsdkjf |alsdkjf fjdl   l" |> sdicToStrN;;
    let empSdic = Map.empty<string,string>
    let empBdic = Map.empty<string,bool>
    let dicVopt         k    (dic:Map<'k,'v>) = if dic.ContainsKey(k) then Some(dic.Item k) else None
    let dicVal          k    (dic:Map<'k,'v>) = dic.Item k
    let dicAddKV        (k,v)(dic:Map<'k,'v>) = dic.Add(k,v)
    let dicAddKVSkipDupK(k,v)(dic:Map<'k,'v>) = if dic.ContainsKey(k) |> not then dic.Add(k,v) else dic
    let dicHasKey(k:key)(dic:dic<'v>) = dic.ContainsKey(k) 
    let inDic dic k = dicHasKey k dic
    let notInDic dic = pNot(inDic dic)
    let keyVal dic k = dicVal k dic
    let private f1 (d:sdic) lin = dicAddKVSkipDupK(brk1Spc lin) d
    let private f2 (d:sdic) lin = dicAddKV        (brk1Spc lin) d
    let private s f (ly:ly) = ly |> Array.fold f empSdic
    let ly_dupFmTo(ly:ly):fmTo=
        let fmIx = 0
        let toIx = 0
        fmIx,toIx
    let fmTo_isEmpty(ub:ix)(fmTo:fmTo):bool = true
    let ayRplByFmTo by fmTo ay = ay
    let sdicByLySkipDup:ly->sdic = s f1
    let sdicByLy       :ly->sdic= s f2
    let sdicByVbl      :vbl->sdic = splitVbar >> sdicByLy
    let isSdic(o:obj) = match o with :? sdic -> true | _ -> false

    // Fmt
    let fmtQQ qqStr (olis:olis) = olis |>lisFold (fun o v->(rplOnce "?" (toStr v) o)) qqStr

    // Term
    let rmvFstTerm(s:termLvs):termLvs = takAftSpcOrAll s |> ltrim
    let rmv2Terms:termLvs->termLvs = rmvFstTerm >> rmvFstTerm
    let fstTerm:termLvs->term = ltrim >> takBefSpcOrAll
    let sndTerm:termLvs->term = takAftSpcOrAll >> fstTerm
    let shiftTerm(s:termLvs):term*termLvs =(fstTerm s),(rmvFstTerm s)
    let ly_combineSamFstTerm ly:lin = 
        match Seq.tryHead ly with 
        | None -> ""
        | _ ->
            let fst,rst = ly |> ayMap shiftTerm |> ayUnzip
            if isAllEq fst |> not then failwith "{ly} should have all same fst-term" else
                fst.[0] + " " + (rst |> jnSpc)
    let brkNTerm'f (lis,s) _ = let t,s = shiftTerm s in if(isEmpStr t) then lis,s else lis@[t],s
    let brkNTerm atMost s    = let lis,s = {2..atMost} |> Seq.fold brkNTerm'f ([],s) in lis@[s]
    let brk3Term s  = 
        let a = brkNTerm 3 s |> lisToAy
        let a = ayRz 3 "" a
        a.[0],a.[1],a.[2]
    let brk2Term s  = let a = brkNTerm 2 s in a.[0],a.[1]
    let isNterm n s = (brkNTerm (n+1) s |> List.length) = n
    let is1term     = isNterm 1
    let is2term     = isNterm 2
    let is3Term     = isNterm 3
    let nTerm lin   = sz (splitLvs lin)

    // dupFstTermLy
    let dupFstTermLy_isVdt(ly:dupFstTermLy):bool =
        let f = ly |> ayMap fstTerm
        isAllEq f
    let dupFstTermLy_mge(ly:dupFstTermLy):lin = 
        assert(dupFstTermLy_isVdt ly)
        if ayIsEmpty ly then "" else
            let k = ly.[0] |> fstTerm
            k + (ly |> ayMap rmvFstTerm |> ayMap trim |> jnSpc)
    let ly_dupFstTermSy(ly:ly):sy = ly |> ayMap fstTerm |> ayWhDup
    let ly_splitInto_nonDup_and_dup(ly:ly):(ly*dupFstTermLy) = 
        let dupSy = ly_dupFstTermSy(ly)
        if ayIsEmpty dupSy then ly,[||] else
            let f:(slis*slis)->lin->(slis*slis) = fun (nonDup,dup)(lin) ->
                let t1 = fstTerm lin
                if t1 |> isInAy dupSy then (nonDup@[lin],dup) else (nonDup,dup@[lin])
            let nonDupLis,dupLis = ly|>ayFold f ([],[])
            let nonDup = nonDupLis |> lisToAy
            let dup    = dupLis    |> lisToAy
            nonDup,dup
    let rec ly_mgeDupFstTerm ly =
        let nonDup,dup = ly_splitInto_nonDup_and_dup ly
        if ayIsEmpty dup then nonDup else
            let lin = dupFstTermLy_mge dup
            ayPush lin nonDup |> ly_mgeDupFstTerm
    let sdicByLyHandleDup = ly_mgeDupFstTerm >> sdicByLy


    // Rmk
    let lin_has2Dash:lin->bool = hasSub "--"
    let lin_has3Dash:lin->bool = hasSub "---"
    let lin_isRmk:lin->bool = pOr isEmpStr lin_has2Dash
    let lin_isNonRmk:lin->bool = pNot lin_isRmk
    let lin_rmvRmk rmk:lin->lin = takBefOrAll rmk >> rtrim
    let lin_rmv3DashRmk:lin->lin = lin_rmvRmk "---"
    let lin_rmv2DashRmk:lin->lin = lin_rmvRmk "--"
    let ly_rmv3DashRmk:ly->ly = ayMap lin_rmv3DashRmk
    let ly_rmv2DashRmk:ly->ly = ayMap lin_rmv2DashRmk
    let ly_rmvRmkLin:ly->ly = ayWh lin_isNonRmk
    let lin_isBlank(lin:lin) = lin.Trim() = ""
    let ly_rmvBlankLin:ly->ly = ayWh (pNot lin_isBlank)

    // Lis
    type dftLis<'a> = unit->'a list
    let lisDft(dftLis:dftLis<'a>) lis = if lisIsEmpty lis then dftLis() else lis
    let lisRz n dft lis =
        let sz = List.length lis
        if sz = n then lis else
            match sz > n with
            | true -> List.take sz lis
            | false -> lis@(lisDup (n-sz) dft)
    let olis(objLis:olis) = objLis
    let isInLis lis a = lis |> lisAny(eq a)
    let isInLisI(slis:slis) s = slis |> lisAny(strEqIgnCas s)
    let lisMinus lis1 lis2    = lis1|>lisWh(fun i->isInLis i lis2)
    let lisAddIdx lis = lis |> List.mapi (fun i itm -> i,itm)

    // Lis
    let lisWhDup lis =  lis |> List.countBy(fun a->a) |> lisChoose (fun(k,c) -> if(c>1) then Some k else None)

    // Tab
    let syTab pfx nSpc (sy:sy) : sy = 
        let tab = spc nSpc
        let sy = sy |> syAddPfx tab
        if(sz sy > 0) then 
            let pfx' = alignL nSpc pfx
            sy.[0] <- rplPfx tab pfx' (sy.[0])
        sy
    let linesTab(pfx:pfx)(nSpc:nSpc)(lines:lines):lines = lines |> splitCrLf |> syTab pfx nSpc |> jnCrLf
    let linesWdt lines:wdt = lines |> splitCrLf |> ssWdt
    let linesAyWdt linesAy:wdt = linesAy |> ayMap linesWdt |> ayMax
    let linesAddSfx w sfx lines =
        let ly = lines |> splitCrLf
        let las = ayLas ly |> alignL w |> addSfx sfx
        ly |> ayRmvLasEle |> jnCrLf |> addSfxIfNonBlank "\r\n" |> addSfx las

    // Tmp
    let tmpPth        = jnPthSeqLis[Environment.GetEnvironmentVariable "tmp";"fsharp"]
    let tmpNm    ()   = "T" + DateTime.Now.ToString("yyyy_MM_dd_HHmmss")
    let tmpFn    ext  = tmpNm() + ext
    let tmpFtFn  ()   = tmpFn ".txt" 
    let tmpFdr   fdr  = let p = jnPthSeqLis[tmpPth;fdr;tmpNm()] in pthEns p; p 
    let tmpFt    ()   = tmpPth + tmpFtFn()
    pthEns tmpPth

    // Wrt
    let wrt ft s = File.WriteAllText(ft,s)
    let ftWrtStr s ft = wrt ft s
    let strOptWrt ft s' = if(isSome s') then wrt ft (optVal s')
    let ssWrt ft ss = File.WriteAllLines(ft,ss|>ssSy)
    let ayWrtAy ft ay  = ay |> toSs |> ssWrt ft

    // Brw =
    let ftBrw ft = shell(sprintf "code.cmd \"%s\" " ft)(sty.NormalFocus )
    let brw s = tmpFt() |> tee (ftWrtStr s) |> ftBrw
    let ssBrw sy = sy |> jnCrLf |> brw
    let ayBrw ay = ay|>aySs  |>ssBrw
    let objBrw o = o|>toStr|>brw
    let pthBrw(pth:pth)  = if(isPthExist pth) then shell(sprintf """explorer "%s" """ pth)  sty.NormalFocus
    let tmpPthBrw ()  = pthBrw tmpPth

    // ftSrt
    let ftSrt ft = ft |> ftLy |> aySrt |> ssWrt ft

    // 
    // MacroStr
    let macroStrNy(s:macroStr):sy = 
        let sy  = split "{" s
        let sy1 = sy |> ayWh (hasSub "}")
        let sy2 = sy1 |> ayMap (takBef "}")
        let sy3 = sy2 |> ayRmvDup
        let o   = sy3 |> ayMap (quote "{}")
        o
    let isPrim(a:'a):bool = if isNull a then false else (box a).GetType().IsPrimitive
    let toLines(a:'a):lines =
        ret {
            if isNull a then return "<null>"
            if isPrim a then return toStr a
            if isStr a then 
                let s = toStr a
                return (if s="" then "<BlankStr>" else s)
            if isSdic a then return ((box a):?>sdic) |> sdicToStr 
            if isSeq a then return (box a) :?> 'a seq |> toSs |> jnCrLf
            return toStr a
        }
    let erLines(macroStr)(olis:olis):lines = 
        let nmLis = macroStrNy macroStr |> ayToLis 
        let w = ssWdt nmLis + 1
        let zip = List.zip nmLis (olis|>lisMap toLines)
        let x(nm,lines) = linesTab nm w lines
        let linesLis = zip |> lisMap x
        let lines = macroStr :: linesLis |> jnCrLf
        let fmtStackTrace s =
            let ay1,ay2 = splitCrLf s |> ayMap((rmvPfx "   at ")>>(brk1 " in ")) |> ayUnzip
            let ay2a = syAlignL ay2
            let o = ay2a |> ayZip ay1 |> ayMap(fun(a,b)->b+" "+a) |> jnCrLf
            o
        let stack = fmtStackTrace System.Environment.StackTrace
        lines + "\r\n" + stack
    let er macroStr olis = erLines macroStr olis |> tee brw |> failwith

    // Dup
    let whDup seq = 
        query {
            for i in Queryable.AsQueryable(seq) do
            groupBy i into g
            where(g.Count()>1)
            select g.Key }
    let dupMsgOptAy ay:msgOptAy = 
        let dupMsgOptAyByDupAy dupAy ay =
            let dupMsg = toStr >> sprintf "dup(%s)" >> some
            let msgOpt itm = if itm |> isInSeq dupAy then dupMsg itm else None
            let o = ay |> Array.map msgOpt
            o
        dupMsgOptAyByDupAy (ayWhDup ay) ay
    let ly_dupFstTermMsgOptAy(ly:ly):msgOptAy=
        let dupSy=ly_dupFstTermSy(ly)
        let fstTermAy=ly|>ayMap fstTerm
        let msgOpt fstTerm = if fstTerm|>isInAy dupSy then Some(fmtQQ("dup(?)")[fstTerm]) else None
        fstTermAy|>ayMap msgOpt 
    let ly_dupFstTermLyMsgs(ly:ly):lyMsgs= ly|>ly_dupFstTermMsgOptAy|>(ayMap optOneEleLis)
    let doc'fstTermDupMsgAy =
        let doc = 
            """
fstTermDupMsgAy'doc = {ly}   :  {dupMsgOpt}
                    : seq<'a> -> seq<'a> -> string option list
it is mapping of {seq} to some {dupMsgsAy} if {ly}-itm is found in with lin-fstTerm is dup
"""
        let eg0() =
            let ay = [|"aa";"aa";"cc";"bb";"dd"|]
            let dupMsgsAy = ly_dupFstTermLyMsgs ay
            erLines doc [ay;dupMsgsAy]
        let eg = [eg0]
        let nm = "fstTermDupMsgsAy"
        let nmSpc = "Lib.Core.Dup"
        let sgn = "ly -> msgs[]"
        {nm=nm;nmSpc=nmSpc;sgn=sgn;doc=doc;eg=eg}
    let doc'ayDupMsg =
        let doc = """return {msg' list} of same size as {lis}.  
Those {lis}.item with dup will get "dup(?)
where ? is {lis}.item.ToString()"""
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
            let ay = splitCrLf tp 
            erLines doc [ay; ayDupMsg ay]
        let eg = [eg0]
        let nm = "aa"
        let sgn = ""
        let nmSpc = ""
        {doc=doc; nm=nm; nmSpc=nmSpc; sgn=sgn; eg=eg}

    // OptSeq 
    let optSeqZip a aOpt = 
        query {
            for (a,aOpt) in Seq.zip a aOpt do
            where (isSome aOpt)
            select (a,aOpt.Value)
        }
    let optSeqZipAsAy a aOpt =optSeqZip a aOpt |> seqToAy
    let optSeqZipAsLis a aOpt = optSeqZip a aOpt |> seqToLis

    // AddIx =
    let seqAddIx seq = seq |> Seq.mapi zip
    let ayAddIx ay = ay |> Array.mapi zip
    let lisAddIx lis = lis |> List.mapi zip

    // Seq =
    let seqHeadDft dft = Seq.tryHead >> optDft dft
    let seqChoose cond lis = 
        let p(cond,v) = if(cond()) then Some v else None
        List.zip (cond@[turnT]) lis |> List.pick p
    let seqUnZip(seq:('a*'b) seq) = (seq |>Seq.map (fun(a:'a,_)->a)),(seq |>Seq.map(fun(_,b:'b)->b))
    let seqSplitAy p (a:'a seq) =
        let f (t,f) i = if p i then (t@[i],f) else (t,f@[i])
        let toAy(a,b) = (lisToAy a),(lisToAy b)
        a |> Seq.fold f ([],[]) |> toAy
 
    // Ly =
    let ly_cmbFstTerm(ly:ly):ly = 
        let fmToBy ly = 
            let ay = ly |> ayMap fstTerm
            match dupFmTo ay with
            | Some fmTo -> 
                let by = [|""|]
                Some(fmTo,by)
            | None -> None
        let rec rpl ly =
            match (fmToBy ly) with
            | None -> ly
            | Some(fmTo,by) -> rpl (ayRplByFmTo by fmTo ly)
        rpl ly

    // Enm

    let isEnm<'a> = typeof<'a>.IsEnum
    let assertIsEnm<'a> = if not isEnm<'a> then er "The {type-name} is not Enum" [typeof<'a>.Name]
    let enmAy<'a> :'a[] = [| for i in Enum.GetValues(typeof<'a>) do yield i :?> 'a|]
    let enmNy<'a> : ny =  Enum.GetNames(typeof<'a>) 
    let private x<'a> ignoreCase s = 
        assertIsEnm<'a>
        Enum.Parse(typeof<'a>,s,ignoreCase) :?> 'a
    let private y<'a> ignoreCase s = try Some(x<'a> ignoreCase s) with _ -> None
    let enmParse<'a> s  = x<'a> false s
    let enmParseI<'a> s = x<'a> true s
    let enmTryParse<'a> s  = y<'a> false s
    let enmTryParseI<'a> s = y<'a> true s
    let enmToStr<'a> = enmNy<'a> |> aySrt |> jn " | "

    // Nbr 
    let nDig = nDig
    let runningSy = runningSy

open Microsoft.VisualStudio.TestTools.UnitTesting
[<TestClass>]
type Seq() =
    [<TestMethod>]
    member x.dupFmTo() =
        let lis=[1;2;3;4;4;4;5]
        let act = dupFmTo lis
        let exp = Some(3,5)
        assert(act = exp)
        //
        let lis=[1;2;3;4;5;6]
        let act = dupFmTo lis
        let exp = None
        assert(act = exp)
[<TestClass>]
type Ay() =
    [<TestMethod>]
    member x.ayRplByFmTo() =
        let ay = [|1;2;3;4;5|]
        let fmTo = 1,2
        let by = [|9;10;11|]
        let act = ayRplByFmTo by fmTo ay
        let exp = [|1;9;10;11;4;5|]
        assert(act=exp)
[<TestClass>]
type Term() =
    [<TestMethod>]
    member x.combineSamFstTerm() =
        let ly = splitVbar "aa xyz  |aa bbccdd|aa 1234"
        let act = ly_combineSamFstTerm ly    
        let exp = "aa xyz bbccdd 1234"
        assert(act=exp)
        //
        let ly = splitVbar "aaa xyz  |aa bbccdd|aa 1234"
        try 
            let act = ly_combineSamFstTerm ly
            assert false
        with e ->
            assert (e.Message = "{ly} should have all same fst-term")
            