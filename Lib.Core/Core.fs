[<AutoOpen>]
module Lib.Core.Functions
#nowarn "40"
#nowarn "64"
open System.Linq
open System.IO
open System
open Lib.Core
open Microsoft.VisualBasic
// Emp
let empSlis:slis = []
let empBdic:bdic = Map.empty<string,bool>
let empSdic:sdic = Map.empty<string,string>
let empSy:sy = [||]

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
let tyCdTy = Type.GetType("System.TypeCode")
let tyCdNm o = Enum.GetName(tyCdTy,tyCd o)
let tryTyCd o = if isNull o then None else Some(tyCd o)
let nzFun f o = if isNull o then false else f o
let isAy(o:obj) = nzFun(fun o->o.GetType().IsArray) o
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
let isInSeq seq itm = Seq.contains itm seq


// Shell
let shell(sty:AppWinStyle) cmd = Interaction.Shell(cmd,sty,false,-1) |> ignore
let shellNorm = shell AppWinStyle.NormalFocus

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
let lisHead = List.head
let lisTryHead = List.tryHead
let lisTail = List.tail
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
let right len s         = Strings.Right(s,len)
let strDup n (s:string) = Strings.StrDup(n,s)
let left  len s         = Strings.Left(s,len)
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
let alignL w s = 
    let l = len s 
    if w >= l 
        then s + spc (w - l) 
        else 
            if w>=2 
                then (left(w-2) s) + ".."
                else s
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
let private er1 = fun sep s -> failwith("no sep[" + sep + "] in s[" + s + "]")

let private b1 fPos (sep:sep)(s:s) = 
    let p = fPos sep s in 
    if(p = -1) then er1 sep s
    brkAt p (len sep) s
let brk     = b1 pos    
let brkRev  = b1 posRev 

let private b2 fPos f (sep:sep)(s:s) = let p=fPos sep s in if(p= -1) then (f s) else brkAt p (len sep) s
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
let quoteSng = quote "'"
let quoteDbl = quote "\""
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
let jnComma  ss:lin = jn "," ss
let jnCommaSpc ss:lin = jn ", " ss

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
    
// Opy
/// return {'a option[]} from {opy:'a option[]} for those element has value.
let opyWhSome opy = opy |> ayWh isSome

/// return {'a[]} from {opy:'a option[]} for those element has value.
let opyWhSomVal opy = opy|>opyWhSome|>ayMap optVal

/// return true if all elements of given {opy} isSome
let opyAllSome ay = ay |> ayAll isSome
let opyAnySome ay = ay |> ayAny isSome
let opyAllNone ay = ay |> ayAll isNone
let opyHasNone ay = ay |> ayAny isNone

// Dft
let dft      = optDft
let dftF opt = if isSome opt then opt.Value else false
let dftT opt = if isSome opt then opt.Value else false
let dftBlankStr = dft "" 

// To
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
let aySs(ay:'a[]):ss=ay|>seqMap toStr
let ayRplByFmTo by (fmTo:fmTo) ay =
    let (fmIx,toIx) = fmTo
    let p1 = Array.take fmIx ay
    let p2 = Array.skip(toIx+1) ay
    Array.concat[p1;by;p2]
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
let ayRepeat n dft = seq {for j=1 to n do yield dft} |> Seq.toArray
let ayRmvFstEle ay = Array.skip 1 ay
let ayRmvLasEle ay = Array.take (sz ay - 1) ay
let ayRmvDup ay =
    let f o c = if (o|>ayHas c) then o else ayAddItm c o
    ay |> Array.fold f [||]
let ayRz n dft ay = 
    let s = sz ay
    if n = s then ay else 
        match n > s with
        | true -> ayAdd ay (ayRepeat (n-s) dft)
        | false -> Array.take (s-n) ay
let syShift sy = let a0,sy1 = ayShift sy in (dft "" a0), sy1
let private erXX n sy = failwith(sprintf "size of {sy} should be[%i], but now[%i]" (sz sy) n)
let syT2(sy:sy) = if sz sy<>2 then erXX 2 sy else sy.[0],sy.[1]
let syT3(sy:sy) = if sz sy<>3 then erXX 3 sy else sy.[0],sy.[1],sy.[2]
let syT4(sy:sy) = if sz sy<>4 then erXX 4 sy else sy.[0],sy.[1],sy.[2],sy.[3]
let syT5(sy:sy) = if sz sy<>5 then erXX 5 sy else sy.[0],sy.[1],sy.[2],sy.[3],sy.[4]
let ssWdt(ss:ss) = ss |> seqMap len |> seqMax 
let syAlignL sy = sy |> ayMap(alignL (sy|>ssWdt))
let syRTrim = ayMap rtrim
let syLTrim = ayMap ltrim
let syTrim  = ayMap trim
let syQuote q = ayMap (quote q)
let ayIsSamSz ay1 ay2 = sz ay1 = sz ay2
let push itm ay = Array.append ay [|itm|]

// AyWh
let ayWhOne cond ay = ay |> ayPick (fun(i)->if cond i then Some i else None)
let ayWhByBoolAyForT boolAy ay = ayZip boolAy ay |> ayWh(fst>>pT)
let ayWhByBoolAyForF boolAy ay = ayZip boolAy ay |> ayWh(fst>>pF)
let ayWhByOnyForNone ony ay = ayZip ony ay |> ayWh(fst>>isNone) |> ayMap snd
let ayWhByOnyForSome ony ay = ayZip ony ay |> ayWh(fst>>isSome) |> ayMap snd
let ayWhDup  ay = ay |> Array.countBy(fun a->a) |> ayChoose (fun(k,c) -> if(c>1) then Some k else None)

// Seq
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

// Function
let tryDo f = try f() finally()
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
let hasSfx sfx s = takSfx sfx s = sfx
let hasPfx pfx s = takPfx pfx s = pfx
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
let pthSep :pthSep        = Path.DirectorySeparatorChar.ToString()

// Ffn =
let ffnExt(ffn:ffn):ext = let p = posRev "."   ffn in if(p=0) then ""  else midFm p ffn
let ffnFn (ffn:ffn):fn = let p = posRev pthSep ffn in if(p=0) then ffn else midFm (p+1) ffn
let ffnPth(ffn:ffn):pth = let p = posRev pthSep ffn in if(p=0) then ""  else left p ffn
let ffnRmvExt(ffn:ffn):fnn  = takRevBefOrAll "." ffn
let ffnRplExt ext ffn  = (ffnRmvExt ffn) + ext
let ffnDlt(ffn:ffn) = File.Delete ffn
let ffnDltTry(ffn:ffn) = tryDo(fun()->ffnDlt ffn)
// Pth =
let isPthExist(pth:pth) = System.IO.Directory.Exists(pth)
let pthCrt    (pth:pth) = System.IO.Directory.CreateDirectory(pth) |> ignore
let pthEns    (pth:pth) = if(not(isPthExist pth)) then pthCrt pth
let pthRmvSfx:pth->pth    = rmvSfx pthSep
let pthFfnAy  (pth:pth):ffn[] = Directory.GetFiles(pth)
let pthEnsSfx (pth:pth):pth = if hasSfx pthSep pth then pth else pth + pthSep
let pthFnAy   (pth:pth):fn[] = pth |> pthFfnAy |> ayMap(rmvPfx(pthEnsSfx pth))
let jnPthSeqLis pthSegLis = (pthSegLis |> List.map pthRmvSfx |> jn pthSep)  +  pthSep
let curPth = System.AppDomain.CurrentDomain.BaseDirectory
let pthRmv(pth:pth) = Directory.Delete pth
let pthSubPthAy(pth:pth):pth[] = Directory.GetDirectories(pth)
let rec pthClr (pth:pth) = 
    if isPthExist pth then
        let xffn ffn = try ffnDlt ffn finally ()
        let xpth pth = try pthClr pth; pthRmv pth finally ()
        pthFfnAy pth |> Array.iter xffn
        pthSubPthAy pth |> Array.iter xpth
            
// StrRpl
let rpl ss by s = Strings.Replace(s,ss,by)
let rplQ = rpl "?"
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
let dicVopt         k    (dic:Map<'k,'v>) = if dic.ContainsKey(k) then Some(dic.Item k) else None
let dicDftVal dft   k    (dic:Map<'k,'v>) = if dic.ContainsKey(k) then dic.Item k else dft
let dicVal          k    (dic:Map<'k,'v>) = dic.Item k
let dicAddKV        (k,v)(dic:Map<'k,'v>) = dic.Add(k,v)
let dicAddKVSkipDupK(k,v)(dic:Map<'k,'v>) = if dic.ContainsKey(k) |> not then dic.Add(k,v) else dic
let dicHasKey(k:key)(dic:dic<'v>) = dic.ContainsKey(k) 
let inDic dic k = dicHasKey k dic
let notInDic dic = pNot(inDic dic)
let keyVal dic k = dicVal k dic
let keyVopt dic k = dicVopt k dic
let keyDftVal dft dic k = dicDftVal dft k dic
let private f1 (d:sdic) lin = dicAddKVSkipDupK(brk1Spc lin) d
let private f2 (d:sdic) lin = dicAddKV        (brk1Spc lin) d
let private s f (ly:ly) = ly |> Array.fold f empSdic
let lyDupFmTo(ly:ly):fmTo =
    let fmIx = 0
    let toIx = 0
    fmIx,toIx
let fmToIsEmpty(ub:ix)(fmTo:fmTo):bool = true
let sdicBySdicLySkipDup:sdicLy->sdic = s f1
let sdicBySdicLy       :sdicLy->sdic = s f2
let sdicBySdicVbl      :sdicVbl->sdic = splitVbar >> sdicBySdicLy
let isSdic(o:obj) = match o with :? sdic -> true | _ -> false

// Fmt
let fmtQQ qqStr (lis:'a list) = lis |>lisFold (fun o v->(rplOnce "?" (toStr v) o)) qqStr

// Term
let rmvFstTerm(s:termLvs):termLvs = takAftSpcOrAll s |> ltrim
let rmv2Terms:termLvs->termLvs = rmvFstTerm >> rmvFstTerm
let fstTerm:termLvs->term = ltrim >> takBefSpcOrAll
let sndTerm:termLvs->term = takAftSpcOrAll >> fstTerm
let shiftTerm(s:termLvs):term*termLvs =brk1Spc s
let lyCombineFstTerm(ly:ly):ly = 
    let fmToBy ly = 
        let ay = ly |> ayMap fstTerm
        match dupFmTo ay with
        | Some fmTo -> let by = [|""|] in Some(fmTo,by)
        | None -> None
    let rec rpl ly =
        match (fmToBy ly) with
        | None -> ly
        | Some(fmTo,by) -> rpl (ayRplByFmTo by fmTo ly)
    rpl ly
let lyCombineSamFstTerm ly:lin = 
    if (Seq.tryHead ly).IsNone then "" else
        let fst,rst = ly |> ayMap shiftTerm |> ayUnzip
        if isAllEq fst |> not then failwith "{ly} should have all same fst-term" else
            fst.[0] + " " + (rst |> jnSpc)
let brkNTerm n s    = 
    let f(lis,s) _ = 
        let t,s = shiftTerm s 
        lis@[t],s
    let lis,s = {2..n} |> Seq.fold f ([],s)
    lis@[s] |> List.toArray
let brk5Term = brkNTerm 5 >> syT5
let brk4Term = brkNTerm 4 >> syT4
let brk3Term = brkNTerm 3 >> syT3
let brk2Term = brkNTerm 2 >> syT2
let isNterm n s = (splitLvs s |> Array.length) = n
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
let lyDupFstTermSy(ly:ly):sy = ly |> ayMap fstTerm |> ayWhDup
let lySplitInto_nonDup_and_dup(ly:ly):(ly*dupFstTermLy) = 
    let dupSy = lyDupFstTermSy(ly)
    if ayIsEmpty dupSy then ly,[||] else
        let f:(slis*slis)->lin->(slis*slis) = fun (nonDup,dup)(lin) ->
            let t1 = fstTerm lin
            if t1 |> isInAy dupSy then (nonDup@[lin],dup) else (nonDup,dup@[lin])
        let nonDupLis,dupLis = ly|>ayFold f ([],[])
        let nonDup = nonDupLis |> lisToAy
        let dup    = dupLis    |> lisToAy
        nonDup,dup
let rec lyMgeDupFstTerm ly =
    let nonDup,dup = lySplitInto_nonDup_and_dup ly
    if ayIsEmpty dup then nonDup else
        let lin = dupFstTermLy_mge dup
        push lin nonDup |> lyMgeDupFstTerm
let sdicByLyHandleDup = lyMgeDupFstTerm >> sdicBySdicLySkipDup

// Rmk
let linHas2Dash:lin->bool = hasSub "--"
let linHas3Dash:lin->bool = hasSub "---"
let linIsRmk:lin->bool = pOr isEmpStr linHas2Dash
let linIsNonRmk:lin->bool = pNot linIsRmk
let linRmvRmk rmk:lin->lin = takBefOrAll rmk >> rtrim
let linRmv3DashRmk:lin->lin = linRmvRmk "---"
let linRmv2DashRmk:lin->lin = linRmvRmk "--"
let lyRmv3DashRmk:ly->ly = ayMap linRmv3DashRmk
let lyRmv2DashRmk:ly->ly = ayMap linRmv2DashRmk
let lyRmvRmkLin:ly->ly = ayWh linIsNonRmk
let linIsBlank(lin:lin) = lin.Trim() = ""
let lyRmvBlankLin:ly->ly = ayWh (pNot linIsBlank)

// Lis
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
let tmpPthClr()   = pthClr tmpPth
pthEns tmpPth

// Wrt
let wrt ft s = File.WriteAllText(ft,s)
let ftWrtStr s ft = wrt ft s
let strOptWrt ft s' = if(isSome s') then wrt ft (optVal s')
let ssWrt ft ss = File.WriteAllLines(ft,ss|>ssSy)
let ayWrtAy ft ay  = ay |> toSs |> ssWrt ft

// Brw =
let ftBrw ft = sprintf """code.cmd "%s" """ ft |> shellNorm
let brw s = tmpFt() |> tee (ftWrtStr s) |> ftBrw
let ssBrw sy = sy |> jnCrLf |> brw
let ayBrw ay = ay|>aySs  |>ssBrw
let objBrw o = o|>toStr|>brw
let pthBrw(pth:pth)  = if(isPthExist pth) then sprintf """explorer "%s" """ pth |> shellNorm
let tmpPthBrw ()  = pthBrw tmpPth
   
// ftSrt
let ftSrt ft = ft |> ftLy |> aySrt |> ssWrt ft

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
let erImpossible() = er "Impossible to reach here" []

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
let lyDupFstTermMsgOptAy(ly:ly):msgOptAy=
    let dupSy=lyDupFstTermSy(ly)
    let fstTermAy=ly|>ayMap fstTerm
    let msgOpt fstTerm = if fstTerm|>isInAy dupSy then Some(fmtQQ("dup(?)")[fstTerm]) else None
    fstTermAy|>ayMap msgOpt 
let lyDupFstTermLyMsgs(ly:ly):lyMsgs= ly|>lyDupFstTermMsgOptAy|>(ayMap optOneEleLis)
let doc'fstTermDupMsgAy =
    let doc = 
        """
fstTermDupMsgAy'doc = {ly}   :  {dupMsgOpt}
                : seq<'a> -> seq<'a> -> string option list
it is mapping of {seq} to some {dupMsgsAy} if {ly}-itm is found in with lin-fstTerm is dup
"""
    let eg0() =
        let ay = [|"aa";"aa";"cc";"bb";"dd"|]
        let dupMsgsAy = lyDupFstTermLyMsgs ay
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
 
// BoolAy
let boolAyAnd boolAy = boolAy |> ayAll(fun(b:bool)->b=true)
let boolAyOr  boolAy = boolAy |> ayAny(fun(b:bool)->b=false)

// Enm

let isEnm<'a> = typeof<'a>.IsEnum
let assertIsEnm<'a> = if not isEnm<'a> then er "The {type-name} is not Enum" [typeof<'a>.Name]
let enmAy<'a> :'a[] = [| for i in Enum.GetValues(typeof<'a>) do yield i :?> 'a|]
let enmNy<'a> : ny =  Enum.GetNames(typeof<'a>) 
let private x1<'a> ignoreCase s = 
    assertIsEnm<'a>
    Enum.Parse(typeof<'a>,s,ignoreCase) :?> 'a
let private y<'a> ignoreCase s = try Some(x1<'a> ignoreCase s) with _ -> None
let enmParse<'a> s  = x1<'a> false s
let enmParseI<'a> s = x1<'a> true s
let enmTryParse<'a> s  = y<'a> false s
let enmTryParseI<'a> s = y<'a> true s
let enmToStr<'a> = enmNy<'a> |> aySrt |> jn " | "