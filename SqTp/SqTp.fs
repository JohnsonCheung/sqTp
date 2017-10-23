#nowarn "40" 
#nowarn "64" 
namespace Lib.SqTp
open Lib.Core

[<AutoOpen>]
module IxLin =
    type ILin = { ix: int; lin: string }
    type IMsg = { ix: int; msg: string }
    /// return {ILin[]} from {ly} so that no need to process lines will be skipped
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
    let private put r src = src |> syAlignL |> ayMapi(addMsg r) |> ayMap unpack |> Array.concat
    let srcPutRslt r src = if (Array.isEmpty r) then false,src else true,put r src
        
    /// use {chkLinF} to check each {src[].lin} and return the {Rslt[]}, 
    /// where Rslt={lin;linIdx}.
    /// Rslt.linIdx coming from Src.linIdx 
    /// and Rslt.mIMsgoming given chkLinF().Value
    let chkSrcLin(chkLinF:string->string option)(src:ILin[]):IMsg[] = [||]
    let chkSrcBk (bkChkr:string[]->IMsg[])(src:ILin[]):IMsg[] =
        [||]
    let chkDupTermOne(src:ILin[]): IMsg[] =
        let chk(src:string[]):IMsg[] = [||]
        chkSrcBk chk src

[<AutoOpen>]
module Typ =
    //------------------------------
    type SqTpRslt = { tp': string option; sq' : string option }
    //------------------------------
    type SqBt = PrmBk|SwBk|SqBk|RmkBk|ErBk
    type sqLt = Sel|SelDis|Upd|Set|Fm|Gp|Jn|Left|Wh|WhBet|WhLik|WhIn|And|AndBet|AndIn|AndLik
    //------------------------------
    type SwOp = AND | OR | EQ | NE
    type SwTerms = TermAy of string[] | T1T2 of string * string
    type Sw = Map<string,bool>
    type SwLin = {k:string;op:SwOp;terms:SwTerms}
    let swOp op = System.Enum.Parse(typeof<SwOp>,op,true):?>SwOp
    let swTerms op termLvs = 
        let ay = splitLvs termLvs
        match op with
        | AND | OR -> 
            if ay.Length <> 2 then failwith("sz of terms of EQ NE switch line should be 2, but now is [" + string (sz ay) + "]")
            SwTerms.TermAy ay
        | NE | EQ ->
            if ay.Length = 0 then  failwith("sz of terms of EQ NE switch line should be 2, but now is [" + string (sz ay) + "]")
            SwTerms.T1T2(ay.[0],ay.[1])
    let swLin(sy:string[]) =
        let op = swOp sy.[1]
        let terms = swTerms op sy.[2]
        {k=sy.[0];op=op;terms=terms}
    let empSw:Sw = Map.empty<string,bool>
    //------------------------------
    type Prm = Map<string,string>
    let empPrm:Prm = Map.empty<string,string>

[<AutoOpen>]
module VdtSq =
    let lin'sqLt lin = Sel
    let sqLin'chk lin =  Some ""
        (*
        oneOf {
        if(isSqLin lin) then 
            match lin'sqLt lin with
            | Sel -> ()
            | _ ->()
        if(isExprLin lin) then
            ()
        return "lin must a sql-lin or $expr-line"
        }
        *)
    let sqILinAy'chk'ExprMustBeAtEnd(iLinAy:ILin[]) = [||]
    let prmLy'vdt ly : bool*string[] =
        let l = ly |> IxLin.wh (pNot isRmkLin)
        let r1 = l |> IxLin.chkSrcLin sqLin'chk
        let r2 = l |> sqILinAy'chk'ExprMustBeAtEnd
        let r = Array.concat[r1;r2]
        ly|>IxLin.srcPutRslt r1

    let vdtSqLy (ly:string[]) = true,ly

[<AutoOpen>]
module VdtPrm =
    let chkPrmLin lin = oneOf {
        if(hasPfx "%" lin|>not) then return "must have pfx-(%)"
        if(hasPfx "%?" lin) then 
            if nTerm lin <> 2 then return "for %?, it should have only 2 terms"
            let s = sndTerm lin
            if (s<>"0" && s<>"1") then return "for %?, 2nd term must be 0 or 1"
        }
    let vdtPrmLy ly : bool*string[] =
        let l = ly |> IxLin.wh (pNot isRmkLin)
        let r1 = l |> IxLin.chkSrcLin chkPrmLin
        let r2 = l |> IxLin.chkDupTermOne
        let r = Array.concat[r1;r2]
        ly|>IxLin.srcPutRslt r1

[<AutoOpen>]
module VdtSw =
    let chkSwLin lin = oneOf {
        if (fstChr lin) <> "?" then return "must begin with ?"
        let nTerm = nTerm lin
        if nTerm < 3 then return "must have 3 or more terms"
        let s = sndTerm lin
        if s |> isInLis ["EQ";"NE";"AND";"OR"] |> not then return "2nd term is operator, it must be [NE EQ OR AND]"
        if s |> isInLis ["EQ";"NE"] && (nTerm<>4) then return "when 2nd term is [EQ|NE], it must have 4 terms"
        }
    let chkSwLin1 prm sw lin = Some ""
    //--
    let vdtSwLy prm sw ly : bool*string[] =
        let l = ly |> IxLin.wh (pNot isRmkLin)
        let r1 = l |> IxLin.chkSrcLin chkSwLin
        let r2 = l |> IxLin.chkSrcLin (chkSwLin1 prm sw)
        let r3 = l |> IxLin.chkDupTermOne
        let r = Array.concat[r1;r2;r3]
        IxLin.srcPutRslt r ly

[<AutoOpen>]
module TpBk =
    let isSqLin  = fstTerm >> rmvPfx "?" >> isInLisI["drp";"sel";"seldis";"upd"]
    let isExprLin  = hasPfx "$"
    let isRmkLy  = sz >> eq 0
    let isPrmLy  = ayAll (hasPfx "%")
    let isSwLy   = ayAll (hasPfx "?")
    let isSqLy   = ayFstEleDft "" >> isSqLin
    let ly'ty ly = 
        oneOf {
            let ly = ly |> syRmvRmkLin
            if isRmkLy ly then return RmkBk
            if isSwLy ly then return SwBk
            if isPrmLy ly then return PrmBk
            if isSqLy ly then return SqBk
        } |> optDft ErBk

type TpBk(lyBk:LyBk) =
    inherit LyBk(lyBk)
    let ty' = lyBk.ly |> ly'ty
    member x.lyBk = lyBk
    member x.ty = ty'
    member x.ly = lyBk.ly
    member x.isEr = lyBk.ly |> ayAny has3Dash
    member x.vdt prm sw : bool*string[] = true,[||]

type SqTp(sqTp:string) =
    inherit LyTp("==",sqTp)
    let bkAy' = base.lyBkAy |> ayMap TpBk
    let sqBk'ly(b:TpBk) = b.ly
    member x.bkAy = bkAy'
    member x.bkAyWhTy ty = x.bkAy |> ayWh (fun(b:TpBk)->b.ty=ty)
    member x.tp = x.bkAy |> ayMap (fun(b:TpBk)->b.tp) |> jnSyCrLf
    member x.bkLy ty = x.bkAyWhTy ty |> ayFstEleOpt |> optMapDft sqBk'ly [||]
    member x.swLy  = x.bkLy SwBk
    member x.prmLy = x.bkLy PrmBk
    member private x.x ty = x.bkLy ty |> sdicByLy 
    member x.prmDic =  x.x PrmBk
    member x.swDic =  x.x SwBk
    member x.vdt = 
        let prm = x.prmDic
        let sw  = x.swDic
        let isErAy,sqBkAy = x.bkAy |> ayMap (fun(b:TpBk)->b.vdt prm sw) |> Array.unzip
        isErAy |> ayAny T,sqBkAy

[<AutoOpen>]
module EvlSqLin = 
    let sqLtStr'sqLtOpt a = Some Sel
    let sqLt lin = let f = fstTerm lin |> rmvPfx "?" in enmParseI<sqLt> f 
    let sqPfx ty =
        match ty with
        | Sel    -> "Select "
        | SelDis -> "Select Distinct "
        | Upd    -> "Update       "
        | Set    -> "   Set       "
        | Fm     -> "   From      "
        | Gp     -> "   Group By  "
        | Jn     -> "   Join      "
        | Left   -> "   Left Join "
        | WhBet | WhLik | WhIn | Wh
                 -> "   Where     "
        | AndBet | AndIn | AndLik | And
                 -> "   And       "
             
    let cxt'SEL expr rst = ""
    let cxt'GP expr rst = ""
    let cxt'SET expr rst = ""
    let sqRst ty expr rst =
        match ty with
        | Sel | SelDis -> cxt'SEL expr rst
        | Gp ->           cxt'GP expr rst
        | Set ->          cxt'SET expr rst
        | Jn | Left | Fm | Wh | And | Upd -> rst
        | WhBet | AndBet -> 
            let f = ""
            let a1 = ""
            let a2 = ""
            fmtQQ "? between ? and ?" [f;a1;a2]
        | WhIn | AndIn -> 
            let f = ""
            let inLis = ""
            fmtQQ "? in (?)" [f;inLis]
        | WhLik | AndLik -> 
            let f = ""
            let lik = ""
            fmtQQ "? like ?" [f;lik]
        
    let evlSqLin prm expr lin = 
        let fst,rst = shiftTerm lin
        let ty = sqLt fst
        let pfx = sqPfx ty
        let rst = sqRst ty expr rst
        pfx + rst
    
[<AutoOpen>]
module EvlSq =
    let hasPfxInLis pfxLis l = true
    let lin'UPD ly = 
        if sz ly = 0 then None else 
            let l0 = ly.[0]
            if(hasPfxInLis ["upd";"?upd"] l0) then Some l0 else None

    let lin'FM ly = ly |> Array.tryFind( hasPfx "fm")
    let sqLy_Oup_TblLin ly = 
        match lin'UPD ly with
        | Some l -> l
        | _ -> 
            match lin'FM ly with
            | Some l -> l
            | _ -> er "the {SqLy} should have [Upd | Fm] -line" [ly]
    let sqLy_Oup_TblNm ly = ly |> sqLy_Oup_TblLin |> sndTerm
    let Lcase s = ""
    let sqStmtTy ly = if sz ly = 0 then "" else ly.[0] |> fstTerm |> rmvPfx "?" |> Lcase
    let sqStmtSwKey ly = 
        let keyPfx = "?" + (sqStmtTy ly)
        ly |> sqLy_Oup_TblNm |> addPfx keyPfx
    let isSkipSq (sw:Sw) ly = sw.ContainsKey (sqStmtSwKey ly)
    let rmvOptTermInAy sw termAy = [||]
    let rmvOptTerm sw l = 
        if fstChr l <> "?" then l else
            match sqLt l with 
            | Sel | SelDis | Gp | Upd -> l |> rmvFstTerm |> splitLvs |> rmvOptTermInAy sw |> jnSySpc |> addPfx (fstTerm l)
            | _ -> l
    let sq_sqBk'evl prm sw (b:TpBk) = 
        if b.ty <> SqBk then er "given {Bk} should be SqBk" [b]
        let ly = b.ly |> syRmvEmpLin 
        if isSkipSq sw ly then "" else
            let expr = ly |> ayWh (hasPfx "$") |> sdicByLy
            let sqLy = ly |> ayWh (hasPfx "$"|>pNot)
            let evlLin = evlSqLin prm expr
            sqLy|> ayMap (rmvOptTerm sw) |> syRmvEmpLin |> ayMap evlLin |> jnSyCrLf

[<AutoOpen>]
module EvlSw =
    let evlT1 prm sw t1 =
        match fstChr t1 with
        | "?" -> dicVopt t1 sw |> optMap string
        | "%" -> dicVopt t1 prm
        | _ -> er "the given {T1_of_AndOrOperation} must have pfx-? or pfx-%" [t1]
    let evlT2 prm sw t2 = Some ""
    let evlT1T2(prm:Prm)(sw:Sw) op t1 t2 = 
        let v1 = evlT1 prm sw t1
        let v2 = evlT2 prm sw t2
        let f = match op with | SwOp.EQ -> eq | SwOp.NE -> ne | _ -> er "{SwOp} passed to this function should only be [ EQ | NE ]" [op]
        match zipOpt v1 v2 with None -> None | Some(v1,v2) -> Some(f v1 v2) 
    let evlBoolTerm(prm:Prm)(sw:Sw) t = 
        match fstChr t with
        | "?" -> dicVopt t sw  
        | "%" -> dicVopt t prm |> optMap System.Boolean.Parse
        | _ -> er "the given {boolTerm} must have pfx-? or pfx-%" [t]
    let evlBool'Ay op bool'Ay =
        let x1 f bool'Ay = if(opyAnyNone bool'Ay) then None else Some (bool'Ay |> f optVal )
        let andF = x1 ayAll
        let orF  = x1 ayAny
        let f = match op with
                | SwOp.OR  -> orF  
                | SwOp.AND -> andF  
                | _ -> er "{op} is unexpected" [op]
        f bool'Ay
    let evlLin prm sw swLin = 
        match swLin.terms with
        | SwTerms.T1T2(t1,t2) -> evlT1T2 prm sw (swLin.op) t1 t2
        | SwTerms.TermAy termAy -> termAy |> ayMap (evlBoolTerm prm sw)  |> evlBool'Ay (swLin.op) 
    let evlOnce swLy' prm sw =
        let b' = swLy' |> ayMap (evlLin prm sw)
        let oSwLy' = ayWhByOnyForNone b' swLy'
        let oIsEvled = b' |> ayAny isSome
        let ky = swLy' |> ayMap (fun(l:SwLin)->l.k)
        let kvAy = ayZip b' ky |> ayChoose (fun(b',k)->if(b'.IsSome) then Some(k,b'.Value) else None)
        let oSw = kvAy |> ayFold (fun(sw:Sw) kv -> sw.Add kv) sw
        oSwLy',oSw,oIsEvled
    let evlSwLy prm swLy =
        let swLy' = swLy |> ayMap (brk3Term>>swLin) 
        let rec e2 swLy' (sw:Sw) = 
            let swLy',sw,isEvled = evlOnce swLy' prm sw
            match swLy'.Length with
            | 0 -> sw
            | _ -> 
                match isEvled with
                | true -> e2 swLy' sw
                | _ -> er "{swLy'} still have data cannot further evl and some has evled into {Sw}" [swLy']
        e2 swLy' empSw

[<AutoOpen>]
module Evl =
    let sqBkAy'evl(a:SqTp) =
        let prm = a.prmDic 
        let sw  = a.swLy  |> evlSwLy prm 
        let evlSq = sq_sqBk'evl prm sw
        a.bkAyWhTy SqBk |> ayMap evlSq |> jnSyDblCrLf

[<AutoOpen>]
module Main =
    let sqTp'evl a = 
        let sqBkAy = SqTp(a)
        let isEr,sqBkAy' = sqBkAy.vdt 
        let newTp = sqBkAy.tp 
        let tp' = if newTp = a then None else Some(newTp)
        let sq' = if isEr then None else Some (sqBkAy'evl sqBkAy)
        optDo brwObj tp'
        { tp' = tp'; sq' = sq'}
    let rsltProcess (r:SqTpRslt) tpFt = 
        let sqFt = ffnRplExt ".sql" tpFt
        wrtStrOpt tpFt (r.sq')
        wrtStrOpt sqFt (r.tp')
        r
    let tpFtEvl ft = ftStr ft |> sqTp'evl |> rsltProcess
    let main = tpFtEvl
