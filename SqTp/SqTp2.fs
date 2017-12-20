namespace Lib.SqTp2
open Lib.Core
open Lib.Core.Types
open Lib.Tp
open Lib.LyVdt
open Lib.Dta
open Lib.Refl
open Lib.LyVdt
open Lib.SqTp2.Types
[<AutoOpen>]
module Emp =
    let empMsgs:msgs = []
    let empSw:sw = empBdic
    let empPrm:prm = empSdic
    let empEdic:edic = empSdic
[<AutoOpen>]
module Const =
    let sqFtExt = ".sql"
    let sqTpExt = ".txt"
    let sqTpPth:sqTpPth = @"C:\Users\user\Source\Repos\Sql3\SqTp\"
    let dftSqTpNm = "sqTp"
[<AutoOpen>]
module SqWh =
                     //   f  op1  op2 a  b
    let sqWhHlpLines = [  "wh $  XXXX"
                          "wh $F IN   STR $B"
                          "wh $F IN   NBR $B"
                          "wh $F BET  STR $A $B"
                          "wh $F BET  NBR $A $B"
                          "wh $F LIK  $A"
                       ] |> jnCrLf
    let sqWhDta(s:whDtaStr):WhDta =
        let f,a = shiftTerm s
        let op1,b = shiftTerm a
        let op2,c = shiftTerm b
        let d,e = brk1Spc c
        let op1 = op1.ToUpper()
        let op2 = op2.ToUpper()
        match f,op1,op2 with
        | "$", _    , _    -> WhConst a
        | _  , "LIK", _    -> WhLik   (f,b)
        | _  , "IN" ,"STR" -> WhInStr (f,c)
        | _  , "IN" ,"NBR" -> WhInNbr (f,c)
        | _  , "BET","STR" -> WhBetStr(f,d,e)
        | _  , "BET","NBR" -> WhBetNbr(f,d,e)
        | _  , _    , _    -> er "" []
    let sqWhExpandDta edic vdic whDta =
        let x a = keyDftVal a edic a
        let y a = keyDftVal a vdic a
        match whDta with
        | WhConst  a      -> WhConst (y a)
        | WhInStr (f,lvs) -> WhInStr (x f, y lvs)
        | WhInNbr (f,lvs) -> WhInNbr (x f, y lvs)
        | WhBetStr(f,a,b) -> WhBetStr(x f, y a, y b)
        | WhBetNbr(f,a,b) -> WhBetNbr(x f, y a, y b)
        | WhLik   (f,a)   -> WhLik   (x f, y a)
    let sqWhCxt whDta:sqpCxt =
        let in_str  f lvs = fmtQQ "? in (?)"              [f;splitLvs lvs |> syQuote "'" |> jnComma]
        let in_nbr  f lvs = fmtQQ "? in (?)"              [f;splitLvs lvs |> jnComma]
        let bet_str f a b = fmtQQ "? between '?' and '?'" [f;a;b]
        let bet_nbr f a b = fmtQQ "? between ? and ?"     [f;a;b]
        let lik     f a   = fmtQQ "? like '?'"            [f;a]
        let o =
            match whDta with
            | WhConst a -> a
            | WhInStr (f,lvs) -> in_str  f lvs
            | WhInNbr (f,lvs) -> in_nbr  f lvs
            | WhBetStr(f,a,b) -> bet_str f a b
            | WhBetNbr(f,a,b) -> bet_nbr f a b
            | WhLik   (f,a)   -> lik     f a
        o
[<AutoOpen>]
module VdtPrm = 
    let prmLinMsgs prmLin = 
        let l = prmLin
        ret {
            if(hasPfx "%" l|>not) then return ["must have pfx-(%)"]
            let nTerm = nTerm l
            if(hasPfx "%?" l) then 
                if nTerm <> 2 then return ["for %?, it should have only 2 terms"]
                let s = sndTerm l
                if (s<>"0" && s<>"1") then return ["for %?, 2nd term must be 0 or 1"]
            if nTerm <= 1 then return ["must have 2 or more terms"]
            return []
            }
    let prmLyVdt(prmLy:prmLy):vdtMsgs =
        let lyMsgs = prmLy |> ayMap prmLinMsgs
        lyMsgs,[]
    let prmLyVdtMsgs prmLy = lyVdt [prmLyVdt] true prmLy
[<AutoOpen>]
module VdtSql = 
    let sqLyVdt(sqLy:ly):vdtMsgs = [||],[]
    let sqLyVdtMsgs sqLy prmSdic swSdic= lyVdt [sqLyVdt] false sqLy
[<AutoOpen>]
module VdtSw =
    let andOrT1Vdt andOrT1 : string option =
        let t = andOrT1
        match fstChr t with
        | "?" | "%" -> None
        | _ -> Some(sprintf "T1-{%s} must have pfx-%s or pfx-$" t "%")

    //swLy |> ayMap (swLin_erTermLis_mustExist_in_Prm_or_Sw prm swSdic)
    let swLinMsgs(swSdic:swSdic)(prmSdic:prmSdic)(swLin:swLin):msgs=
        msgs {
            let k,op,termLvs = brk3Term swLin
            let termAy = splitLvs termLvs
            let op = toUpper op
            if fstChr k <> "?" then 
                yield "must begin with ?"
                return()
            if op |> isInLisI ["EQ";"NE";"AND";"OR"] |> not then 
                yield "2nd term is operator, it must be [NE EQ OR AND]"
                return()
            if op |> isInLisI ["AND";"OR"] then
                if sz termAy < 1 then
                    yield "when 2nd term is [AND|OR], it must have at least 3 terms"
                    return()
            else 
                if sz termAy <> 2 then
                    yield "when 2nd term is [EQ|NE], it must have 4 terms"
                    return()
                
                let er = (hasPfx "?" .&  notInDic swSdic) .| (hasPfx "%" .& notInDic prmSdic)       
                let erTermLis = termAy |> ayWh er |> ayToLis
                if lisIsEmpty erTermLis |> not then 
                    let s = jnSpc erTermLis
                    yield fmtQQ "Following terms must exist in {sw} or {prm}: [?]" [s]
                    return()
        }
    let swLyVdt(prmSdic:prmSdic)(swSdic:swSdic)(swLy:swLy):vdtMsgs = 
        let lyMsgs = swLy|>ayMap(swLinMsgs swSdic prmSdic)
        empVdtMsgs
    let swLyVdtMsgs swLy prmSdic swSdic = lyVdt [swLyVdt prmSdic swSdic] true swLy
[<AutoOpen>]
module QBk =
    let isRmk = sz >> eq 0
    let isMajPfx pfx ly = 
        let c1,c2 = syPfxCnt pfx ly
        c1>c2
    let isPrm = isMajPfx "%"
    let isSw  = isMajPfx "?"
    let isSq  = fstEleDft "" >> fstTerm >> rmvPfx "?" >> isInAyI(splitLvs "drp sel seldis upd")
    let lyQTy(ly:ly):qTy =         
        let l = ly |> lyRmvRmkLin
        ret {
            if isRmk l then return RmkBk
            if isSw  l then return SwBk
            if isPrm l then return PrmBk
            if isSq  l then return SqBk
            return ErBk
        }
[<AutoOpen>]
module VdtBk =
    let private x ly = ly|>ayMap(fun _->empMsgs)
    let qbkVdtMsgs(b:qbk)(prmSdic:prmSdic)(swSdic:swSdic):vdtMsgs = 
        let ly = b.ly
        match b.ty with
        | PrmBk -> prmLyVdtMsgs ly
        | SwBk  -> swLyVdtMsgs ly prmSdic prmSdic
        | SqBk  -> sqLyVdtMsgs ly swSdic prmSdic
        | ErBk  -> x ly,["These block is error due to it is not parameter block, not switch block, not remark block and not sql block"]
        | RmkBk -> x ly,[]
    let qbkVdtTp(prmSdic:prmSdic)(swSdic:swSdic)(b:qbk):vdtTp = 
        let vdtMsgs = qbkVdtMsgs b prmSdic swSdic
        toVdtTp(b.fstLinOpt)(b.ly)(vdtMsgs)
[<AutoOpen>]
module QBkAy =
    let qbkAyLyAy(ty:qTy):qbk[]->ly[] = 
        let eqTy(b:qbk) = b.ty = ty
        let ly(b:qbk) = b.ly
        ayWh eqTy >> ayMap ly
    let qbkAyPrmLyAy:qbk[]->prmLy[]= qbkAyLyAy PrmBk
    let private fstLy = seqHeadDft([||])
    let qbkAySqLyAy   = qbkAyLyAy SqBk
    let qbkAySwLyAy   = qbkAyLyAy SwBk
    let qbkAySwLy     = qbkAySwLyAy >> fstLy
    let qbkAyPrmLy    = qbkAyPrmLyAy >> fstLy 
    let qbkAyPrmSdic  = qbkAyPrmLy >> sdicBySdicLySkipDup
    let qbkAySwSdic   = qbkAySwLy >> sdicBySdicLySkipDup
    let qbkAyVdtTp(qbkAy:qbk[]) =
        let prmSdic = qbkAyPrmSdic qbkAy
        let swSdic = qbkAySwSdic qbkAy
        let isErAy,msgTpAy = qbkAy |> ayMap(qbkVdtTp prmSdic swSdic) |> ayUnzip
        let isEr = true // isErAy |> ayAny pT
        let msgTp = msgTpAy |> jnCrLf
        isEr,msgTp
[<AutoOpen>]
module EvlSw =
    let evlSwT1T2(sw:sw)(prm:prm)(op:eqNe)(t1:term)(t2:term) :bool option= 
        let v1 =
            match fstChr t1 with
            | "?" -> dicVopt t1 sw |> optMap string
            | "%" -> dicVopt t1 prm
            | _ -> er "the given {T1_of_AndOrOperation} must have pfx-? or pfx-%" [t1]
        let v2 =
            if t2="*Blank" then Some "" else
                match fstChr t2 with
                | "?" -> dicVopt t2 sw |> optMap string 
                | "%" -> dicVopt t2 prm
                | _ -> Some t2
        let f = match op with | EQ -> eq | NE -> ne 
        match zipOpt v1 v2 with None -> None | Some(v1,v2) -> Some(f v1 v2) 
    let evlSwBrk(sw:sw)(prm:prm)(swBrk:swBrk):bool option = 
        let bTerm_bOpt bTerm: bool option =
            let t = bTerm
            match fstChr t with
            | "?" -> dicVopt t sw  
            | "%" -> dicVopt t prm |> (optMap toBool)
            | _ -> er "the given {boolTerm} must have pfx-? or pfx-%" [t]
        let evlBoolAy (op:andOr) boolOptAy: bool option =
            if opyHasNone boolOptAy then None else
                let boolAy = boolOptAy |> ayMap(fun(b:bool option)->b.Value)
                let o = match op with
                        | andOr.OR  -> boolAyOr boolAy
                        | andOr.AND -> boolAyAnd boolAy
                Some o
        match swBrk.lgc with
        | Some(SwAndOr(andOr,termAy)) -> termAy |> ayMap bTerm_bOpt |> evlBoolAy andOr
        | Some(SwEqNe(eqNe,t1,t2)) -> evlSwT1T2 sw prm eqNe t1 t2
        | None -> None
    let parseSwLgcStr (swLgcStr:swLgcStr):swLgc option = 
        let op,t =
            let op,rst = shiftTerm swLgcStr
            let op = toUpper op
            let t = splitLvs rst
            op, t
        do
            match op with 
            | "EQ"|"NE" -> if sz t <> 2 then er "validation  error" []
            | _ -> ()
        match op with 
        | "AND" -> Some(SwAndOr(AND,t))
        | "OR" -> Some(SwAndOr(OR,t))
        | "EQ" -> Some(SwEqNe(EQ,t.[0],t.[1]))
        | "NE" -> Some(SwEqNe(NE,t.[0],t.[1]))
        | _ -> er "validation of {swLin} has er, {op} is not [AND|OR|EQ|NE]" [swLgcStr;op]
    let brkSwLin(swLin:swLin):swBrk =
        let k,swLgcStr = shiftTerm swLin
        let lgc = parseSwLgcStr swLgcStr
        {lin=swLin;k=k;lgc=lgc}
    let evlSwBrkAy prm sw swBrkAy: swBrk[]*sw*bool =
        let b' : bool option[] = swBrkAy |> ayMap (evlSwBrk sw prm)
        let oSwBrkAy = ayWhByOnyForNone b' swBrkAy
        let oIsEvled = b' |> ayAny isSome
        let oSw =
            let ky = swBrkAy |> ayMap (fun(l:swBrk)->l.k)
            let kvAy = ayZip b' ky |> ayChoose (fun(b',k)->if(b'.IsSome) then Some(k,b'.Value) else None)
            let oSw = kvAy |> ayFold (fun(sw:sw) kv -> sw.Add kv) sw
            oSw
        oSwBrkAy,oSw,oIsEvled
    let evlSw(prm:prm)(swLy:swLy):sw =
        let rec e2 sw cnt swBrkAy:sw = 
            let swBrkAy,sw,isEvled = evlSwBrkAy prm sw swBrkAy
            if ayIsEmpty swBrkAy then sw else
                match isEvled with
                | true -> e2 sw (cnt+1) swBrkAy
                | _ -> 
                    let toLin(a:swBrk) = a.lin
                    let lines =  swBrkAy |> ayMap toLin |> jnCrLf
                    er ("{swBrkAy} still have data cannot further evl." +
                            "{Sw} is switch-dictionary.  {swLy} {prm}")
                            [lines; sw; swLy; prm]
        swLy |>  ayMap brkSwLin |> e2 empBdic 0
[<AutoOpen>]
module SqLin =
    let private exprWdt elinesAy:exprWdt = elinesAy |> linesAyWdt |> incr 1
    let private elinesAy termAy edic:exprLines[] =
        if Array.isEmpty termAy then er "sqRst cannot be blank" [] 
        let ky = termAy |> syAddPfx "$"
        let elinesAy= ky |> ayMap (keyDftVal "" edic)
        elinesAy
    let private x rst exprdic =
        let termAy = splitLvs rst
        let elinesAy = elinesAy termAy exprdic
        let ew = exprWdt elinesAy
        termAy,elinesAy,ew
    let sqLinSel rst exprdic = 
        let termAy,elinesAy,ew = x rst exprdic
        let map(term,exprLines) = linesAddSfx ew term exprLines
        let o= elinesAy |> ayZip (syAlignL termAy) |> ayMap map |> jn ",\r\n" |> linesTab "" 6
        o
    let sqLinSet rst exprdic = 
        let termAy,elinesAy,ew = x rst exprdic
        let tw:termWdt = termAy |> ssWdt |> incr 3
        let map(term,exprLines) = linesTab term tw exprLines |> linesAddSfx ew ""
        let o = elinesAy |> ayZip (termAy |> syAlignL |> syAddSfx " = ") |> ayMap map |> jn ",\r\n" |> linesTab "" 6
        o
    let sqLinCond rst exprdic valdic = rst |> sqWhDta |> sqWhExpandDta exprdic valdic |> sqWhCxt
    let sqLinGp rst exprdic =
        let _,elinesAy,ew = x rst exprdic
        let o = elinesAy |> ayMap (linesAddSfx ew "") |> jn ",\r\n"
        o
    let sqLinTy fstTerm =
        if fstChr fstTerm = "?" then er "{sqLin-FstTerm} cannot begin with '?'" [fstTerm]
        unionParseI<sqpTy> fstTerm
    let sqLines lin exprDic valDic =
        let fst,rst = shiftTerm lin
        let ty = sqLinTy fst
        let lines =
            match ty with
            | Drp -> rst |> splitLvs |> ayMap(rplQ "Drop Table #?\r\n") |> jnCrLf
            | SelDis -> "Select Distict\r\n" + sqLinSel rst exprDic
            | Sel    -> "Select\r\n"         + sqLinSel rst exprDic
            | Upd    -> "Update       "   + rst + "\r\n"
            | Gp     -> "   Group By\r\n" + sqLinGp rst exprDic
            | Set    -> "   Set\r\n"      + sqLinSet rst exprDic
            | Fm     -> "   From      "   + rst + "\r\n"
            | Jn     -> "   Join      "   + rst + "\r\n"
            | Left   -> "   Left Join "   + rst + "\r\n"
            | Into   -> "   Into      "   + rst + "\r\n"
            | Wh     -> "   Where     "   + sqLinCond rst exprDic valDic
            | And    -> "   And       "   + sqLinCond rst exprDic valDic
        lines
[<AutoOpen>]
module SqStmt =
    let sqLyRmvOptTerm(sw:sw)(clnSqLy:clnSqLy):sqLy = 
        let (&&&) = pAnd
        let (|||) = pOr
        let nonQ = hasPfx "?" |> pNot
        let isKeep sw =
            let inSw = inDic sw
            let isTrue = keyVal sw >> (=) true
            inSw &&& isTrue ||| nonQ
        let rmvOptTerms rstTerm =
            let rstTermAy = rstTerm |> splitLvs |> ayWh(isKeep sw)
            if sz rstTermAy = 0 then er "{rstTerm} are all option terms and they are all removed.  See {sw}" [rstTerm;dicFmtLy sw]
            let rstTerm = rstTermAy |> ayMap (rmvPfx "?") |> jnSpc
            rstTerm
        let oneLin sqLin:lin option= // if {sqLin}-pfx is ?, the return lin may be blank
            let fst,rst = shiftTerm sqLin
            let fstTerm = rmvPfx "?" fst
            let isOptLin = fstTerm |> isInLisI ["sel";"seldis";"gp";"set"] // gp & set not have ?-pfx
            if isOptLin then Some(fstTerm + (rmvOptTerms rst)) else None
        clnSqLy |> ayChoose oneLin
    let sqLy2swKey(clnSqLy:sqLy):swKey = 
        let ty = clnSqLy |> fstEleDft "" |> fstTerm |> rmvPfx "?" |> toLower
        let tblNmLin = 
            match ty with
            | "sel" | "seldis" -> clnSqLy.[0] |> rmvFstTerm 
            | "into"           -> clnSqLy |> ayWhOne(hasPfx "into")
            | _ -> ""
        let o = 
            if tblNmLin = "" then "" else 
                let tblNm = tblNmLin |> sndTerm
                "?" + ty + tblNm
        o
    let isSkipEvl(sw:sw)(clnSqLy:clnSqLy):bool =
        let lin0 = clnSqLy |> fstEleDft ""
        let lin0fstChr = fstChr lin0
        let lin0isQ = lin0fstChr = "?"
        if lin0isQ then false else
            let swKey = sqLy2swKey clnSqLy
            (sw.ContainsKey swKey) && sw.Item(swKey) 
    let sqStmt prm sw clnSqLy:sqStmt =
        if isSkipEvl sw clnSqLy then "" else
            let exprLy,stmtLy = clnSqLy |> seqSplitAy (hasPfx "$")
            if Array.isEmpty stmtLy then er "{stmtLy} cannot empty ay" [clnSqLy]
            let edic = sdicBySdicLy exprLy
            let lines lin = sqLines lin edic prm
            let lines = stmtLy |> sqLyRmvOptTerm sw |> ayMap lines |> jnCrLf
            lines
[<AutoOpen>]
module SqStmts = 
    let sqStmtsOpt(qbkAy:qbk[])(isVdtEr) =
        if isVdtEr then None else
            let prm = qbkAyPrmSdic qbkAy
            let swLy = qbkAySwLy qbkAy
            let sw = evlSw prm swLy
            let stmt sqLy = SqStmt.sqStmt prm sw sqLy
            let sqStmts = qbkAy |> qbkAySqLyAy |> ayMap lyRmvRmkLin|> ayMap stmt |> jnCrLf
            Some sqStmts
[<AutoOpen>]
module SqTp =
    let dftEdic edicOpt = if isSome edicOpt then optVal edicOpt else empEdic
    let private mkQbk(bk:bk):qbk =
        let fstLinOpt = bk.fstLinOpt
        let ly = bk.ly
        let ty = lyQTy ly
        {fstLinOpt=fstLinOpt;ly=ly;ty=ty}
    let sqTpQbkAy(sqTp:sqTp) = sqTp |> tpBkAy "==" |> ayMap mkQbk
    let sqTpVdt =  sqTpQbkAy >> qbkAyVdtTp
    let sqTpIsEr sqTp = sqTp |> sqTpVdt |> fst
    let sqTpStmtsOpt sqTp = sqStmtsOpt(sqTpQbkAy sqTp)(sqTpIsEr sqTp)
    let sqTpEvl sqTp:runRslt =
        let isEr,msgTp = sqTpVdt sqTp
        let tpOpt = if msgTp=sqTp && not isEr then None else Some msgTp
        let stmtsOpt = sqStmtsOpt(sqTpQbkAy sqTp) isEr
        tpOpt,stmtsOpt
[<AutoOpen>]
module SqTpNm =
    let sqTpNmSqFt nm = sqTpPth + nm + sqFtExt
    let sqTpNmTpFt nm = sqTpPth + nm + sqTpExt
    let sqTpNmEvl nm = sqTpEvl(sqTpNmTpFt nm |> ftLines)
    let sqTpNmRun nm:runRslt  =
        let r = sqTpNmEvl nm
        let tpOpt,sqOpt = r
        strOptWrt(sqTpNmSqFt nm) sqOpt
        strOptWrt(sqTpNmTpFt nm) tpOpt
        r
    let sqTpNmEdt nm:edtRslt =
        let edt ft:ftEdtRslt = 
            do ftBrw ft
            ftEdtRslt.Done
        let tpFt = sqTpNmTpFt nm
        let sqFt = sqTpNmSqFt nm
        let ftEdtRslt = tpFt |> edt
        match ftEdtRslt with 
        | Done -> 
            let runRslt = sqTpNmRun nm 
            Saved(true,true,tpFt,sqFt)
        | ftEdtRslt.Cancel -> Cancel
    let dftSqTpNmEdt() = sqTpNmEdt dftSqTpNm
