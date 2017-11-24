namespace Lib.SqTp2.Types
open Lib.Core
open Lib.Tp
open Lib.LyVdt
open Lib.Dta
open Lib.Refl
open Lib.LyVdt
type sqEvlTy = NORM|DROP|SKIP
type swDic = bdic
type sqTpFt = ft
type sqTpNm = nm
type prm = sdic
type sw = dic<bool>
type prmLy = ly
type swLy = ly
type prmLyAy = prmLy[]
type swLyAy = swLy[]
type sqLin = lin
type sqLy = sqLin[]
type sqStmt = lines
type sqStmts = lines
type ftEdtRslt =Done|Cancel
type tpOpt = tp option
type sqOpt = sqStmts option
type runRslt = tpOpt*sqOpt
type tpNm = nm
type tpFt = ft
type sqFt = ft
type tpChanged = bool
type sqChanged = bool
type edtRslt = Cancel|Saved of tpChanged*sqChanged*tpFt*sqFt
type sqTpPth = pth
type sqTp = tp
type erTerm = term  // error term
type eTerm = string // expression term
type sqTerm = string
type exprLines = lines
type edic = Map<eTerm,lines>
type termWdt = int
type exprWdt = int
type sqpCxt = lines
type sqpKey = term  /// always have width of 10 char   
//------------------------------
type expr = sdic
type exprLin = string
type swLgcStr = string
//------------------------------
/// expression terms, started with $
type sqFmLin = sqLin
type sqUpdLin = sqLin
type sqIntoLin = sqLin
type sqKey = term
type sqRst = termLvs
//---------------------------------
type clnSqLy = ly
type clnLy = ly
type tpLy = ly
type sqpPfx = string
type qTy = PrmBk|SwBk|SqBk|RmkBk|ErBk
type sqpTy = Sel|SelDis|Upd|Set|Fm|Into|Gp|Jn|Left|Wh|And|Drp
//------------------------------
type prmSdic = sdic
type swSdic = sdic
type swLin = lin
type swKey = key
type andOr = AND|OR
type eqNe = EQ|NE
type swTerm = term
type swT1 = term
type swT2 = term
type swLgc = SwAndOr of andOr*swTerm[] | SwEqNe of eqNe*swT1*swT2
type swBrk = {lin:swLin;k:swKey;lgc:swLgc option}

namespace Lib.SqTp2
open Lib.Core
open Lib.Tp
open Lib.LyVdt
open Lib.Dta
open Lib.Refl
open Lib.LyVdt
open Lib.SqTp2.Types
type VPrm(prmLy:prmLy) =
    let prmLy_chkr(ly:ly):vdtMsgs =
        let linMsgs lin = ret {
            if(hasPfx "%" lin|>not) then return ["must have pfx-(%)"]
            if(hasPfx "%?" lin) then 
                if nTerm lin <> 2 then return ["for %?, it should have only 2 terms"]
                let s = sndTerm lin
                if (s<>"0" && s<>"1") then return ["for %?, 2nd term must be 0 or 1"]
            return []
            }
        let lyMsgs = ly |> ayMap linMsgs
        lyMsgs,[]
    let vdtMsgs_ = Ly.vdtMsgs [prmLy_chkr] true prmLy
    member x.vdtMsgs = vdtMsgs_
type VSq(sqLy:sqLy,sw:swSdic,prm:prmSdic) = 
    //let vdtMsgs = Ly.vdtMsgs [SqLin.chkr0;SqLin.chkr1] false sqLy
    //vdtMsgs
    let vdtMsgs_ = (sqLy |> ayMap(fun _->[])),[]
    member x.vdtMsgs = vdtMsgs_
type VSw(swLy:swLy,swSdic:sdic,prmSdic:sdic) =
    let aoT1_chk andOrTerm1 : string option =
        let t = andOrTerm1
        match fstChr t with
        | "?" | "%" -> None
        | _ -> Some(sprintf "T1-{%s} must have pfx-%s or pfx-$" t "%")

    //swLy |> ayMap (swLin_erTermLis_mustExist_in_Prm_or_Sw prm swSdic)
    let swLin_msgs(swLin:swLin):msgs=
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
    let swLy_chkr(swLy:swLy):vdtMsgs = 
        let lyMsgs = swLy|>ayMap(swLin_msgs)
        VdtMsgs.empVdtMsgs
    let swLy_vdtMsgs(ly:swLy) = Ly.vdtMsgs [swLy_chkr] true ly
    member x.vdtMsgs = [||],[]
type QBk(b:bk) =
    inherit bk(b.fstLinOpt,b.ly)
    let no3DashRmkLy_ = b.ly |> ayMap lin_rmv3DashRmk
    let isRmk = sz >> eq 0
    let isMajPfx pfx ly = 
        let c1,c2 = syPfxCnt pfx ly
        c1>c2
    let isPrm = isMajPfx "%"
    let isSw  = isMajPfx "?"
    let isSq  = fstEleDft "" >> fstTerm >> rmvPfx "?" >> isInAyI(splitLvs "drp sel seldis upd")
    let bkTy ly = ret {
            let ly = ly |> ly_rmvRmkLin
            if isRmk ly then return RmkBk
            if isSw  ly then return SwBk
            if isPrm ly then return PrmBk
            if isSq  ly then return SqBk
            return ErBk
        }
    let ty_ = bkTy b.ly
    member x.ty:qTy = ty_
    member x.no3DashRmkLy = no3DashRmkLy_
type VBk(b:QBk,prmSdic:prmSdic,swSdic:swSdic) =
    let zTy:qTy = b.ty
    let fstLinOpt = b.fstLinOpt
    let ly = b.ly
    let x() = ly|>ayMap(fun _->[])
    let zVdtMsgs =
        match zTy with
        | PrmBk -> VPrm(ly).vdtMsgs
        | SwBk  -> VSw(ly,swSdic,prmSdic).vdtMsgs
        | SqBk  -> VSq(ly,swSdic,prmSdic).vdtMsgs
        | ErBk  -> x(),["These block is error due to it is not parameter block, not switch block, not remark block and not sql block"]
        | RmkBk -> x(),[]
    let zVdtTp = VdtMsgs(zVdtMsgs).vdtTp fstLinOpt ly
    member x.vdtMsgs = zVdtMsgs
    member x.vdtTp = zVdtTp
    member x.isEr = fst zVdtTp
    member x.ty = zTy
type QBlks(tp:sqTp) =
    let zClnQBkAy = tp |> tpBkAy "==" |> ayMap QBk
    let lyAyOfTy ty:ly[] = 
        let eqTy (b:QBk) = b.ty = ty
        let ly(b:QBk) = b.ly
        zClnQBkAy |> ayWh eqTy |> ayMap ly
    let fstLy ty = seqHeadDft([||])(lyAyOfTy ty)
    let zSqLyAy = lyAyOfTy SqBk
    let zNoRmkSqLyAy = zSqLyAy |> ayMap ly_rmvRmkLin
    let zSwLy = fstLy SwBk
    let zSwLyAy = lyAyOfTy SwBk
    let zLyAy = zClnQBkAy|>ayMap(fun(b:QBk)->b.ly)
    let zPrmLy = fstLy PrmBk
    let zPrmSdic = zPrmLy |> sdicByLySkipDup
    let zSwSdic = zSwLy |> sdicByLySkipDup
    let zVdtAy = zClnQBkAy |> ayMap(fun(b:QBk) -> VBk(b,zPrmSdic,zSwSdic))
    let zVdtTp =         
        let isErAy,msgTpAy = zVdtAy |> ayMap(fun(v:VBk)->v.vdtTp) |> ayUnzip
        let isEr = isErAy |> ayAny pT
        let msgTp = ""
        isEr,msgTp
    member x.isVdtEr = fst zVdtTp
    member x.sqLyAy = zSqLyAy
    member x.erBkAy = zVdtAy |> Array.choose(fun(b:VBk)->if b.isEr then Some(b) else None)
    member x.noRmkSqLyAy = zNoRmkSqLyAy
    member x.swLy  = zSwLy
    member x.tp = tp
    member x.swLyAy = zSwLyAy
    member x.lyAy = zLyAy
    member x.prmLy = zPrmLy
    member x.prmSdic = zPrmSdic
    member x.prm():prm = zPrmLy |> sdicByLy
    member x.swSdic:sdic = zSwLy |> sdicByLySkipDup
    member x.clnQBkAy = zClnQBkAy
    member x.vdtAy = zVdtAy
    member x.vdtTp:vdtTp = zVdtTp
type SqTpDta(tp:sqTp) =
//    let swLy_vdtMsgs i x:vdtMsgs=x2 swLy_vdtMsgs prmSdic (swLy i) x
//    let swLin_msgs i j x:msgs= x3 swLin_msgs prmSdic swSdic (swLin i j) x
    let blks = QBlks(tp)
    let swLyAy:swLy[] = blks.swLyAy
    let swLy(i:ix):swLy = swLyAy.[i]
    let swLin i (j:jx):swLin = (swLy i).[j]
    let prmSdic:prmSdic = blks.prmSdic
    let swSdic:swSdic = blks.swSdic
type Sw(swLy:swLy,isVdtEr,prm:prm) =
    let aoT1T2_bOpt(sw:sw)(op:eqNe) t1 t2:bool option= 
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
    let swBrk_bOpt sw (swBrk:swBrk):bool option = 
        let bTerm_bOpt bTerm: bool option =
            let t = bTerm
            match fstChr t with
            | "?" -> dicVopt t sw  
            | "%" -> dicVopt t prm |> (optMap toBool)
            | _ -> er "the given {boolTerm} must have pfx-? or pfx-%" [t]
        let bAy_evl (op:andOr) bAy: bool option =
            let x1 f bool'Ay = if(opyAnyNone bool'Ay) then None else Some (bool'Ay |> f optVal )
            let andF = x1 ayAll
            let orF  = x1 ayAny
            let f = match op with
                    | andOr.OR  -> orF  
                    | andOr.AND -> andF  
            f bAy
        match swBrk.lgc with
        | Some(SwAndOr(andOr,termAy)) -> termAy |> ayMap bTerm_bOpt |> bAy_evl andOr
        | Some(SwEqNe(eqNe,t1,t2)) -> aoT1T2_bOpt sw eqNe t1 t2
        | None -> None
    let swLgcStr_parse (swLgcStr:swLgcStr):swLgc option = 
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
    let swLin_brk(swLin:swLin):swBrk =
        let k,swLgcStr = shiftTerm swLin
        let lgc = swLgcStr_parse swLgcStr
        {lin=swLin;k=k;lgc=lgc}
    let swBrkAy_sw sw swBrkAy: swBrk[]*sw*bool =
        let b' : bool option[] = swBrkAy |> ayMap (swBrk_bOpt sw)
        let oSwBrkAy = ayWhByOnyForNone b' swBrkAy
        let oIsEvled = b' |> ayAny isSome
        let oSw =
            let ky = swBrkAy |> ayMap (fun(l:swBrk)->l.k)
            let kvAy = ayZip b' ky |> ayChoose (fun(b',k)->if(b'.IsSome) then Some(k,b'.Value) else None)
            let oSw = kvAy |> ayFold (fun(sw:sw) kv -> sw.Add kv) sw
            oSw
        oSwBrkAy,oSw,oIsEvled
    let zSwDic =
        if isVdtEr then Map.empty<string,bool> else
            let swBrkAy = swLy |>  ayMap swLin_brk
            let rec e2 swBrkAy sw cnt:sw = 
                let swBrkAy,sw,isEvled = swBrkAy_sw sw swBrkAy
                match swBrkAy.Length with
                | 0 -> sw
                | _ -> 
                    match isEvled with
                    | true -> e2 swBrkAy sw (cnt+1)
                    | _ -> 
                        let toLin(a:swBrk) = a.lin
                        let lines =  swBrkAy |> ayMap toLin |> jnCrLf
                        er ("{swBrkAy} still have data cannot further evl." +
                                "{Sw} is switch-dictionary.  {swLy} {prm}")
                                [lines; sw; swLy; prm]
            e2 swBrkAy (Map.empty<string,bool>) 0
    member x.swDic = zSwDic
type SqpCxt(ty,rst:sqRst,?exprDic:edic) =
    let edic = if isSome exprDic then exprDic.Value else empSdic
    do
        if isBlankStr rst then er "{rst} cannot be blank" []
    let t:sqTerm[] = splitLvs rst
    let (elines,ew):exprLines[]*exprWdt =
        if Array.isEmpty t then er "sqRst cannot be blank" []
        let ky = t |> syAddPfx "$"
        let elines= ky |> ayMap (keyVal edic)
        let ew = elines |> linesAyWdt |> incr 1
        elines,ew
    let xsel() =
        let map(term,exprLines) = linesAddSfx ew term exprLines
        let o= elines |> ayZip (syAlignL t) |> ayMap map |> jn ",\r\n" |> linesTab "" 6
        o
    let xset():sqpCxt =
        let tw:termWdt = t |> ssWdt |> incr 3
        let map(term,exprLines) = linesTab term tw exprLines |> linesAddSfx ew ""
        let o = elines |> ayZip (t |> syAlignL |> syAddSfx " = ") |> ayMap map |> jn ",\r\n" |> linesTab "" 6
        o
    let xwh():sqpCxt = 
        let op1,op2,rst1 = brk3Term rst
        let o =
            match op1.ToUpper() with 
            | "$" -> rmvFstTerm rst
            | "IN" ->
                let fmt = "%s in (%s)"
                let lis =
                    match op2.ToUpper() with
                    | "STR" -> splitLvs rst |> syQuote "\"" |> jnComma
                    | "NBR" -> splitLvs rst |> jnComma
                    | _ -> er "{op2} should be STR or NBR" [op2]
                let f,a1,a2 = brk3Term rst1
                sprintf "%s in (%s)" op2 rst1
            | "BET" -> 
                let fmt = 
                    match op2.ToUpper() with
                    | "STR" -> sprintf "%s between \"%s\" and \"%s\""
                    | "NBR" -> sprintf "%s between %s and %s"
                    | _ -> er "{op2} should be STR or NBR" [op2]
                let f,a1,a2 = brk3Term rst
                fmt f a1 a2
            | "LIK" -> sprintf "%s like \"%s\"" op2 rst1
            | _ -> er "{op2} of {rst} is invalid.  Valid op2 is IN BET LIK" [op2;rst]  
        o
    let xgp() = 
        let o = elines |> ayMap (linesAddSfx ew "") |> jn ",\r\n"
        o
    let zCxt =
        match ty with
        | Sel | SelDis -> xsel()
        | Gp ->           xgp()
        | Set ->          xset()
        | Jn | Left | Fm | Upd | Into -> rst
        | Wh | And ->     xwh()
    member x.cxt:sqpCxt = zCxt
type SqLin(sqLin,?exprDic:edic) =
    let fst,rst = shiftTerm sqLin
    let zTy = unionParseI<sqpTy> fst
    let zPfx =
        match zTy with
        | Sel    -> "Select"
        | SelDis -> "Select Distinct"
        | Upd    -> "Update       "
        | Set    -> "   Set       "
        | Fm     -> "   From      "
        | Gp     -> "   Group By  "
        | Jn     -> "   Join      "
        | Left   -> "   Left Join "
        | Wh     -> "   Where     "
        | And    -> "   And       "
        | Into   -> "   Into      "
        | Drp    -> "Drop Table "
    let edic = if isSome exprDic then exprDic.Value else empSdic
    let zCxt = SqpCxt(zTy, rst, edic).cxt
    let zLines = zPfx + zCxt + "\r\n\r\n"
    member x.ty = zTy
    member x.cxt = zCxt
    member x.pfx = zPfx
    member x.lines = zPfx + zCxt
type NoOptTermSqLy(clnSqLy:sqLy,sw:swDic) = 
    let oneLin sqLin =
        let (&&&) = pAnd
        let (|||) = pOr
        let nonQ = hasPfx "?" |> pNot
        let isKeep sw =
            let inSw = inDic sw
            let isTrue = keyVal sw >> (=) true
            inSw &&& isTrue ||| nonQ
        let isSelGpSet = sqLin |> fstTerm |> rmvPfx "?" |> isInLisI ["sel";"seldis";"gp";"set"] 
        if not isSelGpSet then sqLin else
            let fst,rst = shiftTerm sqLin 
            let fst = rmvPfx "?" fst
            let b = "sdf"
            let a = isKeep sw b
            let remain = rst |> splitLvs |> ayWh(isKeep sw)
            if sz remain = 0 then er "{sqLin}'s option term are all remove.  See {sw}" [sqLin;dicFmtLy sw]
            remain |> ayMap (rmvPfx "?") |> jnSpc |> addPfx (fst + " ")
    let o = clnSqLy |> ayMap oneLin |> ly_rmvBlankLin
    member x.ly = o
type SqStmt(clnSqLy:sqLy,?prmOpt:prm,?swOpt:sw) =
    let prm = if isSome prmOpt then prmOpt.Value else empSdic
    let sw = if isSome swOpt then swOpt.Value else empBdic
    let swKey():swKey = 
        let ty = clnSqLy |> fstEleDft "" |> fstTerm |> rmvPfx "?" |> toLower
        let tblNmLin = 
            match ty with
            | "sel" | "seldis" -> clnSqLy.[0] |> rmvFstTerm 
            | "into"           -> clnSqLy |> ayWhOne(hasPfx "into")
            | _ -> ""
        let swKey = 
            if tblNmLin = "" then "" else 
                let tblNm = tblNmLin |> sndTerm
                "?" + ty + tblNm
        swKey
    let zEvlTy =
        let isDrp() =  clnSqLy |> ayMap fstTerm |> isAllEqTo "drp"
        let isSkip() = 
            let lin0 = clnSqLy |> fstEleDft ""
            if fstChr lin0 <> "?" then false else
                if (dicVopt (swKey()) sw) = Some false then false else true 
        seqChoose [isSkip;isDrp] [SKIP;DROP;NORM]
    let zSqStmt = 
        match zEvlTy with
        | SKIP -> ""
        | DROP -> 
            let toDrpStmt tblNm = "Drop Table #" + tblNm + "\r\n"
            clnSqLy.[0] |> splitLvs |> Array.skip 1 |> ayMap toDrpStmt |> jnCrLf
        | NORM -> 
            let exprLy,stmtLy = clnSqLy |> seqSplitAy (hasPfx "$")
            if Array.isEmpty stmtLy then er "{stmtLy} cannot empty ay" [clnSqLy]
            let edic = sdicByLy exprLy
            let lines sqLin = SqLin(sqLin,edic).lines 
            let lines = NoOptTermSqLy(stmtLy,sw).ly |> ayMap lines |> jnCrLf
            lines
    member x.evlTy = zEvlTy
    member x.sqStmt = zSqStmt
type SqStmts(blks:QBlks,?isVdtErOpt) =
    let dftF opt = if isSome opt then opt.Value else false
    let isVdtEr = dftF isVdtErOpt
    let sqOpt_ = 
        if isVdtEr then None else
        let prm = blks.prm()
        let swLy = blks.swLy
        let sw = Sw(swLy,isVdtEr,prm).swDic
        let stmt sqLy = SqStmt(sqLy,prm,sw).sqStmt
        let sqStmts = blks.noRmkSqLyAy |> ayMap stmt |> jnCrLf
        Some(sqStmts)
    member x.sqOpt = sqOpt_
type SqTp(tp:sqTp) = 
    let zBlks = QBlks(tp)
    let zVdtTp = zBlks.vdtTp
    let zIsEr = zVdtTp |> fst
    let zMsgTp = zVdtTp |> snd
    let zSqStmts = SqStmts(zBlks,zIsEr)
    member x.blks = zBlks
    member x.isEr = zIsEr
    member x.msgTp = zMsgTp
    member x.tpOpt = if tp = zMsgTp then None else Some zMsgTp
    member x.sqStmts = zSqStmts
    member x.sqOpt = zSqStmts.sqOpt
    member x.evl:runRslt = x.tpOpt, x.sqOpt
type SqTpNm(nm:sqTpNm) =
    let zSqExt = ".sql"
    let zTpExt = ".txt"
    let zTpPth:sqTpPth = @"C:\Users\user\Source\Repos\Sql3\Lib.Core\"
    let zSqFt = zTpPth + nm + zSqExt
    let zTpFt = zTpPth + nm + zTpExt
    let zSqTp = SqTp(zTpFt |> ftLines)
    member x.sqTp = zSqTp
    member x.evl:runRslt = zSqTp.evl
    member x.run():runRslt  =
        let r = x.evl
        let tpOpt,sqOpt = r
        strOptWrt zSqFt sqOpt
        strOptWrt zTpFt tpOpt
        r
    member x.edt():edtRslt =
        let ft_Edt ft:ftEdtRslt = 
            do ftBrw ft
            ftEdtRslt.Done
        let ftEdtRslt = zTpFt |> ft_Edt
        match ftEdtRslt with 
        | Done -> 
            (*
            let runRslt = tpFt |> ft_tp |> sqTp_run |> tee (runRslt_wrt tpFt sqFt)
            let tpOpt,sqOpt = runRslt
            let tpChanged = isSome tpOpt
            let sqChanged = isSome sqOpt
            Saved(tpChanged,sqChanged,tpFt,sqFt)
            *)
            Saved(true,true,zTpFt,zSqFt)
        | ftEdtRslt.Cancel -> Cancel
