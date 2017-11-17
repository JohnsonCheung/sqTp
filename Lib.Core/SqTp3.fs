module rec Lib.SqTp3.SqTp3
(*
open Lib.Core
open Lib.Tp
open Lib.LyVdt
open Lib.Dta
open Lib.Refl
open Lib.LyVdt
open Lib.SqTp3.Types
type inp = {mutable tp:string}
let inp = {tp=""}
let isRmk = sz >> eq 0
let isMajPfx pfx ly = 
    let c1,c2 = syPfxCnt pfx ly
    c1>c2
let isPrm = isMajPfx "%"
let isSw  = isMajPfx "?"
let isSq  = fstEleDft "" >> fstTerm >> rmvPfx "?" >> isInAyI(splitLvs "drp sel seldis upd")
let lyTy ly:qTy = ret {
    let ly = ly |> ly_rmvRmkLin
    if isRmk ly then return RmkBk
    if isSw  ly then return SwBk
    if isPrm ly then return PrmBk
    if isSq  ly then return SqBk
    return ErBk
}
let noRmkLy = bk.ly |> ly_rmvRmkLin
let bk_rmvLy3DashRmk(bk:bk)=
    let no3DashLy = bk.ly|>ayMap lin_rmv3DashRmk
    bk.ly <- no3DashLy
    bk
let clnQBkAy:qBk[] = inp.tp |> tpBkAy "==" |> ayMap bk_rmvLy3DashRmk |> ayMap qBk
let sqLyAy = lyAy SqBk
let noRmkSqLyAy = sqLyAy |> ayMap ly_rmvRmkLin
let swLy  = ly SwBk
let prmLy = ly PrmBk
let prmSdic:sdic = prmLy |> sdicByLySkipDup
let prm = lazy(prmLy |> sdicByLy)
let swSdic:sdic = swLy |> sdicByLySkipDup
let sw = lazy(sdicByLy swLy)
let lyAy ty:ly[] = 
    let eqTy (qBk:qBk) = qBk.ty = ty
    let ly(bk:qBk) = bk.ly
    clnQBkAy |> ayWh eqTy |> ayMap ly
let ly ty = seqHeadDft([||])(lyAy ty) 
//type SqTpDta(tp:sqTp) =
//    let swLy_vdtMsgs i x:vdtMsgs=x2 swLy_vdtMsgs prmSdic (swLy i) x
//    let swLin_msgs i j x:msgs= x3 swLin_msgs prmSdic swSdic (swLin i j) x
let swLyAy:swLy[] = lyAy SwBk
let swLyI(i:ix):swLy = swLyAy.[i]
let swLin i (j:jx):swLin = (swLyI i).[j]
let empSw:sw = Map.empty<string,bool>
let empPrm:prm = empSdic
let sqpCxt(ty)(edic:sdic)(rst:sqRst):sqpCxt =
    do
        if isBlankStr rst then er "{rst} cannot be blank" []
    let t:sqTerm[] = splitLvs rst
    let (elines,ew):exprLines[]*exprWdt =
        if Array.isEmpty t then er "sqRst cannot be blank" []
        let ky = t |> syAddPfx "$"
        let elines= ky |> ayMap (keyVal edic)
        let ew = elines |> linesAyWdt |> incr 1
        elines,ew
    let xsel():sqpCxt =
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
    let sqpCxt =
        match ty with
        | Sel | SelDis -> xsel()
        | Gp ->           xgp()
        | Set ->          xset()
        | Jn | Left | Fm | Upd | Into -> rst
        | Wh | And ->     xwh()
    sqpCxt
let sqLinEvl(exprDic:edic)(sqLin:sqLin):lines =
    let fst,rst = shiftTerm sqLin
    let ty = unionParseI<sqpTy> fst
    let pfx =
        match ty with
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
    let cxt = sqpCxt ty exprDic rst
    let lines = pfx + cxt + "\r\n\r\n"
    lines
let sw = lazy(
    let aoT1T2_bOpt(sw:sw)(op:eqNe) t1 t2:bool option=
        let prm = prm.Force()
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
    let sw=
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
        e2 swBrkAy empSw 0
    sw
)
let noOptTermSqLy(clnSqLy:sqLy):sqLy = 
    let oneLin sqLin =
        let (&&&) = pAnd
        let (|||) = pOr
        let nonQ = hasPfx "?" |> pNot
        let isKeep sw =
            let inSw = inDic(sw.Force())
            let isTrue = keyVal sw >> (=) true
            inSw &&& isTrue ||| nonQ
        let isSelGpSet = sqLin |> fstTerm |> rmvPfx "?" |> isInLisI ["sel";"seldis";"gp";"set"] 
        if not isSelGpSet then sqLin else
            let fst,rst = shiftTerm sqLin 
            let fst = rmvPfx "?" fst
            let b = "sdf"
            let a = isKeep b
            let remain = rst |> splitLvs |> ayWh(isKeep sw)
            if sz remain = 0 then er "{sqLin}'s option term are all remove.  See {sw}" [sqLin;dicFmtLy sw]
            remain |> ayMap (rmvPfx "?") |> jnSpc |> addPfx (fst + " ")
    let o = clnSqLy |> ayMap oneLin |> ly_rmvBlankLin
    o
let sqStmt(clnSqLy) =
    let noOptTermSqLy = noOptTermSqLy clnSqLy
    let swKey():swKey = 
        let updLin =
            if Array.isEmpty clnSqLy then None else
                clnSqLy.[0] |> itmSome (hasPfxLis ["upd";"?upd"])
        let intoLin = 
            match updLin with
            | Some l -> l
            | _ ->
                let fmLin = Array.tryFind(hasPfx "fm") clnSqLy
                match fmLin with
                | Some l -> l
                | _ -> er "the {SqLy} should have [Upd | Fm] -line" [clnSqLy]
        let ty = clnSqLy |> fstEleDft "" |> fstTerm |> rmvPfx "?" |> toLower
        let tblNm = intoLin |> sndTerm
        let swKey = "?" + ty + tblNm
        swKey
    let (|SKIP|DROP|NORM|)() =
        let isDrp() =  clnSqLy |> ayMap fstTerm |> isAllEqTo "drp"
        let isSkip() = 
            let lin0 = clnSqLy |> fstEleDft ""
            if fstChr lin0 <> "?" then false else
                if (dicVopt (swKey()) sw) = Some false then false else true 
        seqChoose [isSkip;isDrp] [SKIP;DROP;NORM]
    let sqStmt = 
        match() with
        | SKIP -> ""
        | DROP -> 
            let toDrpStmt tblNm = "Drop Table #" + tblNm + "\r\n"
            clnSqLy.[0] |> splitLvs |> Array.skip 1 |> ayMap toDrpStmt |> jnCrLf
        | NORM -> 
            let exprLy,stmtLy = clnSqLy |> seqSplitAy (hasPfx "$")
            if Array.isEmpty stmtLy then er "{stmtLy} cannot empty ay" [clnSqLy]
            let lin = sqLinEvl(sdicByLy exprLy)
            noOptTermSqLy |> ayMap lin |> jnCrLf
    sqStmt
let sqLy_vdtMsgs(sqLy:sqLy) :vdtMsgs= 
    let sqLin_msgs(sqLin):msgs =
        let notSqLin   = sqLin |> fstTerm |> rmvPfx "?" |> isInAyI(splitLvs "drp sel seldis upd fm gp set into wh and left jn")
        let notExprLin = sqLin |> hasPfx "$"
        let msgs =
            msgs {
                if notSqLin && notExprLin then yield "line must be sq or expr"; return()
            }
        msgs
    let sqLy_vdtMsgs(ly:sqLy):vdtMsgs = 
        VdtMsgs.empty
    let chkr(sqLy:sqLy):vdtMsgs=
        //sqLy |> ayMap (fun i -> [i])
        VdtMsgs.empty
//      let sqLy_vdtMsgs_Expr_MustBe_AtEnd sqLy:lyMsgs = [||]
    let vdtMsgs = Ly.vdtMsgs [chkr] false sqLy
    vdtMsgs
let swLy_vdtMsgs(swLy:swLy):vdtMsgs =
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
        VdtMsgs.empty
    let swLy_vdtMsgs(ly:swLy) = Ly.vdtMsgs [swLy_chkr] true ly
    VdtMsgs.empty
let prmLy_vdtMsgs prmLy = 
    let prmLy_chkr:ly->vdtMsgs = fun(ly:ly)->
        (*
        in prmLin =oneOf {
        let lin = prmLin
        if(hasPfx "%" lin|>not) then return "must have pfx-(%)"
        if(hasPfx "%?" lin) then 
            if nTerm lin <> 2 then return "for %?, it should have only 2 terms"
            let s = sndTerm lin
            if (s<>"0" && s<>"1") then return "for %?, 2nd term must be 0 or 1"
        }
        *)
        VdtMsgs.empty
    Ly.vdtMsgs [prmLy_chkr] true prmLy
let erLy_vdtMsgs(ly:ly):vdtMsgs = 
    let endMsgs = [
        "These block is error due to it is not parameter block, not switch block, not remark block and not sql block"
        ]
    VdtMsgs.empty
let rmkLy_vdtMsgs(ly:ly):vdtMsgs = 
    //ly|>ayMap(fun _->[]),[]
    VdtMsgs.empty
let qBk_vdtTp(qBk:qBk):vdtTp =
    let ly = qBk.ly 
    let ty = qBk.ty 
    let fstLinOpt = qBk.fstLinOpt
    let vdtMsgs =
        match ty with
        | PrmBk -> prmLy_vdtMsgs ly
        | SwBk  -> swLy_vdtMsgs  ly
        | SqBk  -> sqLy_vdtMsgs  ly
        | ErBk  -> erLy_vdtMsgs  ly
        | RmkBk -> rmkLy_vdtMsgs ly
    let vdtTp = vdtMsgs |> VdtMsgs.vdtTp fstLinOpt ly
    vdtTp
let vdtTp = 
    let vdtTp =
        let isErAy,msgTpAy =
            clnQBkAy
            |>ayMap qBk_vdtTp
            |>Array.unzip
        let isEr = isErAy |> ayAny pT
//        let newQBlks = qBlks
//      newQBlks.clnQBkAy |> Array.iteri(fun(ix:int)(qBk:qBk)-> qBk.bk.ly <- msgTpAy.[ix])
//        let msgTp = newQBlks.tp
//        isEr,msgTp
        isEr,""
    vdtTp
let isEr = fst vdtTp
let msgTp = snd vdtTp
let sqOpt() = 
    if isEr then None else 
        let sqStmts = noRmkSqLyAy |> ayMap sqStmt |> jnCrLf
        Some(sqStmts)
let tpOpt = if inp.tp=msgTp then None else Some msgTp
let evl() = tpOpt,sqOpt
type SqTpNm(nm:sqTpNm) =
    let sqFtExt = ".sql"
    let tpFtExt = ".txt"
    let tpPth:sqTpPth = @"C:\Users\user\Source\Repos\Sql3\Lib.Core\"
    let sqFt = tpPth + nm + sqFtExt
    let tpFt = tpPth + nm + tpFtExt
    member x.evl:runRslt = tpFt |> ftLines |> sqTpEvl
    member x.run():runRslt  =
        let r = x.evl
        let tpOpt,sqOpt = r
        strOptWrt sqFt sqOpt
        strOptWrt tpFt tpOpt
        r
    member x.edt():edtRslt =
        let ft_Edt ft:ftEdtRslt = 
            do ftBrw ft
            ftEdtRslt.Done
        let ftEdtRslt = tpFt |> ft_Edt
        match ftEdtRslt with 
        | Done -> 
            (*
            let runRslt = tpFt |> ft_tp |> sqTp_run |> tee (runRslt_wrt tpFt sqFt)
            let tpOpt,sqOpt = runRslt
            let tpChanged = isSome tpOpt
            let sqChanged = isSome sqOpt
            Saved(tpChanged,sqChanged,tpFt,sqFt)
            *)
            Saved(true,true,tpFt,sqFt)
        | ftEdtRslt.Cancel -> Cancel
*)
let x = 1