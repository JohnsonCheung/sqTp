namespace Lib.SqTp
module Dmy =
(*
open Lib.Core
open Lib.Tp
open Lib.LyChk
open Lib
type sqFt = ft
type sqTpFt = ft
type sqTp = tp
type sqStmts = lines
type sqRslt = { tp': sqTp option; sq' : sqStmts option }
module ZTyp =
    //------------------------------
    type swTerm = string
    type swT1 = string
    type swT2 = string
    //------------------------------
    type expr = sdic
    type exprLin = string
    //------------------------------
    /// expression terms, started with $
    type sqLin = lin
    type sqKey = term
    type sqRst = termLvs
    //---------------------------------
    type clnSqLy = ly
    type clnLy = ly
    type tpLy = ly
    type sqStmt = string
    type sqLy = ly
    type sqpPfx = string
    type sqpCxt = string
    type qTy = PrmBk|SwBk|SqBk|RmkBk|ErBk
    type sqpTy = Sel|SelDis|Upd|Set|Fm|Into|Gp|Jn|Left|Wh|And
    type qBk = {ty:qTy;mutable bk:bk}
    //------------------------------
    type swOp = AND|OR|EQ|NE
    type swTerms = TermAy of swTerm[] | T1T2 of swT1*swT2
    type sw = Map<string,bool>
    type swSdic = sdic
    type swLin = string
    type swKey = string
    type swLy = swLin[]
    type swBrk = {lin:swLin;k:swKey;op:swOp option;terms:swTerms option}
    //------------------------------
    type prm = sdic
    let empSw:sw = Map.empty<string,bool>
    let empPrm:prm = Map.empty<string,string>
open ZTyp
module LyTy =
    module H =
        let isRmkBk = sz >> eq 0
        let isPfxBk pfx ly = 
            let c1,c2 = syPfxCnt pfx ly
            c1>c2
        let isPrmBk = isPfxBk "%"
        let isSwBk  = isPfxBk "?"
        let isSqBk  = fstEleDft "" >> fstTerm >> rmvPfx "?" >> isInAyI(splitLvs "drp sel seldis upd")
    open H
    open ZTyp
    let lyTy ly = 
        oneOf {
            let ly = ly |> syRmvRmkLin
            if isRmkBk ly then return RmkBk
            if isSwBk  ly then return SwBk
            if isPrmBk ly then return PrmBk
            if isSqBk  ly then return SqBk
        } |> optDft ErBk
module Qbk =
    open Tp
    let qbkLy(qBk:qBk) = let {bk={ly=ly}} = qBk in ly
    let qbkyTp = ayMap(fun i->i.bk)>>lyChkr
    let qbkLyAy ty = 
        let qbkTyEq ty (qBk:qBk) = qBk.ty = ty
        ayWh (qbkTyEq ty) >> ayMap(qbkLy)
    let qbkyLy ty = qbkLyAy ty >> fstEleDft [||]
    let qbkySqLyAy = qbkLyAy SqBk
    let qbkySwLy  = qbkyLy SwBk
    let qbkyPrmLy = qbkyLy PrmBk
    let qbkyPrm = qbkyPrmLy >> sdicByLySkipDup
    let qbkySwSdic = qbkySwLy >> sdicByLySkipDup
module VdtSqLy =
    module H =
        open Lib.ChkLy
        let isSqLin = fstTerm >> rmvPfx "?" >> isInAyI(splitLvs "drp sel seldis upd fm gp set into wh and left jn")
        let isExprLin = hasPfx "$"
        let sqLyChkr(ly:ly):msg list[] = 
            [||]
            
            (*
            let a =
                shortCut {
                    if isSqLin sqLin then return! None
                    if isExprLin sqLin then return! None
                    return(Some "line must be sq or expr")
                }
            if isNone a then failwith "shortCut is shorted" else optVal a
            *)
        let chkSqLy prm sw sqLy= sqLy |> ayMap (fun i -> [i])
        let SqLy'chk_Expr_MustBe_AtEnd sqLy = Some ""
    open H
    let SqLy'vdt prm sw sqLy = 
        let chkrLis = [sqLyChkr]
        let chkFstTermDup = false
        chkLy chkrLis chkFstTermDup sqLy
module VdtSwLy =
    module H =
        let AndOrTerm1'chk prm sw andOrTerm1 : string option =
            let t = andOrTerm1
            match fstChr t with
            | "?" | "%" -> None
            | _ -> Some(sprintf "T1-{%s} must have pfx-%s or pfx-$" t "%")
        let SwTermLis'chk_MustExist_in_Prm_or_Sw prm sw swTermLis : string list = 
            let f3 term : string option = 
                match fstChr term with
                | "?" -> if dicHasKey term sw then None else Some(fmtQQ "Term(?) not found in sw-dic" [term])
                | "%" -> if hasPfx "%?" term |> not then None else 
                            if dicHasKey term prm then None else Some(fmtQQ "Term(?) not found prm-dic" [term])
                | _ -> Some (fmtQQ "Term(?) must started with ? or %" [term])
            swTermLis |> lisMap f3  |> lisWh isSome |> lisMap optVal
        let SwLinChk'Term_MustExist_in_Prm_or_Sw(prm)(sw)(swLin) : string list =
            let _,_,rst = brk3Term swLin
            let termAy = splitLvs rst
            let x t dic dicNm = if isSome(dicVopt t dic) then [] else [sprintf "term(%s) not found in %s" t dicNm]
            let chkTerm t =
                match fstChr t with
                | "?" -> x t sw "sw"
                | "%" -> x t prm "prm" 
                | _   -> []
            termAy |> ayFold (fun o t -> o@(chkTerm t)) []
        let SwLy'chk(prm:prm)(swSdic:swSdic)(swLy:swLy):string list[] =
            swLy |> ayMap (SwLinChk'Term_MustExist_in_Prm_or_Sw prm swSdic)
        let SwTerm'chkExist: prm->sw->swTerm->bool option= fun prm sw swTerm->
            let t = swTerm
            match fstChr t with
            | "?" -> inDic sw t |> some
            | "%" -> inDic prm t |> some
            | _ -> None // er "the given {T1_of_AndOrOperation} must have pfx-? or pfx-%" [t]
        let chkSwLy(ly:ly):msg list[] = [||]
            (*
            oneOf {
            let lin = swLin
            if (fstChr lin) <> "?" then return "must begin with ?"
            let nTerm = nTerm lin
            if nTerm < 3 then return "must have 3 or more terms"
            let s = (sndTerm lin).ToUpper()
            if s |> isInLis ["EQ";"NE";"AND";"OR"] |> not then return "2nd term is operator, it must be [NE EQ OR AND]"
            if s |> isInLis ["EQ";"NE"] && (nTerm<>4) then return "when 2nd term is [EQ|NE], it must have 4 terms"
            }
            *)
    open H
    let SwLy'vdt(prm:sdic) swLy:lyChkRslt =
        let sw = sdicByLySkipDup swLy
        let chkFstTermDup = true
        let chkrLis = [chkSwLy]
        let isEr,tp = lyChk chkrLis chkFstTermDup swLy
        isEr,tp
module VdtPrmLy =
    module H =
        let chkPrmLy(ly:ly):msg list[] = [||]
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
    open H
    let vdtPrmLy prmLy : lyChkRslt =
        let chkrLis = [chkPrmLy]
        let chkFstTermDup = true
        //let r1 = l |> IxLin.chkSrcLin sqLin'chk
        //let r2 = l |> sqILinAy'chk'ExprMustBeAtEnd
        //let r = Array.concat[r1;r2]
        chkLy chkrLis chkFstTermDup prmLy
module VdtErLy =
    let ErLy'vdt ly = true,jnCrLf ly
module VdtQbk =
    open VdtSwLy
    open VdtPrmLy
    open VdtErLy
    open VdtSqLy
    open Qbk
    open Lib.Core
    let vdtQbk(qBk:qBk[]) : lyChkRslt =
        let newQbk = qBk
        let prmLy = qbkyPrmLy qBk
        let swLy = qbkySwLy qBk
        let prm = sdicByLySkipDup prmLy 
        let sw  = sdicByLySkipDup swLy
        let vdt (qBk: qBk) =
            let ly = qBk.bk.ly 
            let ty = qBk.ty 
            let isEr,tp =
                match ty with
                | PrmBk -> vdtPrmLy        ly
                | SwBk  -> SwLy'vdt  prm    ly
                | SqBk  -> SqLy'vdt  prm sw ly
                | ErBk  -> ErLy'vdt         ly
                | RmkBk -> false,jnCrLf     ly
            do
                let has3Dash = tp |> hasSub "---"
                let no3Dash = not has3Dash
                let er = isEr && no3Dash || not isEr && has3Dash
                if er then failwith "logic error"
            isEr,tp
        let isErAy,lyAy = 
            seq {
                for j = 0 to (ub newQbk) do 
                    yield (vdt newQbk.[j])
            } |> Seq.toArray |> Array.unzip
        let isEr = isErAy |> ayAny pT
        for j = 0 to (ub newQbk) do
            newQbk.[j].bk.ly <- lyAy.[j] |> splitCrLf
        let newTp = qbkyTp newQbk
        isEr,newTp
module SqStmtSwKey =
    module H =
        let Lcase s = ""
        let SqLy'sqStmtTy clnSqLy = clnSqLy |> fstEleDft "" |> fstTerm |> rmvPfx "?" |> Lcase
        let SqLy'updLin sqLy = 
            if Array.isEmpty sqLy then None else
                sqLy.[0] |> itmSome (hasPfxLis ["upd";"?upd"])
        let SqLy'fmLin = Array.tryFind( hasPfx "fm")
        let SqLy'oupTblLin ly = 
            match SqLy'updLin ly with
            | Some l -> l
            | _ -> 
                match SqLy'fmLin ly with
                | Some l -> l
                | _ -> er "the {SqLy} should have [Upd | Fm] -line" [ly]
        let SqLy'oupTblNm ly = ly |> SqLy'oupTblLin |> sndTerm
    open H
    let sqStmtSwKey clnSqLy = 
        let keyPfx = "?" + (SqLy'sqStmtTy clnSqLy)
        clnSqLy |> SqLy'oupTblNm |> addPfx keyPfx
module RmvSqLinOptTerm =
    module H =
        let (&&&) = pAnd
        let (|||) = pOr
        let nonQ = hasPfx "?" |> pNot
        let isKeep sw =
            let inSw = inDic sw
            let isTrue = keyVal sw >> (=) true
            inSw &&& isTrue ||| nonQ
        let isQSelSetGp = fstTerm >> rmvPfx "?" >> isInLisI ["sel";"seldis";"gp";"set"] 
    open H
    open Lib.Dta
    let rmvSqLinOptTerm sw sqLin = 
        if isQSelSetGp sqLin |> not then sqLin else
            let fst,rst = shiftTerm sqLin 
            let fst = rmvPfx "?" fst
            let b = "sdf"
            let a = isKeep sw b
            let remain = rst |> splitLvs |> ayWh(isKeep sw)
            if sz remain = 0 then er "{sqLin}'s option term are all remove.  See {sw}" [sqLin;dicFmtLy sw]
            remain |> ayMap (rmvPfx "?") |> jnSpc |> addPfx (fst + " ")
module EvlSwLy =
    module H =
        let evlAndOrT1 prm sw andOrTerm1 : string option =
            let t = andOrTerm1
            match fstChr t with
            | "?" -> dicVopt t sw |> optMap string
            | "%" -> dicVopt t prm
            | _ -> er "the given {T1_of_AndOrOperation} must have pfx-? or pfx-%" [t]
        let evlBoolTerm prm sw boolTerm: bool option =
            let t = boolTerm
            match fstChr t with
            | "?" -> dicVopt t sw  
            | "%" -> dicVopt t prm |> (optMap toBool)
            | _ -> er "the given {boolTerm} must have pfx-? or pfx-%" [t]
        let evlBoolAy op boolAy: bool option =
            let x1 f bool'Ay = if(opyAnyNone bool'Ay) then None else Some (bool'Ay |> f optVal )
            let andF = x1 ayAll
            let orF  = x1 ayAny
            let f = match op with
                    | swOp.OR  -> orF  
                    | swOp.AND -> andF  
                    | _ -> er "{op} is unexpected" [op]
            f boolAy
        let evlAndOrT2 prm sw andOrTerm2 : string option =
            let t = andOrTerm2
            if t="*Blank" then Some "" else
                match fstChr t with
                | "?" -> dicVopt t sw |> optMap string 
                | "%" -> dicVopt t prm
                | _ -> Some t
        let evlT1T2(prm:prm)(sw:sw) op t1 t2:bool option= 
            let v1 = evlAndOrT1 prm sw t1
            let v2 = evlAndOrT2 prm sw t2
            let f = match op with | swOp.EQ -> eq | swOp.NE -> ne | _ -> er "{SwOp} passed to this function should only be [ EQ | NE ]" [op]
            match zipOpt v1 v2 with None -> None | Some(v1,v2) -> Some(f v1 v2) 
        let parseSwOp (swOpStr:string):swOp option = 
            let op = 
                match swOpStr.ToUpper() with 
                | "AND" -> Some AND
                | "OR" -> Some OR
                | "EQ" -> Some EQ
                | "NE" -> Some NE
                | _ -> None
            op
        let evlSwBrk prm sw (swBrk:swBrk) = 
            match swBrk.terms with
            | Some(T1T2(t1,t2)) -> evlT1T2 prm sw (swBrk.op.Value) t1 t2
            | Some(TermAy termAy) -> termAy |> ayMap (evlBoolTerm prm sw)  |> evlBoolAy (swBrk.op.Value) 
            | None -> None
        let mkSwTerms swOp termLvs = 
            let ay = splitLvs termLvs
            match swOp with
            | Some swOp.AND | Some swOp.OR -> 
                if ay.Length = 0 then failwith("sz of terms of AND OR switch line should be >0, but now is [" + string (sz ay) + "]")
                Some (swTerms.TermAy ay)
            | Some swOp.NE | Some swOp.EQ ->
                if ay.Length <> 2 then failwith("sz of terms of EQ NE switch line should be 2, but now is [" + string (sz ay) + "]")
                Some(swTerms.T1T2(ay.[0],ay.[1]))
            | _ -> None
        let brkSwLin(swLin:string):swBrk =
            let k,opStr,rst = brk3Term swLin
            let op = parseSwOp opStr
            let terms = mkSwTerms op rst
            {lin=swLin;k=k;op=op;terms=terms}
        let evlSwBrkAy prm sw swBrkAy =
            let b' = swBrkAy |> ayMap (evlSwBrk prm sw)
            let oSwBrkAy = ayWhByOnyForNone b' swBrkAy
            let oIsEvled = b' |> ayAny isSome
            let ky = swBrkAy |> ayMap (fun(l:swBrk)->l.k)
            let kvAy = ayZip b' ky |> ayChoose (fun(b',k)->if(b'.IsSome) then Some(k,b'.Value) else None)
            let oSw = kvAy |> ayFold (fun(sw:sw) kv -> sw.Add kv) sw
            oSwBrkAy,oSw,oIsEvled
        let SwTerms'toStr(swTerms:swTerms):string = 
            match swTerms with
            | swTerms.T1T2(t1,t2) -> t1 + " " + t2
            | swTerms.TermAy termAy -> jnSpc termAy
        let SwBrk'lin(a:swBrk) = a.lin
        let SwBrkAy'lines =  ayMap SwBrk'lin >> jnCrLf

    open H
    let evlSwLy prm swLy : sw=
        let swBrkAy = swLy |>  ayMap brkSwLin
        let rec e2(swBrkAy:swBrk[])(sw:sw) cnt = 
            let swBrkAy,sw,isEvled = evlSwBrkAy prm sw swBrkAy
            match swBrkAy.Length with
            | 0 -> sw
            | _ -> 
                match isEvled with
                | true -> e2 swBrkAy sw (cnt+1)
                | _ -> er ("{swBrkAy} still have data cannot further evl." +
                          "{Sw} is switch-dictionary.  {swLy} {prm}")
                            [SwBrkAy'lines swBrkAy;sw; swLy; prm]
        e2 swBrkAy empSw 0
module EvlSqLin =
    module H =
        type eTerm = string
        type sqTerm = string
        type exprLines = lines
        type edic = Map<eTerm,lines>
        type termWdt = int
        type exprWdt = int
        type sqpCxt = lines
        type sqpKey = term  /// always have width of 10 char
        open Lib.Refl.Union
        let x(d:edic)(r:sqRst):sqTerm[]*exprLines[]*exprWdt =
            let t = splitLvs r
            if Array.isEmpty t then er "sqRst cannot be blank" []
            let ky = t |> syAddPfx "$"
            let elines:exprLines[]= ky |> ayMap (keyVal d)
            let w = elines |> linesAyWdt |> incr 1
            t,elines,w
        let xsel edic rst = 
            let t,elines,ew = x edic rst
            let map(term,exprLines) = linesAddSfx ew term exprLines
            let o:sqpCxt = elines |> ayZip (syAlignL t) |> ayMap map |> jn ",\r\n" |> linesTab "" 6
            o
        let xset edic rst =
            let t,elines,ew = x edic rst
            let tw:termWdt = t |> ssWdt |> incr 3
            let map(term,exprLines) = linesTab term tw exprLines |> linesAddSfx ew ""
            let o:sqpCxt = elines |> ayZip (t |> syAlignL |> syAddSfx " = ") |> ayMap map |> jn ",\r\n" |> linesTab "" 6
            o
        let xwh expr rst = 
            let op1,op2,rst1 = brk3Term rst
            let o:sqpCxt =
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
        let xgp edic rst = 
            let _,exprLinesAy,ew = x edic rst
            let o:sqpCxt = exprLinesAy |> ayMap (linesAddSfx ew "") |> jn ",\r\n"
            o
        let sqpTy(t:sqpKey):sqpTy = unionParseI<sqpTy> t
        let sqpPfx ty:sqpPfx =
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
        let sqpCxt ty edic (rst:sqRst) =
            if isBlankStr rst then er "{rst} cannot be blank" []
            match ty with
            | Sel | SelDis -> xsel edic rst
            | Gp ->           xgp edic rst
            | Set ->          xset edic rst
            | Jn | Left | Fm | Upd | Into -> rst
            | Wh | And ->     xwh edic rst

    open H
    let evlSqDrp sqDrpLin = 
        let toDrpStmt tblNm = "Drop Table #" + tblNm + "\r\n"
        sqDrpLin |> splitLvs |> Array.skip 1 |> ayMap toDrpStmt |> jnCrLf
    let evlSqLin prm expr lin:lines = 
        let fst,rst = shiftTerm lin
        let ty = sqpTy fst
        let pfx = sqpPfx ty
        let cxt = sqpCxt ty expr rst
        pfx + cxt + "\r\n\r\n"
module EvlSqLy = 
    open SqStmtSwKey
    module H =
        let SqLy'isDrp clnSqLy =  clnSqLy |> fstEleDft "" |> hasPfxI "drp"
        let SqLy'isSkip (sw:sw) clnSqLy = 
            let lin0 = clnSqLy |> fstEleDft ""
            if fstChr lin0 <> "?" then false else
                let key = clnSqLy |> sqStmtSwKey
                if (dicVopt key sw) = Some false then false else true 
        let SqLy'choose cond lis = 
            let p(cond,v) = if(cond()) then Some v else None
            List.zip (cond@[turnT]) lis |> List.pick p
        let (|SKIP|DROP|NORM|)(sw,clnSqLy) =
            let isSkip() = SqLy'isSkip sw clnSqLy
            let isDrp()  = SqLy'isDrp clnSqLy
            SqLy'choose [isSkip;isDrp] [SKIP;DROP;NORM]
        let aySplit p ay = 
            let f (t,f) i = if p i then (t@[i],f) else (t,f@[i])
            let toAy(a,b) = (lisToAy a),(lisToAy b)
            ay |> ayFold f ([],[]) |> toAy
    open EvlSqLin
    open RmvSqLinOptTerm
    open H
    let evlSqLy(prm:prm)(sw:sw)(clnSqLy:clnSqLy):sqStmt = 
        match(sw,clnSqLy) with
        | SKIP -> ""
        | DROP -> evlSqDrp clnSqLy.[0]
        | NORM -> 
            let exprLy,stmtLy = clnSqLy |> aySplit (hasPfx "$")
            let expr = sdicByLy exprLy
            if Array.isEmpty stmtLy then er "{stmtLy} cannot empty ay" [stmtLy]
            let optFixed = stmtLy |> ayMap (rmvSqLinOptTerm sw)
            let optFixed = optFixed |> syRmvEmpLin
            let evl = optFixed |> ayMap (evlSqLin prm expr) |> jnCrLf
            evl
module EvlQbk =
    open Qbk
    module H =
        let evlPrmLy prmLy = sdicByLy prmLy
        let clnQbk(qBk:qBk) = 
            qBk.bk.ly <- (qBk.bk.ly |> syRmvRmkLin)
            qBk
        let clnQbky qBky = qBky |> ayMap clnQbk
    open H
    open EvlSwLy
    open EvlSqLy
    let evlQbky(qBky:qBk[]) = 
        let clnQbky = clnQbky qBky
        let prm       = clnQbky |> qbkyPrmLy  |> evlPrmLy
        let sw        = clnQbky |> qbkySwLy   |> evlSwLy prm
        let sqLinesAy = clnQbky |> qbkySqLyAy |> ayMap (evlSqLy prm sw) 
        let sqLines   = sqLinesAy |> jnCrLf
        sqLines
module EvlTp =
    open LyTy
    open EvlQbk
    open VdtQbk
    module H =
        let sqTp'qBk sqTp:qBk[] = 
            let rmv3Dash{fstLinOpt=fstLinOpt;ly=ly}=
                let no3DashLy = ly|>ayMap rmv3DashRmk
                {fstLinOpt=fstLinOpt;ly=no3DashLy}
            let bk = sqTp |> brkTp "==" |> ayMap rmv3Dash
            let ty = 
                let bkLy(bk:bk) = bk.ly
                bk |> ayMap(bkLy>>lyTy)
            ayZip ty bk |> ayMap (fun(ty,bk) -> {ty=ty;bk=bk})
    open H
    let sqTpEvl sqTp = 
        let qBk = sqTp'qBk sqTp
        let isEr,tp = vdtQbk qBk
        let sq' = if isEr then None else Some(evlQbky qBk)
        let tp' = if sqTp=tp then None else Some tp
        { tp' = tp'; sq' = sq'}
    let toSqFt(tpFt:tpFt):sqFt = ffnRplExt ".sql" tpFt
    let sqTpFtEvl tpFt = 
        let wrt (r:sqRslt)  = 
            let sqFt = toSqFt tpFt
            wrtStrOpt sqFt (r.sq')
            wrtStrOpt tpFt (r.tp')
            r
        tpFt |> ftLines |> sqTpEvl |> wrt
module TstDta =
    let sqTpFt = @"C:\Users\user\Source\Repos\Sql3\Lib.Core\sqTp.Txt"
//    let sqTpFt = curPth + @"..\..\" + "sqTp.txt"
    let sqTp = ftLines sqTpFt
[<AutoOpen>]
module SqTp =
    open EvlTp
    open VdtPrmLy
    let sqTpEvl = sqTpEvl
    let sqTpFtEvl = sqTpFtEvl
    let toSqFt = toSqFt
*)
    let a = 1