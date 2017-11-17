#nowarn "40" 
#nowarn "64" 
namespace Lib.SqTp
(*
open Lib.Core
open Lib.Tp
open Lib.ChkLy
open Lib
type sqTpRslt = { tp': string option; sq' : string option }
module ZTyp =
    type swTerm1(s:string) = class end
    let a = swTerm1 "slkdfsdfl"
    let swTerm1 swTerm1 = a

    //------------------------------
    type swTerm = string
    type sqTpBkTy = PrmBk|SwBk|SqBk|RmkBk|ErBk
    type sqLinTy = Sel|SelDis|Upd|Set|Fm|Gp|Jn|Left|Wh|And
    type sqTpBk = {ty:sqTpBkTy;mutable tpBk:Tp.bk}
    //------------------------------
    type SwOp = AND|OR|EQ|NE
    type swTerms = TermAy of string[] | T1T2 of string*string
    type sw = Map<string,bool>
    type swSdic = sdic
    type swLy = string[]
    type swBrk = {lin:string;k:string;op:SwOp option;terms:swTerms option}
    //------------------------------
    type prm = Map<string,string>
    let empSw:sw = Map.empty<string,bool>
    let empPrm:prm = Map.empty<string,string>
open ZTyp
module Lin =
    let isSq = fstTerm >> rmvPfx "?" >> isInAyI(splitLvs "drp sel seldis upd fm gp set into wh and left jn")
    let isExpr = hasPfx "$"
module SwOpStr =
    let op (swOpStr:string) = 
        let op = 
            match swOpStr.ToUpper() with 
            | "AND" -> Some AND
            | "OR" -> Some OR
            | "EQ" -> Some EQ
            | "NE" -> Some NE
            | _ -> None
        op
module SwTerm =
    let chkExist(prm:prm)(sw:swSdic)(swTerm:swTerm) =
        let t = swTerm
        match fstChr t with
        | "?" -> dicVopt t sw |> optMap string
        | "%" -> dicVopt t prm
        | _ -> er "the given {T1_of_AndOrOperation} must have pfx-? or pfx-%" [t]
module AndOrTerm1 =
    let evl prm sw andOrTerm1 : string option =
        let t = andOrTerm1
        match fstChr t with
        | "?" -> dicVopt t sw |> optMap string
        | "%" -> dicVopt t prm
        | _ -> er "the given {T1_of_AndOrOperation} must have pfx-? or pfx-%" [t]
    let chk prm sw andOrTerm1 : string option =
        let t = andOrTerm1
        match fstChr t with
        | "?" | "%" -> None
        | _ -> Some(sprintf "T1-{%s} must have pfx-%s or pfx-$" t "%")
module BoolTerm =
    let evl prm sw boolTerm =
        let t = boolTerm
        match fstChr t with
        | "?" -> dicVopt t sw  
        | "%" -> dicVopt t prm |> (optMap toBool)
        | _ -> er "the given {boolTerm} must have pfx-? or pfx-%" [t]
module BoolAy =
    let evl op boolAy =
        let x1 f bool'Ay = if(opyAnyNone bool'Ay) then None else Some (bool'Ay |> f optVal )
        let andF = x1 ayAll
        let orF  = x1 ayAny
        let f = match op with
                | SwOp.OR  -> orF  
                | SwOp.AND -> andF  
                | _ -> er "{op} is unexpected" [op]
        f boolAy
module AndOrTerm2 =
    let evl prm sw andOrTerm2 : string option =
        let t = andOrTerm2
        if t="*Blank" then Some "" else
            match fstChr t with
            | "?" -> dicVopt t sw |> optMap string 
            | "%" -> dicVopt t prm
            | _ -> Some t
module AndOrOpT1T2 =
    let evl(prm:prm)(sw:sw) op t1 t2 = 
        let v1 = AndOrTerm1.evl prm sw t1
        let v2 = AndOrTerm2.evl prm sw t2
        let f = match op with | SwOp.EQ -> eq | SwOp.NE -> ne | _ -> er "{SwOp} passed to this function should only be [ EQ | NE ]" [op]
        match zipOpt v1 v2 with None -> None | Some(v1,v2) -> Some(f v1 v2) 
module SwTerms =
    let toStr(swTerms:swTerms):string = 
        match swTerms with
        | swTerms.T1T2(t1,t2) -> t1 + " " + t2
        | swTerms.TermAy termAy -> jnSpc termAy
    let make swOp termLvs = 
        let ay = splitLvs termLvs
        match swOp with
        | Some SwOp.AND | Some SwOp.OR -> 
            if ay.Length = 0 then failwith("sz of terms of AND OR switch line should be >0, but now is [" + string (sz ay) + "]")
            Some (swTerms.TermAy ay)
        | Some SwOp.NE | Some SwOp.EQ ->
            if ay.Length <> 2 then failwith("sz of terms of EQ NE switch line should be 2, but now is [" + string (sz ay) + "]")
            Some(swTerms.T1T2(ay.[0],ay.[1]))
        | _ -> None
module SwLin =
    let brk(swLin:string):swBrk =
        let k,opStr,rst = brk3Term swLin
        let op = SwOpStr.op opStr
        let terms = SwTerms.make op rst
        {lin=swLin;k=k;op=op;terms=terms}
    let chk swLin = oneOf {
        let lin = swLin
        if (fstChr lin) <> "?" then return "must begin with ?"
        let nTerm = nTerm lin
        if nTerm < 3 then return "must have 3 or more terms"
        let s = (sndTerm lin).ToUpper()
        if s |> isInLis ["EQ";"NE";"AND";"OR"] |> not then return "2nd term is operator, it must be [NE EQ OR AND]"
        if s |> isInLis ["EQ";"NE"] && (nTerm<>4) then return "when 2nd term is [EQ|NE], it must have 4 terms"
        }
module SqLinTy =
    let pfx ty =
        match ty with
        | Sel    -> "Select "
        | SelDis -> "Select Distinct "
        | Upd    -> "Update       "
        | Set    -> "   Set       "
        | Fm     -> "   From      "
        | Gp     -> "   Group By  "
        | Jn     -> "   Join      "
        | Left   -> "   Left Join "
        | Wh     -> "   Where     "
        | And    -> "   And       "
module SqLinRst =
    let selCxt expr rst = ""
    let gpCxt expr rst = ""
    let setCxt expr rst = ""
    let tyCxt ty expr rst =
        match ty with
        | Sel | SelDis -> selCxt expr rst
        | Gp ->           gpCxt expr rst
        | Set ->          setCxt expr rst
        | Jn | Left | Fm | Upd -> rst
        | Wh | And ->
            let op1,op2,rst1 = brk3Term rst
            match op1.ToUpper() with 
            | "IN" ->
                let fmt = "%s in (%s)"
                let lis =
                    match op2 with
                    | "STR" -> splitLvs rst |> syQuote "\"" |> jnComma
                    | "NBR" -> splitLvs rst |> jnComma
                    | _ -> er "{op2} should be STR or NBR" [op2]
                let f,a1,a2 = brk3Term rst1
                sprintf "%s in (%s)" op2 rst1
            | "BET" -> 
                let fmt = 
                    match op2 with
                    | "STR" -> sprintf "%s between \"%s\" and \"%s\""
                    | "NBR" -> sprintf "%s between %s and %s"
                    | _ -> er "{op2} should be STR or NBR" [op2]
                let f,a1,a2 = brk3Term rst
                fmt f a1 a2
            | "LIK" -> sprintf "%s like \"%s\"" op2 rst1
            | _ -> er "{op2} of {rst} is invalid.  Valid op2 is IN BET LIK" [op2;rst] 
module TermAy =
    let rmvOptTerm sw termAy =
        let (&&&) = pAnd
        let pfxQ = hasPfx "?"
        let inDic = inDic sw
        let isFalse = keyVal sw >> (=) false
        termAy |> ayWh (pfxQ &&& inDic &&& isFalse)
module SqLin = 
    let ty lin:sqLinTy = let f = fstTerm lin |> rmvPfx "?" in enmParseI<sqLinTy> f 
    let rmvOptTerm sw sqLin = 
        if fstChr sqLin <> "?" then sqLin else
            let fst,rst = shiftTerm sqLin 
            rst |> splitLvs |> TermAy.rmvOptTerm sw |> jnSpc |> addPfx fst
    let chk sqLin =
        let a =
            shortCut {
                if Lin.isSq sqLin then return! None
                if Lin.isExpr sqLin then return! None
                return(Some "line must be sq or expr")
            }
        if isNone a then failwith "shortCut is shorted" else optVal a
    let evl prm expr lin = 
        let fst,rst = shiftTerm lin
        let ty = ty fst
        let pfx = SqLinTy.pfx ty
        let rst = SqLinRst.tyCxt ty expr rst
        pfx + rst
module SqDrpLin =
    let evl sqDrpLin = ""
module SqLy =
    let updLin sqLy = 
        if Array.isEmpty sqLy then None else
            sqLy.[0] |> itmSome (hasPfxLis ["upd";"?upd"])
    let fmLin = Array.tryFind( hasPfx "fm")
    let chk prm sw sqLy= sqLy |> ayMap (fun i -> [i])
    let vdt prm sw sqLy = 
        let linChkrLis = [SqLin.chk]
        let bkChkrLis = [] // [ chk prm sw ]
        let chkFstTermDup = false
        let skipLinFun' = Some isRmkLin
        let chkr = linChkrLis,bkChkrLis,chkFstTermDup,skipLinFun'
        chkLy chkr sqLy
    let oupTblLin ly = 
        match updLin ly with
        | Some l -> l
        | _ -> 
            match fmLin ly with
            | Some l -> l
            | _ -> er "the {SqLy} should have [Upd | Fm] -line" [ly]
    let sqLy_Oup_TblNm ly = ly |> oupTblLin |> sndTerm
    let Lcase s = ""
    let sqStmtTy clnSqLy = clnSqLy |> fstEleDft "" |> fstTerm |> rmvPfx "?" |> Lcase
    let sqStmtSwKey clnSqLy = 
        let keyPfx = "?" + (sqStmtTy clnSqLy)
        clnSqLy |> sqLy_Oup_TblNm |> addPfx keyPfx
    let chk_Expr_MustBe_AtEnd sqLy = Some ""
    let isDrp clnSqLy =  clnSqLy |> fstEleDft "" |> hasPfxI "drp"
    let isSkip (sw:sw) clnSqLy = 
        let lin0 = clnSqLy |> fstEleDft ""
        if fstChr lin0 <> "?" then false else
            let key = clnSqLy |> sqStmtSwKey
            if (dicVopt key sw) = Some false then false else true 
    let choose cond lis = 
        let p(cond,v) = if(cond()) then Some v else None
        List.zip (cond@[turnT]) lis |> List.pick p
    let (|SKIP|DROP|NORM|)(sw,clnSqLy) =
        let isSkip() = isSkip sw clnSqLy
        let isDrp()  = isDrp clnSqLy
        choose [isSkip;isDrp] [SKIP;DROP;NORM]
    let aySplit p ay = 
        let f (t,f) i = if p i then (t@[i],f) else (t,f@[i])
        let toAy(a,b) = (lisToAy a),(lisToAy b)
        ay |> ayFold f ([],[]) |> toAy
    let evl prm (sw:sw)(sqLy:ly) = 
        let clnSqLy = sqLy |> syRmvEmpLin 
        match(sw,clnSqLy) with
        | SKIP -> ""
        | DROP -> SqDrpLin.evl clnSqLy.[0]
        | NORM -> 
            let exprLy,stmtLy = clnSqLy |> aySplit (hasPfx "$")
            let expr = sdicByLy exprLy
            stmtLy |> ayMap (SqLin.rmvOptTerm sw) 
                   |> syRmvEmpLin 
                   |> ayMap (SqLin.evl prm expr)
                   |> jnCrLf
module PrmLin =
    let chk prmLin =oneOf {
        let lin = prmLin
        if(hasPfx "%" lin|>not) then return "must have pfx-(%)"
        if(hasPfx "%?" lin) then 
            if nTerm lin <> 2 then return "for %?, it should have only 2 terms"
            let s = sndTerm lin
            if (s<>"0" && s<>"1") then return "for %?, 2nd term must be 0 or 1"
        }
module Ly =
    let isRmkBk = sz >> eq 0
    let private isPfxBk pfx ly = 
        let c1,c2 = syPfxCnt pfx ly
        c1>c2
    let isPrmBk = isPfxBk "%"
    let isSwBk  = isPfxBk "?"
    let isSqBk  = fstEleDft "" >> Lin.isSq
    let ty ly = 
        oneOf {
            let ly = ly |> syRmvRmkLin
            if isRmkBk ly then return RmkBk
            if isSwBk  ly then return SwBk
            if isPrmBk ly then return PrmBk
            if isSqBk  ly then return SqBk
        } |> optDft ErBk
module Bk =
    let tyEq ty (sqTpBk:sqTpBk) = sqTpBk.ty = ty
    let ly{ ty=_; tpBk={fstLinStr=_; ly=ly}} = ly
    let isEr tpBk = tpBk |> ly |> ayAny has3Dash
(*
module TpBk =
    let sqTpBk(tpBk:TpBk):SqTpBk =
        let ty = Ly.ty tpBk.ly
        {ty=ty;tpBk=tpBk}
*)
module SwBrk = 
    let lin(a:swBrk) = a.lin
    let evl prm sw (swBrk:swBrk) = 
        match swBrk.terms with
        | Some(T1T2(t1,t2)) -> AndOrOpT1T2.evl prm sw (swBrk.op.Value) t1 t2
        | Some(TermAy termAy) -> termAy |> ayMap (BoolTerm.evl prm sw)  |> BoolAy.evl (swBrk.op.Value) 
        | None -> None
module SwBrkAy =
    let lines =  ayMap SwBrk.lin >> jnCrLf
    let evl prm sw swBrkAy =
        let b' = swBrkAy |> ayMap (SwBrk.evl prm sw)
        let oSwBrkAy = ayWhByOnyForNone b' swBrkAy
        let oIsEvled = b' |> ayAny isSome
        let ky = swBrkAy |> ayMap (fun(l:swBrk)->l.k)
        let kvAy = ayZip b' ky |> ayChoose (fun(b',k)->if(b'.IsSome) then Some(k,b'.Value) else None)
        let oSw = kvAy |> ayFold (fun(sw:sw) kv -> sw.Add kv) sw
        oSwBrkAy,oSw,oIsEvled
module SwTermLis =
    let chk_MustExist_in_Prm_or_Sw prm sw swTermLis : string list = 
        let f3 term : string option = 
            match fstChr term with
            | "?" -> if dicHasKey term sw then None else Some(fmtQQ "Term(?) not found in sw-dic" [term])
            | "%" -> if hasPfx "%?" term |> not then None else 
                        if dicHasKey term prm then None else Some(fmtQQ "Term(?) not found prm-dic" [term])
            | _ -> Some (fmtQQ "Term(?) must started with ? or %" [term])
        swTermLis |> lisMap f3  |> lisWh isSome |> lisMap optVal
module SwLinChk =
    let Term_MustExist_in_Prm_or_Sw(prm)(sw)(swLin) : string list =
        let _,_,rst = brk3Term swLin
        let termAy = splitLvs rst
        let x t dic dicNm = if isSome(dicVopt t dic) then [] else [sprintf "term(%s) not found in %s" t dicNm]
        let chkTerm t =
            match fstChr t with
            | "?" -> x t sw "sw"
            | "%" -> x t prm "prm" 
            | _   -> []
        termAy |> ayFold (fun o t -> o@(chkTerm t)) []
module SwLy =
    let chk(prm:prm)(swSdic:swSdic)(swLy:swLy):string list[] =
        swLy |> ayMap (SwLinChk.Term_MustExist_in_Prm_or_Sw prm swSdic)
    let vdt(prm:sdic) swLy:bool*string =
        let sw = sdicByLySkipDup swLy
        let linChkrLis =[SwLin.chk]
        let bkChkrLis = [chk prm sw]
        let chkFstTermDup = true
        let skipLinFun' = Some isRmkLin
        let chkr = linChkrLis,bkChkrLis,chkFstTermDup,skipLinFun'
        let isEr,tp =chkLy chkr swLy
        isEr,tp
    let evl prm swLy =
        let swBrkAy = swLy |> ayMap SwLin.brk
        let rec e2 swBrkAy (sw:sw) cnt = 
            let swBrkAy,sw,isEvled = SwBrkAy.evl prm sw swBrkAy
            match swBrkAy.Length with
            | 0 -> sw
            | _ -> 
                match isEvled with
                | true -> e2 swBrkAy sw (cnt+1)
                | _ -> er ("{swBrkAy} still have data cannot further evl." +
                          "{Sw} is switch-dictionary.  {swLy} {prm}")
                            [SwBrkAy.lines swBrkAy;sw; swLy; prm]
        e2 swBrkAy empSw 0
module PrmLy =
    let vdt prmLy : bool*string =
        let linChkrLis = [PrmLin.chk]
        let bkChkrLis = []
        let skipLinFun' = Some isRmkLin
        //let r1 = l |> 
        .chkSrcLin sqLin'chk
        //let r2 = l |> sqILinAy'chk'ExprMustBeAtEnd
        //let r = Array.concat[r1;r2]
        chkLy (linChkrLis,bkChkrLis,true,skipLinFun') prmLy
    let evl prmLy = sdicByLy prmLy
module ErLy =
    let vdt ly = true,jnCrLf ly
module BkAy =
    let tp bkAy = bkAy |> ayMap (fun i -> i.tpBk)  |> tpBkAyToLines
    let lyAy ty = ayWh (Bk.tyEq ty) >> ayMap(Bk.ly)
    let ly ty = lyAy ty >> fstEleDft [||]
    let sqLyAy = lyAy SqBk
    let swLy  = ly SwBk
    let prmLy = ly PrmBk
    let prm = prmLy >> sdicByLySkipDup
    let sw = swLy >> sdicByLySkipDup
    let vdt(bkAy:sqTpBk[]) : bool * string =
        let newBkAy = bkAy
        let prmLy = prmLy bkAy
        let swLy = swLy bkAy
        let prm = sdicByLySkipDup prmLy 
        let sw  = sdicByLySkipDup swLy
        let vdt (bk: sqTpBk) =
            let ly = bk.tpBk.ly 
            let ty = bk.ty 
            let isEr,tp =
                match ty with
                | PrmBk -> PrmLy.vdt        ly
                | SwBk  -> SwLy.vdt  prm    ly
                | SqBk  -> SqLy.vdt  prm sw ly
                | ErBk  -> ErLy.vdt         ly
                | RmkBk -> false,jnCrLf     ly
            do
                let has3Dash = tp |> hasSub "---"
                let no3Dash = not has3Dash
                let er = isEr && no3Dash || not isEr && has3Dash
                if er then failwith "logic error"
            isEr,tp
        let isErAy,lyAy = 
            seq {
                for j = 0 to (ub newBkAy) do 
                    yield (vdt newBkAy.[j])
            } |> Seq.toArray |> Array.unzip
        let isEr = isErAy |> ayAny pT
        for j = 0 to (ub newBkAy) do
            newBkAy.[j].tpBk.ly <- lyAy.[j] |> splitCrLf
        let newTp = tp newBkAy
        isEr,newTp
    let evl bkAy = 
        let prm       = bkAy      |> prmLy    |> PrmLy.evl
        let sw        = bkAy      |> swLy     |> SwLy.evl prm
        let sqLinesAy = bkAy      |> sqLyAy   |> ayMap (SqLy.evl prm sw) 
        let sqLines   = sqLinesAy |> jnCrLf
        sqLines
module Tp =
    let bkAy sqTp = 
        let mk bk = 
            let ty = Ly.ty bk.ly 
            {ty=ty;tpBk=bk}
        sqTp |> tpBrk "==" |> ayMap mk
    let evl sqTp = 
        let bkAy = bkAy sqTp
        let isEr,tp = BkAy.vdt bkAy
        let sq' = if isEr then None else Some (BkAy.evl bkAy)
        let tp' = if sqTp=tp then None else Some tp
        { tp' = tp'; sq' = sq'}
[<AutoOpen>]
module SqTp =
    let sqTpEvl sqTp = Tp.evl sqTp
    let private rsltProcess tpFt (r:sqTpRslt)  = 
        let sqFt = ffnRplExt ".sql" tpFt
        wrtStrOpt tpFt (r.sq')
        wrtStrOpt sqFt (r.tp')
        r
    let sqTpFtEvl(ft:ft) = ftLines ft |> sqTpEvl |> rsltProcess ft
*)