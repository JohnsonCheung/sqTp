#nowarn "40" 
#nowarn "64" 
namespace Lib.SqTp
open Lib.Core
open Lib.Tp
open Lib.ChkLy
open Lib
type SqTpRslt = { tp': string option; sq' : string option }
module ZTyp =
    //------------------------------
    type SqTpBkTy = PrmBk|SwBk|SqBk|RmkBk|ErBk
    type SqLinTy = Sel|SelDis|Upd|Set|Fm|Gp|Jn|Left|Wh|And
    type SqTpBk = {ty:SqTpBkTy;mutable tpBk:Tp.Bk}
    //------------------------------
    type SwOp = AND|OR|EQ|NE
    type SwTerms = TermAy of string[] | T1T2 of string*string
    type Sw = Map<string,bool>
    type SwBrk = {lin:string;k:string;op:SwOp option;terms:SwTerms option}
    //------------------------------
    type Prm = Map<string,string>
    let empSw:Sw = Map.empty<string,bool>
    let empPrm:Prm = Map.empty<string,string>
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
    let evl(prm:Prm)(sw:Sw) op t1 t2 = 
        let v1 = AndOrTerm1.evl prm sw t1
        let v2 = AndOrTerm2.evl prm sw t2
        let f = match op with | SwOp.EQ -> eq | SwOp.NE -> ne | _ -> er "{SwOp} passed to this function should only be [ EQ | NE ]" [op]
        match zipOpt v1 v2 with None -> None | Some(v1,v2) -> Some(f v1 v2) 
module SwTerms =
    let toStr(swTerms:SwTerms):string = 
        match swTerms with
        | SwTerms.T1T2(t1,t2) -> t1 + " " + t2
        | SwTerms.TermAy termAy -> jnSpc termAy
    let make swOp termLvs = 
        let ay = splitLvs termLvs
        match swOp with
        | Some SwOp.AND | Some SwOp.OR -> 
            if ay.Length = 0 then failwith("sz of terms of AND OR switch line should be >0, but now is [" + string (sz ay) + "]")
            Some (SwTerms.TermAy ay)
        | Some SwOp.NE | Some SwOp.EQ ->
            if ay.Length <> 2 then failwith("sz of terms of EQ NE switch line should be 2, but now is [" + string (sz ay) + "]")
            Some(SwTerms.T1T2(ay.[0],ay.[1]))
        | _ -> None
module SwLin =
    let brk(swLin:string):SwBrk =
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
 module SqLin = 
    let ty lin:SqLinTy = let f = fstTerm lin |> rmvPfx "?" in enmParseI<SqLinTy> f 
    let rmvOptTermInAy sw termAy = [||]
    let rmvOptTerm sw l = 
        if fstChr l <> "?" then l else
            match ty l with
            |Sel|SelDis|Gp|Upd -> l |> rmvFstTerm |> splitLvs |> rmvOptTermInAy sw |> jnSpc |> addPfx (fstTerm l)
            | _ -> l
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
        lyChk linChkrLis bkChkrLis chkFstTermDup skipLinFun' sqLy
    let oupTblLin ly = 
        match updLin ly with
        | Some l -> l
        | _ -> 
            match fmLin ly with
            | Some l -> l
            | _ -> er "the {SqLy} should have [Upd | Fm] -line" [ly]
    let sqLy_Oup_TblNm ly = ly |> oupTblLin |> sndTerm
    let Lcase s = ""
    let sqStmtTy ly = if sz ly = 0 then "" else ly.[0] |> fstTerm |> rmvPfx "?" |> Lcase
    let sqStmtSwKey ly = 
        let keyPfx = "?" + (sqStmtTy ly)
        ly |> sqLy_Oup_TblNm |> addPfx keyPfx
    let chk_Expr_MustBe_AtEnd sqLy = Some ""
    let isSkip (sw:Sw) ly = sw.ContainsKey (sqStmtSwKey ly)
    let evl prm sw sqLy = 
        let ly = sqLy |> syRmvEmpLin 
        if isSkip sw ly then "" else
            let expr = ly |> ayWh (hasPfx "$") |> sdicByLy
            let sqLy = ly |> ayWh (hasPfx "$"|>pNot)
            let evlLin = SqLin.evl prm expr
            sqLy|> ayMap (SqLin.rmvOptTerm sw) |> syRmvEmpLin |> ayMap evlLin |> jnCrLf
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
    let isSqBk  = ayFstEleDft "" >> Lin.isSq
    let ty ly = 
        oneOf {
            let ly = ly |> syRmvRmkLin
            if isRmkBk ly then return RmkBk
            if isSwBk  ly then return SwBk
            if isPrmBk ly then return PrmBk
            if isSqBk  ly then return SqBk
        } |> optDft ErBk
module Bk =
    let tyEq ty (sqTpBk:SqTpBk) = sqTpBk.ty = ty
    let ly{ ty=_; tpBk={fstLinStr=_; ly=ly}} = ly
    let isEr tpBk = tpBk |> ly |> ayAny has3Dash
(*
module TpBk =
    let sqTpBk(tpBk:TpBk):SqTpBk =
        let ty = Ly.ty tpBk.ly
        {ty=ty;tpBk=tpBk}
*)
module SwBrk = 
    let lin(a:SwBrk) = a.lin
    let evl prm sw (swBrk:SwBrk) = 
        match swBrk.terms with
        | Some(SwTerms.T1T2(t1,t2)) -> AndOrOpT1T2.evl prm sw (swBrk.op.Value) t1 t2
        | Some(SwTerms.TermAy termAy) -> termAy |> ayMap (BoolTerm.evl prm sw)  |> BoolAy.evl (swBrk.op.Value) 
        | None -> None
module SwBrkAy =
    let lines =  ayMap SwBrk.lin >> jnCrLf
    let evl prm sw swBrkAy =
        let b' = swBrkAy |> ayMap (SwBrk.evl prm sw)
        let oSwBrkAy = ayWhByOnyForNone b' swBrkAy
        let oIsEvled = b' |> ayAny isSome
        let ky = swBrkAy |> ayMap (fun(l:SwBrk)->l.k)
        let kvAy = ayZip b' ky |> ayChoose (fun(b',k)->if(b'.IsSome) then Some(k,b'.Value) else None)
        let oSw = kvAy |> ayFold (fun(sw:Sw) kv -> sw.Add kv) sw
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
    let chk(prm)(sw)(swLy):string list[] =
        swLy |> ayMap (SwLinChk.Term_MustExist_in_Prm_or_Sw prm sw)
    let vdt(prm:Sdic) swLy:bool*string =
        let sw = sdicByLySkipDup swLy
        let linChkrLis =[SwLin.chk]
        let bkChkrLis = [chk prm sw]
        let chkFstTermDup = true
        let skipLinFun' = Some isRmkLin
        let isEr,tp =lyChk linChkrLis bkChkrLis chkFstTermDup skipLinFun' swLy
        isEr,tp
    let evl prm swLy =
        let swBrkAy = swLy |> ayMap SwLin.brk
        let rec e2 swBrkAy (sw:Sw) cnt = 
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
        //let r1 = l |> IxLin.chkSrcLin sqLin'chk
        //let r2 = l |> sqILinAy'chk'ExprMustBeAtEnd
        //let r = Array.concat[r1;r2]
        lyChk linChkrLis bkChkrLis true skipLinFun' prmLy
    let evl prmLy = empPrm
module ErLy =
    let vdt ly = true,jnCrLf ly
module BkAy =
    let tp bkAy = bkAy |> ayMap (fun i -> i.tpBk)  |> tpBkAyToStr
    let lyAy ty = ayWh (Bk.tyEq ty) >> ayMap(Bk.ly)
    let ly ty = lyAy ty >> ayFstEleDft [||]
    let sqLyAy = lyAy SqBk
    let swLy  = ly SwBk
    let prmLy = ly PrmBk
    let prm = prmLy >> sdicByLySkipDup
    let sw = swLy >> sdicByLySkipDup
    let vdt(bkAy:SqTpBk[]) : bool * string =
        let newBkAy = bkAy
        let prmLy = prmLy bkAy
        let swLy = swLy bkAy
        let prm = sdicByLySkipDup prmLy 
        let sw  = sdicByLySkipDup swLy
        let vdt (bk: SqTpBk) =
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
                let has3Dash = tp |> hasSs "---"
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
        //brwStr tp
        let sq' = if isEr then None else Some (BkAy.evl bkAy)
        //brwObj sq'
        let tp' = if sqTp=tp then None else Some tp
        { tp' = tp'; sq' = sq'}
[<AutoOpen>]
module A_Main =
    let sqTpEvl sqTp = Tp.evl sqTp
    let private rsltProcess (r:SqTpRslt) tpFt = 
        let sqFt = ffnRplExt ".sql" tpFt
        wrtStrOpt tpFt (r.sq')
        wrtStrOpt sqFt (r.tp')
        r
    let sqTpFtEvl ft = ftStr ft |> sqTpEvl |> rsltProcess