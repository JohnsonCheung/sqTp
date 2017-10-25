#nowarn "40" 
#nowarn "64" 
namespace Lib.SqTp
open Lib.Core
open Lib.Tp
open Lib.ChkLy
[<AutoOpen>]
module ZTyp =
    //------------------------------
    type SqTpRslt = { tp': string option; sq' : string option }
    //------------------------------
    type SqTpBkTy = PrmBk|SwBk|SqBk|RmkBk|ErBk
    type SqLinTy = Sel|SelDis|Upd|Set|Fm|Gp|Jn|Left|Wh|WhBet|WhLik|WhIn|And|AndBet|AndIn|AndLik
    type SqTpBk = {ty:SqTpBkTy;lyBk:LyBk}
    //------------------------------
    type SwOp = AND | OR | EQ | NE
    type SwTerms = TermAy of string[] | T1T2 of string * string
    type Sw = Map<string,bool>
    type SwLinBrk = {k:string;op:SwOp;terms:SwTerms}
    //------------------------------
    type Prm = Map<string,string>
    let empSw:Sw = Map.empty<string,bool>
    let empPrm:Prm = Map.empty<string,string>
module SwOpTerm =
    let swOp swOpTerm = System.Enum.Parse(typeof<SwOp>,swOpTerm,true):?>SwOp
module prmLy =
    let vdt prmLy :bool*string[] =
        (*
        let l = x.ly |> IxLin.wh (pNot isRmkLin)
        let r1 = l |> IxLin.chkSrcLin swL'chk
        let r2 = l |> IxLin.chkSrcLin (chkSwLin1 prm sw)
        let r3 = l |> IxLin.chkDupTermOne
        let r = Array.concat[r1;r2;r3]
        *)
        true,[||]
module AndOrTerm1 =
    let evl prm sw andOrTerm1 : string option =
        let t = andOrTerm1
        match fstChr t with
        | "?" -> dicVopt t sw |> optMap string
        | "%" -> dicVopt t prm
        | _ -> er "the given {T1_of_AndOrOperation} must have pfx-? or pfx-%" [t]
module BoolTerm =
    let evl prm sw boolTerm =
        let t = boolTerm
        match fstChr t with
        | "?" -> dicVopt t sw  
        | "%" -> dicVopt t prm |> optMap System.Boolean.Parse
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
    let make swOp termLvs = 
        let ay = splitLvs termLvs
        match swOp with
        | AND | OR -> 
            if ay.Length <> 2 then failwith("sz of terms of EQ NE switch line should be 2, but now is [" + string (sz ay) + "]")
            SwTerms.TermAy ay
        | NE | EQ ->
            if ay.Length = 0 then  failwith("sz of terms of EQ NE switch line should be 2, but now is [" + string (sz ay) + "]")
            SwTerms.T1T2(ay.[0],ay.[1])
module SwLin =
    let op = sndTerm >> enmTryParseI<SwOp>
    let termAy = rmv2Terms >> splitLvs
    let evl prm sw swLin = 
        match swLin.terms with
        | SwTerms.T1T2(t1,t2) -> AndOrOpT1T2.evl prm sw (swLin.op) t1 t2
        | SwTerms.TermAy termAy -> termAy |> ayMap (BoolTerm.evl prm sw)  |> BoolAy.evl (swLin.op) 
    let swLinBrk(swLin:string):SwLinBrk =
        let sy = splitLvs swLin
        let k = sy.[0]
        let op = SwOpTerm.swOp sy.[1]
        let terms = SwTerms.make op sy.[2]
        {k=k;op=op;terms=terms}
    let chk swLin = oneOf {
        let lin = swLin
        if (fstChr lin) <> "?" then return "must begin with ?"
        let nTerm = nTerm lin
        if nTerm < 3 then return "must have 3 or more terms"
        let s = sndTerm lin
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
        | WhBet | WhLik | WhIn | Wh
                 -> "   Where     "
        | AndBet | AndIn | AndLik | And
                 -> "   And       "
module SqLinRst =
    let selCxt expr rst = ""
    let gpCxt expr rst = ""
    let setCxt expr rst = ""
    let tyCxt ty expr rst =
        match ty with
        | Sel | SelDis -> selCxt expr rst
        | Gp ->           gpCxt expr rst
        | Set ->          setCxt expr rst
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
module SqLin = 
    let ty lin:SqLinTy = let f = fstTerm lin |> rmvPfx "?" in enmParseI<SqLinTy> f 
    let rmvOptTermInAy sw termAy = [||]
    let rmvOptTerm sw l = 
        if fstChr l <> "?" then l else
            match ty l with 
            | Sel | SelDis | Gp | Upd -> l |> rmvFstTerm |> splitLvs |> rmvOptTermInAy sw |> jnSySpc |> addPfx (fstTerm l)
            | _ -> l
    let chk sqLin = Some ""
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

    let evl prm expr lin = 
        let fst,rst = shiftTerm lin
        let ty = ty fst
        let pfx = SqLinTy.pfx ty
        let rst = SqLinRst.tyCxt ty expr rst
        pfx + rst
module SqLy =
    let hasPfxInLis pfxLis l = true
    let updLin sqLy = 
        if sz sqLy = 0 then None else 
            let l0 = sqLy.[0]
            if(hasPfxInLis ["upd";"?upd"] l0) then Some l0 else None
    let vdt prm sw sqLy = true,""
    let fmLin sqLy = sqLy |> Array.tryFind( hasPfx "fm")
    let sqLy_Oup_TblLin ly = 
        match updLin ly with
        | Some l -> l
        | _ -> 
            match fmLin ly with
            | Some l -> l
            | _ -> er "the {SqLy} should have [Upd | Fm] -line" [ly]
    let sqLy_Oup_TblNm ly = ly |> sqLy_Oup_TblLin |> sndTerm
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
            sqLy|> ayMap (SqLin.rmvOptTerm sw) |> syRmvEmpLin |> ayMap evlLin |> jnSyCrLf
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
    let isSqLin  = fstTerm >> rmvPfx "?" >> isInLisI["drp";"sel";"seldis";"upd"]
    let isExprLin  = hasPfx "$"
    let isRmk  = sz >> eq 0
    let isPrm  = ayAll (hasPfx "%")
    let isSw   = ayAll (hasPfx "?")
    let isSq   = ayFstEleDft "" >> isSqLin
    let sqTpBkTy ly = 
        oneOf {
            let ly = ly |> syRmvRmkLin
            if isRmk ly then return RmkBk
            if isSw ly then return SwBk
            if isPrm ly then return PrmBk
            if isSq ly then return SqBk
        } |> optDft ErBk
module SqTpBk =
    let tyEq ty (sqTpBk:SqTpBk) = sqTpBk.ty = ty
    let ly{ty=_;lyBk={fstLinStr=_;ly=ly}} = ly
    let isEr tpBk = tpBk |> ly |> ayAny has3Dash
module LyBk =
    let sqTpBk(lyBk:LyBk):SqTpBk =
        let ty = Ly.sqTpBkTy lyBk.ly
        {ty=ty;lyBk=lyBk}
module SwLinBrkAy =
    let evl prm sw swLy =
        let b' = swLy |> ayMap (SwLin.evl prm sw)
        let oSwLy' = ayWhByOnyForNone b' swLy
        let oIsEvled = b' |> ayAny isSome
        let ky = swLy |> ayMap (fun(l:SwLinBrk)->l.k)
        let kvAy = ayZip b' ky |> ayChoose (fun(b',k)->if(b'.IsSome) then Some(k,b'.Value) else None)
        let oSw = kvAy |> ayFold (fun(sw:Sw) kv -> sw.Add kv) sw
        oSwLy',oSw,oIsEvled
module SwTermAy =
    let chk_MustExist_in_Prm_or_Sw prm sw swTermAy : string[] = 
        let f3 term : string option = 
            match fstChr term with
            | "?" -> if dicHasKey term sw then None else Some(fmtQQ "Term(?) not found in sw-dic" [term])
            | "%" -> if hasPfx "%?" term |> not then None else 
                        if dicHasKey term prm then None else Some(fmtQQ "Term(?) not found prm-dic" [term])
            | _ -> Some (fmtQQ "Term(?) must started with ? or %" [term])
        swTermAy |> ayMap f3  |> ayWh isSome |> ayMap optVal
module SwLyChk =
    let AndOrTerm_MustExist_in_Prm_or_Sw prm sw swLy : string[] list =
        let f1 swLin : string[] = SwLin.termAy swLin |> SwTermAy.chk_MustExist_in_Prm_or_Sw prm sw
        let f swLin :string[]= match SwLin.op swLin with Some AND | Some OR -> f1 swLin | _ -> [||]
        swLy |> ayMap f |> Array.toList
    let EqNeT1_MustExist_in_Prm_or_Sw prm sw swLy : string[] list = []
module SwLy =
    let vdt(prm:Sdic) swLy:bool*string =
        let chkLinFunLis =[]
        let chkBkFunLis = []
        let chkFstTermDup = true
        let skipLinFun' = Some isRmkLin
        lyChk chkLinFunLis chkBkFunLis chkFstTermDup skipLinFun' swLy

    let evl prm swLy =
        let swLinBrkAy = swLy |> ayMap SwLin.swLinBrk 
        let rec e2 swLinBrkAy (sw:Sw) = 
            let swLinBrkAy,sw,isEvled = SwLinBrkAy.evl prm sw swLinBrkAy
            match swLinBrkAy.Length with
            | 0 -> sw
            | _ -> 
                match isEvled with
                | true -> e2 swLinBrkAy sw
                | _ -> er "{swLy'} still have data cannot further evl and some has evled into {Sw}" [swLinBrkAy]
        e2 swLinBrkAy empSw
module PrmLy =
    open Lib.ChkLy
    let vdt prmLy : bool*string =
        let chkLinFunLis = []
        let chkBkFunLis = []
        let skipLinFun' = Some isRmkLin
        //let r1 = l |> IxLin.chkSrcLin sqLin'chk
        //let r2 = l |> sqILinAy'chk'ExprMustBeAtEnd
        //let r = Array.concat[r1;r2]
        lyChk chkLinFunLis chkBkFunLis true skipLinFun' prmLy
    let evl prmLy = empPrm
module SqTpBkAy =
    let lyAy ty = ayWh (SqTpBk.tyEq ty) >> ayMap(SqTpBk.ly)
    let ly ty = lyAy ty >> ayFstEleDft [||]
    let sqLyAy = lyAy SqBk
    let swLy  = ly SwBk
    let prmLy = ly PrmBk
    let vdt tpBkAy : bool*string option=
        let prmLy = prmLy tpBkAy
        let swLy = swLy tpBkAy
        let prm = sdicByLySkipDup prmLy 
        let sw  = sdicByLySkipDup swLy 
        let swIsEr,swTp = SwLy.vdt prm swLy
        let prmIsEr,prmTp = PrmLy.vdt prmLy
        let sqVdtRsltLis = tpBkAy |> sqLyAy |> ayMap (SqLy.vdt prm sw)
        true,Some ""
    let evl tpBkAy = 
        let prm = tpBkAy |> prmLy |> PrmLy.evl
        let sw  = tpBkAy |> swLy |> SwLy.evl prm
        let sqLinesAy = tpBkAy |> sqLyAy |> ayMap (SqLy.evl prm sw) 
        let sqLines = sqLinesAy |> jnSyCrLf
        sqLines
module SqTp =
    open Lib.Tp
    let evl sqTp = 
        let sqTpBkAy = sqTp |> tpBrk "==" |> ayMap LyBk.sqTpBk 
        let isEr,tp' = SqTpBkAy.vdt sqTpBkAy
        let sq' = if isEr then None else Some (SqTpBkAy.evl sqTpBkAy)
        optDo brwObj tp'
        { tp' = tp'; sq' = sq'}
[<AutoOpen>]
module A_Main =
    let sqTpEvl sqTp = SqTp.evl sqTp
    let private rsltProcess (r:SqTpRslt) tpFt = 
        let sqFt = ffnRplExt ".sql" tpFt
        wrtStrOpt tpFt (r.sq')
        wrtStrOpt sqFt (r.tp')
        r
    let sqTpFt'evl ft = ftStr ft |> sqTpEvl |> rsltProcess