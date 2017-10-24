#nowarn "40" 
#nowarn "64" 
namespace Lib.SqTp
open Lib
module IdxLin =
    type IdxLin = { linIdx: int; lin: string }
    type Rslt = { linIdx: int; msg: string }
    open Term
    open AyWh
    open StrHas
    open Quote
    open Dic
    open PfxSfx
    open Itm
    open Ay
    open Opt
    open StrOp
    /// return {IdxLin[]} from {ly} so that no need to process lines will be skipped
    let wh cond ly = ayAddIdx ly |> Array.choose (fun(i,lin)->if(cond lin) then Some({linIdx=i;lin=lin}) else None)
    let private fndMsg i r = r|>ayWh(fun r->r.linIdx = i)|>ayMap(fun r->r.msg) 
    let private addMsg r i lin = lin,fndMsg i r
    let private pack rLin = 
        let lin,msg = rLin
        let len = len lin
        syTab lin len msg
    let private unpack rLin = if rLin|>snd|>Array.isEmpty then [|rLin|>fst|>rtrim|] else pack rLin
    let private put r src = src |> syAlignL |> ayMapi(addMsg r) |> ayMap unpack |> Array.concat
    let srcPutRslt r src = if (Array.isEmpty r) then src else put r src
        
    /// use {chkLinF} to check each {src[].lin} and return the {Rslt[]}, 
    /// where Rslt={lin;linIdx}.
    /// Rslt.linIdx coming from Src.linIdx 
    /// and Rslt.msg coming given chkLinF().Value
    let chkSrcLin(chkLinF:string->string option)(src:IdxLin[]):Rslt[] =
        let chk {lin=lin} = chkLinF lin 
        let mkRslt'({linIdx=linIdx;lin=lin},msg':string option):Rslt option= 
            if(msg'.IsSome) then Some({msg=msg'.Value; linIdx=linIdx}) else None
        src |> ayMap chk |> ayZip src |> ayMap mkRslt' |> opyWhSomVal
    let chkSrcBlk(chkBlk:string[]->Rslt[])(src:IdxLin[]):Rslt[] =
        [||]
    let chkDupTermOne(src:IdxLin[]): Rslt[] =
        let chk src:Rslt[] = [||]
        chkSrcBlk chk src

(*
        let term1Ay = ly |> lyWh |> ayMap fstTerm
        let dupLis = term1Ay |> ayWhDup |> Array.toList
        term1Ay |> ayMap (fun i -> if (hasAnySs dupLis i) then Some(quote "dup(*)" i) else None)
*)
module x =
    let xx = """
Function EvlSw(SwLy$(), Prm As Dictionary) As Dictionary
Dim O As New Dictionary
    O.RemoveAll
    Dim SomLinEvaluated As Boolean
        SomLinEvaluated = True
    While SomLinEvaluated
        SomLinEvaluated = False
        Dim L
        For Each L In AyRmvEmpty(SwLy)
            With ESwLin(L, Prm, O)
                If .Som Then
                    SomLinEvaluated = True
                    O.Add .Nm, .Bool         '<==
                End If
            End With
        Next
    Wend
If O.Count <> Sz(AyRmvEmpty(SwLy)) Then Stop
Set EvlSw = O
End Function

Function ESwAND(TermAy$(), Prm As Dictionary, Sw As Dictionary) As BoolOpt
Dim BoolAy() As Boolean
    Dim I
    For Each I In TermAy
        With ESwTerm(I, Prm, Sw)
            If Not .Som Then Exit Function
            Push BoolAy, CBool(.V)
        End With
    Next
ESwAND = SomBool(BoolAy_And(BoolAy))
End Function

Function ESwEQ(TermAy$(), Prm As Dictionary, Sw As Dictionary) As BoolOpt
If Sz(TermAy) <> 2 Then Stop
With ESwT1T2(TermAy(0), TermAy(1), Prm, Sw)
    If Not .Som Then Exit Function
    With .S1S2
        ESwEQ = SomBool(.S1 = .S2)
    End With
End With
End Function

Function ESwLin(SwLin, Prm As Dictionary, Sw As Dictionary) As NmBoolOpt
'ESwLin = Evaluate-Line-Switch
'OpLin is up to [Op] not yet parse
Dim L$
    L = SwLin
Dim Nm$
    Nm = ParseTerm(L)

If Sw.Exists(Nm) Then Exit Function

Dim O As BoolOpt
    Dim Op$, TermAy$()
        Op = ParseTerm(L)
        TermAy = SplitLvs(L)
    Select Case Op
    Case "OR":  O = ESwOR(TermAy, Prm, Sw)
    Case "AND": O = ESwAND(TermAy, Prm, Sw)
    Case "NE":  O = ESwNE(TermAy, Prm, Sw)
    Case "EQ":  O = ESwEQ(TermAy, Prm, Sw)
    Case Else: Stop
    End Select
If Not O.Som Then Exit Function
ESwLin.Som = True
ESwLin.Nm = Nm
ESwLin.Bool = O.Bool
End Function

Function ESwNE(TermAy$(), Prm As Dictionary, Sw As Dictionary) As BoolOpt
If Sz(TermAy) <> 2 Then Stop
With ESwT1T2(TermAy(0), TermAy(1), Prm, Sw)
    If Not .Som Then Exit Function
    With .S1S2
        ESwNE = SomBool(.S1 <> .S2)
    End With
End With
End Function

Function ESwOR(TermAy$(), Prm As Dictionary, Sw As Dictionary) As BoolOpt
Dim BoolAy() As Boolean
    Dim I
    For Each I In TermAy
        With ESwTerm(I, Prm, Sw)
            If Not .Som Then Exit Function
            Push BoolAy, CBool(.V)
        End With
    Next
ESwOR = SomBool(BoolAy_Or(BoolAy))
End Function

Function ESwT1T2(T1$, T2$, Prm As Dictionary, Sw As Dictionary) As S1S2Opt
Dim S1$, S2$
With ESwTerm(T1, Prm, Sw)
    If Not .Som Then Exit Function
    S1 = .V
End With
With ESwTerm(T2, Prm, Sw)
    If Not .Som Then Exit Function
    S2 = .V
End With
ESwT1T2 = SomS1S2(S1, S2)
End Function

Function ESwTerm(T, Prm As Dictionary, Sw As Dictionary) As VarOpt
'T is for switch-term, which is begin with % or ? or it is *Blank.  % is for parameter & ? is for switch
'  If %, it will evaluated to str
'        if not exist in {Prm}, stop
'  If ?, it will evaluated to bool
'        if not exist in {Switch}, return None
'  Otherwise, just return SomVar(T)
Dim O As VarOpt
    Select Case FstChr(T)
    Case "?"
        If Not Sw.Exists(T) Then Exit Function
        O = SomVar(Sw(T))
    Case "%"
        If Not Prm.Exists(T) Then Stop
        O = SomVar(Prm(T))
    Case "*"
        If T <> "*Blank" Then Stop
        O = SomVar("")
    Case Else
        O = SomVar(T)
    End Select
ESwTerm = O
End Function
"""
    let dicValOpt (dic:Map<string,'a>) key = if(dic.ContainsKey key) then Some(dic.Item key) else None
module Blk =
    open Ay
    open Jn
    open Dic
    open Rmk
    open PfxSfx
    open Predict
    type BlkTy = PrmBlk|SwBlk|SqBlk|RmkBlk|ErBlk
    type Blk = BlkTy * string[]
    type Sw = Map<string,bool>
    type LinDic = Map<string,string>
    let empSw:Sw = Map.empty<string,bool>
    let empLinDic:LinDic = Map.empty<string,string>
    let blkAyWhSq blkAy = [||]
    let blkAyWhPrmLy blkAy = [||]
    let blk (ty:BlkTy) ly:Blk = ty,ly
    let blkTyEq blkTy= fun(blk:Blk) -> fst blk= blkTy 
    let blkAyFind ty = ayFind (blkTyEq ty)
    let blkLy(blk:Blk) = snd blk
    let blkAyDic blkTy = blkAyFind PrmBlk >> blkLy >> sdicByLy 
    let private isSel    = pOr(hasPfx "sel ")   (hasPfx "?sel ")
    let private isSelDis = pOr(hasPfx "selDis ")(hasPfx "?selDis ")
    let private isUpd    = pOr(hasPfx "upd ")   (hasPfx "?upd ")
    let private isSqLin  = pAll [isSel;isSelDis;isUpd]
    let private isPrmLy  = syRmvRmkLin >> ayAll (hasPfx "%")
    let private isSwLy   = ayAll (hasPfx "?")
    let private isSqLy  ly = if(Array.length ly=0) then false else isSqLin(ly.[0])
module VdtPrm =
    open Blk
    //open Ay
    //open Itm
    //open Quote
    //open Jn
    //open StrHas
    //open StrBrk
    open Predict
    //open Dic
    //open Opt
    //open Zip
    //open Term
    //open Ay
    //open AyWh
    open Rmk
    //open Builder
    //open PfxSfx
    //open StrOp
    open IdxLin
    let vdtPrmLy (ly:string[]):Rslt[] =
        let l = ly |> IdxLin.wh (pNot isRmkLin)
        let r1 = l |> IdxLin.chkSrcLin prmLinChk|> ayMap prmLinErOpt
        let r2 = l |> IdxLin.chkDupTermOne
        ly|>IdxLin.rsltPutSrc[r1,r2]
    let vdtPrmLy ly = Some ""
    /// vdt if no error in {lines} return None else return Some lines-with-error-message
    let prmLinChk lin = oneOf {
        if(hasPfx "%" lin|>not) then return "must have pfx-(%)"
        if(hasPfx "%?" lin) then 
            if nTerm lin <> 2 then return "for %?, it should have only 2 terms"
            let s = sndTerm lin
            if (s<>"0" && s<>"1") then return "for %?, 2nd term must be 0 or 1"
        }
module VdtSq =
    open Blk
    open Ay
    open Itm
    open Quote
    open Jn
    open StrHas
    open StrBrk
    open Predict
    open Dic
    open Opt
    open Zip
    open Term
    open Ay
    open AyWh
    open Rmk
    open Builder
    open PfxSfx
    open StrOp
    open System
    let sqLyVdt    (ly:string[]) = true,""
module VdtSw =
    open Blk
    open Ay
    open Itm
    open Quote
    open Jn
    open StrHas
    open StrBrk
    open Predict
    open Dic
    open Opt
    open Zip
    open Term
    open Ay
    open AyWh
    open Rmk
    open Builder
    open PfxSfx
    open StrOp
    open System

    let swLinVdt lin = oneOf {
        if (fstChr lin) <> "?" then return "must begin with ?"
        let nTerm = nTerm lin
        if nTerm < 3 then return "must have 3 or more terms"
        let s = sndTerm lin
        if s |> isInLis ["EQ";"NE";"AND";"OR"] |> not then return "2nd term is operator, it must be [NE EQ OR AND]"
        if s |> isInLis ["EQ";"NE"] && (nTerm<>4) then return "when 2nd term is [EQ|NE], it must have 4 terms"
        }
    //--
    let erOptStr(er:string option) = if er.IsSome then " ---(" + er.Value + ")" else ""
    let erStrAy erAy = erAy |> ayMap erOptStr
module Vdt =
    open Blk
    open Ay
    open Itm
    open Quote
    open Jn
    open StrHas
    open StrBrk
    open Predict
    open Dic
    open Opt
    open Zip
    open Term
    open Ay
    open AyWh
    open Rmk
    open Builder
    open PfxSfx
    open StrOp
    open System
    let private normalize      = syRmv2DashRmk >> syRTrim

    let lyChk(strErOpt:string->string option)= 
        ayMap strErOpt >> ayAddIdx >> ayWh(snd >> isSome) >> ayMap (zipF2 optVal)
    let vdtBlks (a:Blks):bool*string = true,""
    let vdtBlk    (b:Blk):bool*string = 
        let ty,ly = b
        match ty with
        | RmkBlk -> false,(jnSyCrLf ly)
        | PrmBlk -> VdtPrm.vdtPrmLy ly
        | SwBlk  -> VdtSw.vdtSwLy   ly
        | SqBlk  -> VdtSql.vdtSqLy  ly
        | ErBlk  -> true, (jnSyCrLf ly)
    
    let blkAyChk (blkAy:Blk[]):(bool*string)[] = blkAy |> ayMap vdtBlk
    let blkAyVdt(blkAy:Blk[]):string option =
        let erLis =  ( blkAy |> ayMap vdtBlk ) |> Array.append (blkAyChk blkAy)
        let isErAy,linesAy = erLis |> Array.unzip
        match ayAny itmSelf isErAy with
        | true -> Some(jnSy "\r\n==" linesAy)
        | _    -> None
module EvlSq =
    let sqLyEvl(prmDic)(swDic)(sqLy:string[]):string = ""
    let evlSqBlk prm sw blk = ""
module EvlSw =
    open Blk
    open StrOp
    open Opt
    open Zip
    open Ay
    open Dic
    open StrBrk
    open AyWh
    open StrSplit
    open Dic
    let evlTerm (prm:LinDic)(sw:Sw) t = 
        let f = fstChr t
        match fstChr t with
        | "?" -> dicValOpt sw  t
        | "%" -> dicValOpt prm t |> optApply System.Boolean.Parse
        | _ -> None
    let evlT1T2 prm sw (t1,t2)= zipOpt(evlTerm prm sw t1)(evlTerm prm sw t2)
    let andFun (a:bool option[]):bool option = if(opyAnyNone a) then None else Some ( a |> ayAll optVal )
    let orFun  (a:bool option[]):bool option = if(opyAnyNone a) then None else Some ( a |> ayAny optVal )
    let f (g:'a*'a->'b)(opt:('a*'a) option):'b option= if opt.IsSome then Some(opt.Value |> g) else None
    let evl_AND_OR andOrFun prm sw termAy = termAy |> ayMap (evlTerm prm sw) |> andOrFun
    let evl_EQ_NE  eqFun    prm sw termAy = termAy |> ayZipFst2Ele  |> evlT1T2 prm sw |> f eqFun
    let evlAND = evl_AND_OR andFun
    let evlOR  = evl_AND_OR orFun
    let evlEQ  = evl_EQ_NE zipEq
    let evlNE  = evl_EQ_NE zipNe
    let evlRst (prm:LinDic)(sw:Sw) rst =
        let op,term = brk1Spc rst
        let termAy = splitLvs term
        match op with
        | "OR"  -> termAy |> evlOR  prm sw 
        | "AND" -> termAy |> evlAND prm sw 
        | "NE"  -> termAy |> evlNE  prm sw
        | "EQ"  -> termAy |> evlEQ  prm sw

    let swAddDta(ky)(b')(sw) = 
        let f (o:Sw)(k,b':bool option) = if(b'.IsSome) then dicAddKV(k,(b'.Value)) o else o
        b' 
        |> ayZip ky 
        |> Array.fold f sw

    let swLyEvl swLy (prm:LinDic)(sw:Sw):Sw = 
        let e1 ly (sw:Sw) :string[]*Sw*bool =
            let ky,rst = swLy |> ayMap brk1Spc |> Array.unzip
            let b' = rst |> ayMap (evlRst prm sw)
            let oLy = ayWhByOnyForNone b' ly
            let oIsEvled = b'.Length > 0
            let oSw = swAddDta ky b' sw
            oLy,oSw,oIsEvled
        let rec e2 ly (sw:Sw):Sw = 
            let ly,sw,isEvled = e1 ly sw
            if isEvled then if ly.Length>0 then failwith "oLy still have data"
            if isEvled then sw else e2 ly sw
        e2 swLy empSw    
module Evl =
    open Blk
    open EvlSq
    open EvlSw
    open Dic
    open Jn
    let evlBlkAy (blkAy:Blk[]):string = 
        let prmDic = blkAy |> blkAyWhPrmLy |> sdicByLy 
        let swDic = blkAyDic SwBlk blkAy
        let evlSq = evlSqBlk prmDic swDic
        blkAy |> blkAyWhSq |> ayMap evlSq |> jnSyDblCrLf
[<AutoOpen>]
module Main =
    open FtRead
    open Wrt
    open Blk
    type Rslt = { edt': string option; sq' : string option }
    let tpFtToSqFt tpFt = ""
    let sqTpEvl(sqTp:string):Rslt = 
        let blks = blksBrk sqTp
        let isEr, edt = vdtBlks blks
        let oEdt' = if edt = sqTp then None else Some edt
        let oSq' = if isEr then None else Some (evlBlks blks)
        { edt' = oEdt'; sq' = oSq'}
    let rsltProcess(r:Rslt) tpFt = 
        let { edt'=edt'; sq'=sq' } = r
        wrtStrOpt tpFt sq'
        wrtStrOpt (tpFtToSqFt tpFt) edt'
        r
    let tpFtEvl ft = ftStr ft |> sqTpEvl |> rsltProcess
    let main = tpFtEvl