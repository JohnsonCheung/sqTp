namespace Lib.SqTp.Tst
open Lib.SqTp
open Lib.Core
[<AutoOpen>]
module a =
    let aSqTp = """
%?BrkCrd 1
%?BrkSto 1
%?BrkDiv 1
%?BrkMbr 1
%LisCrd 1 2
%LisSto 1 2 33
%LisDiv 02 02
%ECrd 1 lks fkdf
%ECrd 2 ksdfj ksj dk 
%ECrd 3 ksldf
%DteFm 20170101
%DteTo 20180101
%SumLvl Y
-------------------------------------------------------------
?Mbr OR %?BrkMbr
?Crd OR %?BrkCrd
?Div OR %?BrkDiv
?Sto OR %?BrkSto
?LvlY  EQ %SumLvl Y
?LvlM  EQ %SumLvl M
?LvlW  EQ %SumLvl W
?LvlD  EQ %SumLvl D
?Y     OR ?LvlD ?LvlW ?LvlM ?LvlY
?M     OR ?LvlD ?LvlW ?LvlM
?W     OR ?LvlD ?LvlW
?Wd    OR ?W
?Wd1   OR ?W
?D     OR ?LvlD
?Dte   OR ?LvD
?sel#Div
?sel#Sto
?sel#Crd
?sel#TxMbrLis
?sel#TxMbrDta
?sel#MbrWs
?upd#Tx
-------------------------------------------------------------
sel       ?Mbr ?Crd ?Div ?Sto ?Y ?M ?W ?Wd ?Wd1 ?D ?Dte TxAmt TxQty TxCnt
fm        SalesHistory
into      #Tx
whBetStr  %DteFm %DteTo
?andIn    %ECrd %LisCrd
?andIn    Div %LisDiv
?andIn    Sto %LisSto
$Mbr
$Crd
$Div
$Sto
$Y
$M
$W
$Wd
$Wd1
$D
$Dte
$TxAmt
$TxCnt
-------------------------------------------------------------
?upd      #Tx
set       ?Wd
$Wd
-------------------------------------------------------------
?seldis   ?Mbr
fm        #Tx
into      #TxMbrList
gp        ?Mbr
-------------------------------------------------------------
?sel      ?Mbr Adr Nm CNm Sex Reg Dist 
into      #MbrDta
fm        SHMMember
jn        #TxMbrList a on a.Mbr = x.SHMMCode
$Adr
$Sex
$Mbr
$Sex
$Reg
$Dist
$Nm
$CNm
-------------------------------------------------------------
?seldis   ?Mbr
fm        #Tx
into      #Div
gp        ?Mbr
-------------------------------------------------------------
?sel      ?Div
into      #Div
fm        Division
whIn      Div LisDiv
$Div
$DivNm
$DivCNm
-------------------------------------------------------------
?sel      Crd CrdNm
into      #Crd
fm        SelTy()
?whIn     Crd LisCrd
$Crd      %ECrd
$CrdNm
-------------------------------------------------------------
?sel      Sto StoCNm StoNm
into      #Sto
fm        Location
?whIn     Sto LisSto
"""
module Main =
    open Lib
    open Lib.ChkLy1
    let exp = Some ""
    let chkLinF1 lin = Some "error"
    let chkBkF1(llis:string list) = llis |> lisMap (fun lin -> Some "er")
    let chkLinF = [chkLinF1]
    let chkBkF  = [chkBkF1]
    let ly = [||]
    let tst'vdt cas exp ly chkLinF chkBkF =
        let a = new ChkLy1.ChkLy(ly,chkLinF,chkBkF)
        let act = a.tpOpt
        assert (exp = act)
    [<EntryPoint>]
    let main args =
        tst'vdt 0 exp ly chkLinF chkBkF
        0