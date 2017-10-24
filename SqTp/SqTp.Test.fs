namespace Tst.SqTp
open Microsoft.VisualStudio.TestTools.UnitTesting
open Lib.SqTp
open Lib.Core
[<AutoOpen>]
module a =
    let aSqTp = """
-- Rmk: -- is remark
-- %XX: is prmDicLin
-- %?XX: is switchPrm, it value must be 0 or 1
-- ?XX: is switch line
-- SwitchLin: is ?XXX [OR|AND|EQ|NE] [SwPrm_OR_AND|SwPrm_EQ_NE]
-- SwPrm_OR_AND: SwTerm ..
-- SwPrm_EQ_NE:  SwEQ_NE_T1 SwEQ_NE_T2
-- SwEQ_NE_T1: 
-- SwEQ_NE_T2: 
-- SwTerm:     ?XX|%?XX     -- if %?XX, its value only 1 or 0 is allowed
-- Only one gp of %XX:
-- Only one gp of ?XX:
-- All other gp is sql-statement or sql-statements
-- sql-statments: Drp xxx xxx
-- sql-statment: [sel|selDis|upd|into|fm|whBetStr|whBetNbr|whInStrLis|whInNbrLis|andInNbrLis|andInStrLis|gp|jn|left|expr]
-- optional: Whxxx and Andxxx can have ?-pfx becomes: ?Whxxx and ?Andxxx.  The line will become empty
==============================================
Drp Tx TxMbr MbrDta Div Sto Crd Cnt Oup MbrWs
=============================================
%?BrkMbr 0
%?BrkSto 0
%?BrkCrd 0
%?BrkDiv 0
%SumLvl  Y
%?MbrEmail
%?MbrNm
%?MbrPhone
%?MbrAdr
%%DteFm 20170101
%%DteTo 20170131
%LisDiv 1 2
%LisSto
%LisCrd
%CrdExpr ...
============================================
?LvlY    EQ %SumLvl Y
?LvlM    EQ %SumLvl M
?LvlW    EQ %SumLvl W
?LvlD    EQ %SumLvl D
?Y       OR ?LvlD ?LvlW ?LvlM ?LvlY
?M       OR ?LvlD ?LvlW ?LvlM
?W       OR ?LvlD ?LvlW
?D       OR ?LvlD
?Dte     OR ?LvlD
?Mbr     OR %BrkMbr
?MbrCnt  OR %BrkMbr
?Div     OR %BrkDiv
?Sto     OR %?BrkSto
?Crd     OR %?BrkCrd
?sel#Div NE %LisDiv *blank
?sel#Sto NE %LisSto *blank
?sel#Crd NE %LisCrd *blank
============================================= #Tx
sel  ?Crd ?Mbr ?Div ?Sto ?Y ?M ?W ?WD ?D ?Dte Amt Qty Cnt 
into #Tx
fm   SalesHistory
whBetStr     %%DteFm %%DteTo
?andInStrLis Div %LisDiv
?andInStrLis Sto %LisSto
?andInNbrLis Crd %LisCrd
?gp ?Crd ?Mbr ?Div ?Sto ?Crd ?Y ?M ?W ?WD ?D ?Dte
$Crd %CrdExpr
$Mbr JCMCode
$Sto
$Y
$M
$W
$WD
$D
$Dte
Amt Sum(SHAmount)
$Qty Sum(SHQty)
$Cnt Count(SHInvoice+SHSDate+SHRef)
============================================= #TxMbr
selDis  Mbr
fm      #Tx
into    #TxMbr
============================================= #MbrDta
sel   Mbr Age Sex Sts Dist Area
fm    #TxMbr x
jn    JCMMember a on x.Mbr = a.JCMMCode
into  #MbrDta
$Mbr  x.Mbr
$Age  DATEDIFF(YEAR,CONVERT(DATETIME ,x.JCMDOB,112),GETDATE())
$Sex  a.JCMSex
$Sts  a.JCMStatus
$Dist a.JCMDist
$Area a.JCMArea
==-=========================================== #Div
?sel Div DivNm DivSeq DivSts
fm   Division
into #Div
?whInStrLis Div %LisDiv
$Div Dept + Division
$DivNm LongDies
$DivSeq Seq
$DivSts Status
============================================ #Sto
?sel Sto StoNm StoCNm
fm   Location
into #Sto
?whInStrLis Loc %LisLoc
$Sto
$StoNm
$StoCNm
============================================= #Crd
?sel        Crd CrdNm
fm          Location
into        #Crd
?whInNbrLis Crd %LisCrd
$Crd
$CrdNm
============================================= #Oup
sel  ?Crd ?CrdNm ?Mbr ?Age ?Sex ?Sts ?Dist ?Area ?Div ?DivNm ?Sto ?StoNm ?StoCNm ?Y ?M ?W ?WD ?D ?Dte Amt Qty Cnt
into #Oup
fm   #Tx x
left #Crd a on x.Crd = a.Crd
left #Div b on x.Div = b.Div
left #Sto c on x.Sto = c.Sto
left #MbrDta d on x.Mbr = d.Mbr
wh   JCMCode in (Select Mbr From #TxMbr)
============================================ #Cnt
sel ?MbrCnt RecCnt TxCnt Qty Amt
into #Cnt
fm  #Tx
$MbrCnt Count(Distinct Mbr)
$RecCnt Count(*)
$TxCnt  Sum(TxCnt)
$Qty    Sum(Qty)
$Amt    Sum(Amt)
============================================
"""

[<TestClass>]
type VdtPrm() =
    [<TestMethod>]
    member x.chkPrmLin() = 
        let tst exp lin = 
            let act = PrmLin.chk lin
            Assert.AreEqual(exp,act)
        tst None                       
            "%ldsf sldf df"
        
        tst None                       
            "%?ldsf 1"
        
        tst None                       
            "%?ldsf 0"
        
        tst (Some "must have pfx-(%)") 
            "aldsf sldf df"
        
        tst (Some "for %?, it should have only 2 terms") 
            "%?aldsf sldf df"

        tst (Some "for %?, 2nd term must be 0 or 1") 
            "%?aldsf df"
    (*
        let tstThow ly = shouldThow(fun()->prmLyVdt ly)
        let tst(ly,exp) =
            let act = prmLyVdt ly
            let r = act=exp
            if not r then
                printfn "tstDta\n%A" ly
                printfn "act\n%A" act
                printfn "exp\n%A" exp
            Assert.IsTrue r
        let d0 =(   [|  "%ab 1234"
                        "%ab 1234 12 3"
                        "%xyz";"%dd"|],
                    (true, syJnCrLf [|  "%ab 1234       ---(dup(%ab))"
                                        "%ab 1234 12 3  ---(dup(%ab))" 
                                        "%xyz          " 
                                        "%dd           " |]))
        [d0] |> List.iter tst
        *)
        ()

[<TestClass>] 
type tst() = 
    [<TestMethod>] 
    member x.lyDupTermOneChk() =
        let s = Some "dup(a)"
        let n = None
        let d0 = (0,[|s;s;n;n|],[|"a klsdfj lsdfk";"a slkdfj";"dkf";"lksdfjdf"|])
        let d1 = (1,[|Some("dup(aaa)");n;Some("dup(aaa)")|], 
                    [|
                        "aaa sdklfsdklf"
                        "aa sdklfjsdfkl"
                        "aaa    sdklfdfk"
                    |])
        let d2 = (2,[|Some("dup()");Some("dup()");Some("dup()")|],[|"";"";""|])
        let tstr(case,exp,ly) =
            let run() = () // lyDupTermOneChk ly
            let act = run()
            let r = act = exp
            if not r then 
                prtLisNL["TstDta - ly\n";ly]
                prtLisNL["Act\n";act]
                prtLisNL["Exp\n";exp]
            Assert.IsTrue r
        //[d0;d1;d2] |> List.iter tstr
        ()

[<TestClass>] 
type TpBk() = 
    [<TestMethod>] 
    member x.BkTyByLy() =
        ()

 [<TestClass>] 
type Main() = 
    [<TestMethod>] 
    member x.sqTp'evl() =
        let act = sqTp'evl aSqTp
        ()

module main =
    open Prt
    [<EntryPointAttribute>]
    let main args =
        sqTp'evl aSqTp |> toStr |> prtS
        0
